open Stdppx
open Ppxlib
open Ppxlib_jane

module String = struct
  include String

  let is_substring t ~substring =
    let open Int in
    let len_t = String.length t in
    let len_sub = String.length substring in
    if len_sub = 0
    then true
    else if len_sub > len_t
    then false
    else (
      let rec matches_at pos sub_pos =
        if sub_pos = len_sub
        then true
        else if Char.equal (get t pos) (get substring sub_pos)
        then matches_at (pos + 1) (sub_pos + 1)
        else false
      in
      let rec is_substring_at pos =
        if pos + len_sub > len_t
        then false
        else if matches_at pos 0
        then true
        else is_substring_at (pos + 1)
      in
      is_substring_at 0)
  ;;
end

let annotated_ignores = ref true
let check_comments = ref false
let compat_32 = ref false
let allow_toplevel_expression = ref false
let check_underscored_literal = ref true
let cold_instead_of_inline_never = ref false
let require_dated_deprecation = ref true
let allow_letop_uses = ref false
let allow_redundant_modalities = ref false
let raise_on_lint_error = ref false
let errorf ~loc fmt = Location.raise_errorf ~loc (Stdlib.( ^^ ) "Jane Street style: " fmt)

module Ignored_reason = struct
  type t =
    | Argument_to_ignore
    | Underscore_pattern

  let fail ~loc _t = errorf ~loc "Ignored expression must come with a type annotation"
end

module Invalid_deprecated = struct
  type t =
    | Not_a_string
    | Missing_date
    | Invalid_month

  let fail ~loc = function
    | Not_a_string -> errorf ~loc "Invalid [@@deprecated payload], must be a string"
    | Missing_date ->
      errorf
        ~loc
        "deprecated message must start with the date in this format: [since YYYY-MM]"
    | Invalid_month -> errorf ~loc "invalid month in deprecation date"
  ;;
end

module Invalid_constant = struct
  type t = string * string

  let fail ~loc ((s, typ) : t) =
    Location.raise_errorf
      ~loc
      "Integer literal %s exceeds the range of representable integers of type %s on \
       32bit architectures"
      s
      typ
  ;;
end

module Suspicious_literal = struct
  type t = string * string

  let fail ~loc ((s, typ) : t) =
    Location.raise_errorf
      ~loc
      "The %s literal %s contains underscores at suspicious positions"
      typ
      s
  ;;
end

module Invalid_ocamlformat_attribute = struct
  type t = string

  let fail ~loc (reason : t) =
    Location.raise_errorf ~loc "Invalid ocamlformat attribute. %s" reason
  ;;

  let kind { attr_name = name; attr_payload = payload; attr_loc = _ } =
    match name.txt, payload with
    | "ocamlformat", PStr ([%str "disable"] | [%str "enable"]) -> `Enable_disable
    | "ocamlformat", _ -> `Other
    | _ -> `Not_ocamlformat
  ;;
end

type error =
  | Invalid_deprecated of Invalid_deprecated.t
  | Missing_type_annotation of Ignored_reason.t
  | Invalid_constant of Invalid_constant.t
  | Suspicious_literal of Suspicious_literal.t
  | Invalid_ocamlformat_attribute of Invalid_ocamlformat_attribute.t
  | Docstring_on_open
  | Use_of_letop of { op_name : string }

let fail ~loc = function
  | Invalid_deprecated e -> Invalid_deprecated.fail e ~loc
  | Missing_type_annotation e -> Ignored_reason.fail e ~loc
  | Invalid_constant e -> Invalid_constant.fail e ~loc
  | Suspicious_literal e -> Suspicious_literal.fail e ~loc
  | Invalid_ocamlformat_attribute e -> Invalid_ocamlformat_attribute.fail e ~loc
  | Docstring_on_open ->
    errorf
      ~loc
      "A documentation comment is attached to this [open] which will be dropped by odoc."
  | Use_of_letop { op_name } ->
    errorf
      ~loc
      "This use of ( %s ) is forbidden.@.ppx_let is currently more featureful, please \
       use that instead to keep a consistent style"
      op_name
;;

let local_ocamlformat_config_disallowed =
  Invalid_ocamlformat_attribute "Ocamlformat cannot be configured locally"
;;

let check_deprecated_string ~f ~loc s =
  match Stdlib.Scanf.sscanf s "[since %u-%u]" (fun y m -> y, m) with
  | exception _ -> f ~loc (Invalid_deprecated Missing_date)
  | _year, month ->
    if month = 0 || month > 12 then f ~loc (Invalid_deprecated Invalid_month)
;;

let ignored_expr_must_be_annotated ignored_reason (expr : Parsetree.expression) ~f =
  match
    Ppxlib_jane.Shim.Expression_desc.of_parsetree expr.pexp_desc ~loc:expr.pexp_loc
  with
  (* explicitely annotated -> good *)
  | Pexp_constraint _
  | Pexp_coerce _
  (* no need to warn people trying to silence other warnings *)
  | Pexp_construct _
  | Pexp_function _
  | Pexp_ident _ -> ()
  | _ -> f ~loc:expr.pexp_loc (Missing_type_annotation ignored_reason)
;;

module Constant = struct
  let max_int_31 = Int64.sub (Int64.shift_left 1L 30) 1L
  let min_int_31 = Int64.neg (Int64.shift_left 1L 30)

  let check_compat_32 ~loc c =
    if !compat_32
    then (
      match c with
      | Pconst_integer (s, Some 'n') ->
        (try ignore (Int32.of_string s) with
         | _ -> fail ~loc (Invalid_constant (s, "nativeint")))
      | Pconst_integer (s, None) ->
        (try
           let i = Int64.of_string s in
           if Int64.(compare i min_int_31 < 0 || compare i max_int_31 > 0)
           then failwith "out of bound"
         with
         | _ -> fail ~loc (Invalid_constant (s, "int")))
      | _ -> ())
  ;;

  let check_underscored ~loc c =
    if !check_underscored_literal
    then (
      let check_segment ~name ~start ~stop ~kind s =
        (* start and stop are inclusive *)
        let incr = if start < stop then 1 else -1 in
        let modulo =
          match kind with
          | `Decimal -> 3
          | `Hexadecimal | `Binary | `Octal -> 2
        in
        let rec loop string_pos ~number_offset =
          let number_offset =
            match s.[string_pos] with
            | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> number_offset + 1
            | '_' ->
              if number_offset mod modulo <> 0
              then fail ~loc (Suspicious_literal (s, name))
              else number_offset
            | _ -> assert false
          in
          if stop <> string_pos then loop (string_pos + incr) ~number_offset
        in
        loop start ~number_offset:0
      in
      let parse_prefix s =
        let i =
          match s.[0] with
          | '-' | '+' -> 1
          | _ -> 0
        in
        if String.length s >= i + 2
        then (
          match s.[i], s.[i + 1] with
          | '0', ('x' | 'X') -> `Hexadecimal, i + 2
          | '0', ('b' | 'B') -> `Binary, i + 2
          | '0', ('o' | 'O') -> `Octal, i + 2
          | _ -> `Decimal, i)
        else `Decimal, i
      in
      let should_check =
        let has_double_underscores s = String.is_substring ~substring:"__" s in
        let has_underscore s = String.exists ~f:(fun c -> Char.( = ) c '_') s in
        fun s -> has_underscore s && not (has_double_underscores s)
      in
      match Ppxlib_jane.Shim.Constant.of_parsetree c with
      | Pconst_integer (s, _) | Pconst_unboxed_integer (s, _) ->
        if should_check s
        then (
          let kind, lower = parse_prefix s in
          check_segment ~name:"integer" ~start:(String.length s - 1) ~stop:lower ~kind s)
      | Pconst_float (s, _) | Pconst_unboxed_float (s, _) ->
        if should_check s
        then (
          let kind, lower = parse_prefix s in
          let upper =
            (* only validate the mantissa *)
            let power_split =
              match kind with
              | `Decimal ->
                (match String.index_opt s 'e', String.index_opt s 'E' with
                 | None, None -> None
                 | None, (Some _ as some) | (Some _ as some), None -> some
                 | Some a, Some b -> Some (min a b))
              | `Hexadecimal ->
                (match String.index_opt s 'p', String.index_opt s 'P' with
                 | None, None -> None
                 | None, (Some _ as some) | (Some _ as some), None -> some
                 | Some a, Some b -> Some (min a b))
              | `Binary | `Octal -> assert false
            in
            match power_split with
            | None -> String.length s - 1
            | Some i -> i - 1
          in
          let name = "float" in
          match String.index_from_opt s lower '.' with
          | None -> check_segment ~name ~start:upper ~stop:lower ~kind s
          | Some i ->
            if lower <> i then check_segment ~name ~start:(i - 1) ~stop:lower ~kind s;
            if upper <> i then check_segment ~name ~start:(i + 1) ~stop:upper ~kind s)
      | Pconst_char _ | Pconst_untagged_char _ | Pconst_string _ -> ())
  ;;

  let check ~loc c =
    check_compat_32 ~loc c;
    check_underscored ~loc c
  ;;
end

let is_deprecated = function
  | "ocaml.deprecated" | "deprecated" -> true
  | _ -> false
;;

let is_inline = function
  | "ocaml.inline" | "inline" -> true
  | _ -> false
;;

let check_deprecated attr =
  if is_deprecated attr.attr_name.txt
  then
    errorf
      ~loc:(loc_of_attribute attr)
      "Invalid deprecated attribute, it will be ignored by the compiler"
;;

let is_mlt_or_mdx fname =
  String.is_suffix fname ~suffix:".mlt"
  || String.is_suffix fname ~suffix:".mdx"
  || String.equal "//toplevel//" fname
;;

let iter_style_errors ~f =
  object (self)
    inherit Ast_traverse.iter as super

    method! attribute ({ attr_name = name; attr_payload = payload; attr_loc = _ } as attr)
        =
      let loc = loc_of_attribute attr in
      if !require_dated_deprecation && is_deprecated name.txt
      then (
        match
          Ast_pattern.(parse (single_expr_payload (estring __'))) loc payload (fun s -> s)
        with
        | exception _ -> f ~loc (Invalid_deprecated Not_a_string)
        | { Location.loc; txt = s } -> check_deprecated_string ~f ~loc s);
      match Invalid_ocamlformat_attribute.kind attr with
      | `Enable_disable ->
        f
          ~loc
          (Invalid_ocamlformat_attribute
             "Ocamlformat can only be disabled at toplevel\n\
              (e.g [@@@ocamlformat \"disable\"])")
      | `Other -> f ~loc local_ocamlformat_config_disallowed
      | `Not_ocamlformat -> ()

    method! payload p =
      match p with
      | PStr l ->
        (* toplevel expressions in payload are fine. *)
        List.iter l ~f:(fun item ->
          self#check_structure_item item ~allow_toplevel_expression:true)
      | _ -> super#payload p

    method! open_description od =
      if !check_comments
      then (
        let has_doc_comments =
          List.exists od.popen_attributes ~f:(fun { attr_name; _ } ->
            match attr_name.txt with
            | "ocaml.doc" | "doc" -> true
            | _ -> false)
        in
        if has_doc_comments then f ~loc:od.popen_loc Docstring_on_open);
      super#open_description od

    method! value_binding vb =
      if !annotated_ignores
      then (
        let loc = vb.Parsetree.pvb_loc in
        match Ast_pattern.(parse ppat_any) loc vb.Parsetree.pvb_pat () with
        | exception _ -> ()
        | () -> ignored_expr_must_be_annotated Underscore_pattern ~f vb.Parsetree.pvb_expr);
      super#value_binding vb

    method! expression e =
      (match e with
       | { pexp_desc = Pexp_constant c; pexp_loc; _ } -> Constant.check ~loc:pexp_loc c
       | [%expr ignore [%e? ignored]] when !annotated_ignores ->
         ignored_expr_must_be_annotated Argument_to_ignore ~f ignored
       | { pexp_desc = Pexp_letop { let_; _ }; _ } when not !allow_letop_uses ->
         fail ~loc:let_.pbop_op.loc (Use_of_letop { op_name = let_.pbop_op.txt })
       | _ -> ());
      super#expression e

    method! pattern e =
      (match e with
       | { ppat_desc = Ppat_constant c; ppat_loc; _ } -> Constant.check ~loc:ppat_loc c
       | _ -> ());
      super#pattern e

    method! core_type t =
      List.iter t.ptyp_attributes ~f:check_deprecated;
      super#core_type t

    method private check_structure_item t ~allow_toplevel_expression =
      match t.pstr_desc with
      | Pstr_eval (_, _)
        when (not allow_toplevel_expression)
             && not (is_mlt_or_mdx t.pstr_loc.Location.loc_start.Lexing.pos_fname) ->
        errorf ~loc:t.pstr_loc "Toplevel expression are not allowed here."
      | Pstr_attribute a ->
        (match Invalid_ocamlformat_attribute.kind a with
         | `Enable_disable -> ()
         | `Other -> f ~loc:t.pstr_loc local_ocamlformat_config_disallowed
         | `Not_ocamlformat -> super#structure_item t)
      | _ -> super#structure_item t

    method! structure_item t =
      self#check_structure_item t ~allow_toplevel_expression:!allow_toplevel_expression

    method! signature_item t =
      match t.psig_desc with
      | Psig_attribute a ->
        (match Invalid_ocamlformat_attribute.kind a with
         | `Enable_disable -> ()
         | `Other -> f ~loc:t.psig_loc local_ocamlformat_config_disallowed
         | `Not_ocamlformat -> super#signature_item t)
      | _ -> super#signature_item t
  end
;;

let check = iter_style_errors ~f:fail

module Portability = struct
  type t =
    | Nonportable
    | Unknown
    | Portable

  let apply_modality mode ~modality =
    (* equivalent to [meet mode modality] *)
    match mode, modality with
    | Portable, _ | _, Portable -> Portable
    | Unknown, _ | _, Unknown -> Unknown
    | Nonportable, Nonportable -> Nonportable
  ;;

  let find_modal ~(unwrap_modal : 'a -> string) : 'a Loc.t list -> t Loc.t option =
    fun modals ->
    let portable_modal = ref None in
    let unknown_modal = ref None in
    List.iter modals ~f:(fun modal ->
      let { txt = modal; loc } = Loc.map modal ~f:unwrap_modal in
      match modal with
      | "portable" -> portable_modal := Some { txt = Portable; loc }
      | "nonportable" -> portable_modal := Some { txt = Nonportable; loc }
      | _ -> unknown_modal := Some loc);
    match !portable_modal, !unknown_modal with
    | Some portability, _ -> Some portability
    | _, Some loc -> Some { txt = Unknown; loc }
    | None, None -> None
  ;;

  let find_mode = find_modal ~unwrap_modal:(fun (Ppxlib_jane.Mode mode) -> mode)

  let find_modality =
    find_modal ~unwrap_modal:(fun (Ppxlib_jane.Modality modality) -> modality)
  ;;
end

include struct
  open struct
    let allow_redundant_modalities_attr ctx =
      Ppxlib.Attribute.declare
        "ppx_js_style.allow_redundant_modalities"
        ctx
        Ast_pattern.drop
        ()
    ;;
  end

  let allow_redundant_modalities_pval = allow_redundant_modalities_attr Value_description
  let allow_redundant_modalities_pmd = allow_redundant_modalities_attr Module_declaration
  let allow_redundant_modalities_ptype = allow_redundant_modalities_attr Type_declaration
  let allow_redundant_modalities_pld = allow_redundant_modalities_attr Label_declaration

  let allow_redundant_modalities_pcd =
    allow_redundant_modalities_attr Constructor_declaration
  ;;
end

type sig_portability =
  { sig_mode : Portability.t
  ; default_modality : Portability.t
  }

(* performs a simplified version of template expansion on a signature, removing
   [[%%template: ]] wrappers and replace [[@@@attr]] floating template attributes with a
   single template instance (using [include sig ... end]). *)
let rec trivially_expand_ppx_template psg_items =
  match psg_items with
  | [] -> []
  | hd :: tl ->
    (match hd.psig_desc with
     | Psig_extension (({ txt = "template"; _ }, PSig sig_), _attrs) ->
       let sig_ = Ppxlib_jane.Shim.Signature.of_parsetree sig_ in
       trivially_expand_ppx_template sig_.psg_items @ trivially_expand_ppx_template tl
     | Psig_attribute _
       when Ppx_template_expander.Attributes.Floating.Poly.is_present Signature_item hd ->
       let open Ast_builder.Default in
       let loc = hd.psig_loc in
       [ psig_include
           ~modalities:[]
           ~loc
           (include_infos
              ~kind:Structure
              ~loc
              (pmty_signature ~loc (signature ~loc (trivially_expand_ppx_template tl))))
       ]
     | _ -> hd :: trivially_expand_ppx_template tl)
;;

let check_modality_annotations
  (type err)
  ~(on_error : loc:Location.t -> message:string -> err)
  =
  let ( let* ) res f = Result.bind ~f res in
  let errorf ~loc fmt =
    Printf.ksprintf
      (fun message -> on_error ~loc ~message)
      (Stdlib.( ^^ ) "Modality linting error: " fmt)
  in
  let result_list_all list =
    List.fold_right list ~init:(Ok ()) ~f:(fun res acc ->
      match res, acc with
      | Ok (), Ok () -> Ok ()
      | (Error _ as errs), Ok () | Ok (), (Error _ as errs) -> errs
      | Error errs1, Error errs2 -> Error (errs1 @ errs2))
  in
  let check_modalities modalities ~mut =
    let is_present modality =
      List.exists modalities ~f:(fun { txt = Modality modality'; _ } ->
        String.equal modality modality')
    in
    let is_redundant modality =
      match (mut : mutable_flag), modality with
      | Immutable, ("local" | "stateful" | "read_write" | "unique" | "once") ->
        Error "it is the default modality for its mode-axis."
      | Mutable, ("global" | "stateful" | "read_write" | "aliased" | "many") ->
        Error "it is the default modality on mutable fields for its mode-axis."
      | Immutable, (("unyielding" | "yielding") as yielding) ->
        (match is_present "global", yielding with
         | true, "unyielding" -> Error "the global modality implies unyielding."
         | false, "yielding" -> Error "it is the default modality for its mode-axis."
         | _ -> Ok ())
      | Mutable, (("unyielding" | "yielding") as yielding) ->
        (match is_present "local", yielding with
         | true, "yielding" -> Error "the local modality implies yielding."
         | false, "unyielding" ->
           Error "it is the default modality on mutable fields for its mode-axis."
         | _ -> Ok ())
      | _, "uncontended" ->
        if is_present "read" || is_present "immutable"
        then Ok ()
        else Error "it is the default modality for its mode-axis"
      | _, "shared" ->
        if is_present "read" then Error "the read modality implies shared." else Ok ()
      | _, "contended" ->
        if is_present "immutable"
        then Error "the immutable modality implies contended."
        else Ok ()
      | _, "nonportable" ->
        if is_present "stateless"
        then Ok ()
        else Error "it is the default modality for its mode-axis"
      | _, "portable" ->
        if is_present "stateless"
        then Error "the stateless modality implies portable."
        else Ok ()
      | _ -> Ok ()
    in
    List.map modalities ~f:(fun { txt = Modality modality; loc } ->
      match is_redundant modality with
      | Ok () -> Ok ()
      | Error hint ->
        Error [ errorf ~loc "This modality annotation has no effect; %s" hint ])
    |> result_list_all
  in
  let ok : _ -> (unit, _) result = fun _ -> Ok () in
  object (self)
    inherit [(unit, err list) result] Ast_traverse.lift as super
    method unit = ok
    method bool = ok
    method int = ok
    method int32 = ok
    method int64 = ok
    method nativeint = ok
    method float = ok
    method char = ok
    method string = ok
    method other = ok
    method tuple elts = result_list_all elts
    method record fields = List.map fields ~f:snd |> result_list_all
    method constr _name args = result_list_all args
    method array f elts = Array.to_list elts |> List.map ~f |> result_list_all

    method! type_declaration td =
      if Attribute.has_flag allow_redundant_modalities_ptype td
      then Ok ()
      else super#type_declaration td

    method! jkind_annotation_desc =
      function
      | Pjk_mod (jkind_annotation, modes) ->
        let* () = self#jkind_annotation jkind_annotation in
        let* () =
          List.map modes ~f:(Loc.map ~f:(fun (Mode modal) -> Modality modal))
          |> self#modalities
        in
        Ok ()
      | desc -> super#jkind_annotation_desc desc

    method! modalities modalities = check_modalities modalities ~mut:Immutable

    method! label_declaration ld =
      if Attribute.has_flag allow_redundant_modalities_pld ld
      then Ok ()
      else (
        (* Specially handle [label_declaration]s since they might be mutable. *)
        let modalities, ld = Ppxlib_jane.Shim.Label_declaration.extract_modalities ld in
        let* () = check_modalities modalities ~mut:ld.pld_mutable in
        super#label_declaration ld)

    method! constructor_declaration cd =
      if Attribute.has_flag allow_redundant_modalities_pcd cd
      then Ok ()
      else super#constructor_declaration cd

    method! signature_item sigi =
      (* don't put logic in here; this method is skipped for a lot of signature_items in
         the manual recursion below *)
      super#signature_item sigi

    method! signature original_sig =
      (* Recur over the entire "current" signature (that is, the nodes which a default
         modality on this signature would affect), only calling back into [super] at
         signature "boundaries". *)
      let rec loop : signature -> sig_mode:Portability.t -> (unit, err list) result =
        fun original_sig ~sig_mode ->
        let ({ psg_loc = _; psg_modalities; psg_items } : Ppxlib_jane.Shim.Signature.t) =
          Ppxlib_jane.Shim.Signature.of_parsetree original_sig
        in
        let* sig_portability =
          match sig_mode, Portability.find_modality psg_modalities with
          | Portable, Some { txt = Portable | Nonportable; loc } ->
            Error
              [ errorf
                  ~loc
                  "This signature is forced portable by a containing signature, so the \
                   default modality annotation does nothing."
              ]
          | _, Some { txt = Nonportable; loc } ->
            Error
              [ errorf ~loc "Using [nonportable] as a default modality has no effect." ]
          | sig_mode, default_modality ->
            let default_modality =
              match default_modality with
              | Some { txt = default_modality; _ } -> default_modality
              | None -> Nonportable
            in
            Ok { sig_mode; default_modality }
        in
        let signature_item_mode modalities ~allow_redundant_modalities =
          match Portability.find_modality modalities, sig_portability with
          | Some { txt = _; loc }, { sig_mode = Portable; _ } ->
            Error [ errorf ~loc "This modality annotation is ignored." ]
          | Some { txt = Portable; loc }, { default_modality = Portable; _ }
            when not allow_redundant_modalities ->
            Error [ errorf ~loc "This portable annotation is redundant." ]
          | Some { txt = Nonportable; loc }, { default_modality = Nonportable; _ }
            when not allow_redundant_modalities ->
            Error [ errorf ~loc "This nonportable annotation is redundant." ]
          | modality, { sig_mode; default_modality } ->
            let modality =
              match modality with
              | Some { txt; _ } -> txt
              | None -> default_modality
            in
            Ok (Portability.apply_modality sig_mode ~modality)
        in
        let rec loop_pmty { pmty_desc; _ } ~sig_mode =
          match Ppxlib_jane.Shim.Module_type_desc.of_parsetree pmty_desc with
          | Pmty_signature sig_ -> loop sig_ ~sig_mode
          | Pmty_strengthen (pmty, _) | Pmty_with (pmty, _) -> loop_pmty pmty ~sig_mode
          | Pmty_functor (param, return_type, modes) ->
            let param_res =
              match Ppxlib_jane.Shim.Functor_parameter.of_parsetree param with
              | Unit -> Ok ()
              | Named (_name, pmty, modes) ->
                let sig_mode =
                  match Portability.find_mode modes with
                  | Some { txt = mode; _ } -> mode
                  | None -> Nonportable
                in
                loop_pmty pmty ~sig_mode
            in
            let return_res =
              let sig_mode =
                match Portability.find_mode modes with
                | Some { txt = mode; _ } -> mode
                | None -> Nonportable
              in
              loop_pmty return_type ~sig_mode
            in
            result_list_all [ param_res; return_res ]
          | Pmty_ident _ | Pmty_typeof _ | Pmty_extension _ | Pmty_alias _ -> Ok ()
        in
        let check_pmd pmd =
          let pmd, allow_redundant_modalities =
            match Attribute.consume allow_redundant_modalities_pmd pmd with
            | None -> pmd, false
            | Some (pmd, ()) -> pmd, true
          in
          let pmd = Ppxlib_jane.Shim.Module_declaration.of_parsetree pmd in
          let* sub_module_mode =
            signature_item_mode pmd.pmd_modalities ~allow_redundant_modalities
          in
          loop_pmty pmd.pmd_type ~sig_mode:sub_module_mode
        in
        let check_sigi sigi =
          match Ppxlib_jane.Shim.Signature_item_desc.of_parsetree sigi.psig_desc with
          | Psig_module pmd -> check_pmd pmd
          | Psig_recmodule pmds -> List.map pmds ~f:check_pmd |> result_list_all
          | Psig_include (incl, modalities) ->
            let ({ pincl_kind; pincl_mod; pincl_loc = _; pincl_attributes = _ }
                  : _ Ppxlib_jane.Shim.Include_infos.t)
              =
              Ppxlib_jane.Shim.Include_infos.of_parsetree incl
            in
            (match pincl_kind with
             | Structure ->
               let* include_mode =
                 signature_item_mode modalities ~allow_redundant_modalities:false
               in
               loop_pmty pincl_mod ~sig_mode:include_mode
             | Functor -> Ok ())
          | Psig_value vd ->
            let vd, allow_redundant_modalities =
              match Attribute.consume allow_redundant_modalities_pval vd with
              | None -> vd, false
              | Some (vd, ()) -> vd, true
            in
            let modalities, vd =
              Ppxlib_jane.Shim.Value_description.extract_modalities vd
            in
            let* _ = signature_item_mode modalities ~allow_redundant_modalities in
            self#signature_item { sigi with psig_desc = Psig_value vd }
          | Psig_extension ((_, PSig sig_), _attrs) ->
            (* Be more cautious when we meet an extension node; we don't know what is done
               with the payload *)
            loop sig_ ~sig_mode:Unknown
          | Psig_type _ ->
            (* If this branch gets specialized logic, make sure it still calls into
               [#type_declaration]. *)
            self#signature_item sigi
          | Psig_extension _
          | Psig_typesubst _
          | Psig_typext _
          | Psig_exception _
          | Psig_modsubst _
          | Psig_modtype _
          | Psig_modtypesubst _
          | Psig_open _
          | Psig_class _
          | Psig_class_type _
          | Psig_attribute _
          | Psig_kind_abbrev _ ->
            (* This is the boundary of the current signature, but keep recurring from here
               to find more nested signatures. *)
            self#signature_item sigi
        in
        let psg_items = trivially_expand_ppx_template psg_items in
        List.map psg_items ~f:check_sigi |> result_list_all
      in
      loop original_sig ~sig_mode:Nonportable
  end
;;

let lint_error ~loc str = Driver.Lint_error.of_string { loc with loc_ghost = true } str

let check_modality_annotations_lint ~raise_on_lint_error =
  if raise_on_lint_error
  then
    check_modality_annotations ~on_error:(fun ~loc ~message ->
      Location.raise_errorf ~loc "%s" message)
  else check_modality_annotations ~on_error:(fun ~loc ~message -> lint_error ~loc message)
;;

let enforce_cold =
  object
    inherit [Driver.Lint_error.t list] Ast_traverse.fold

    method! attribute attr acc =
      let loc = loc_of_attribute attr in
      if !cold_instead_of_inline_never && is_inline attr.attr_name.txt
      then (
        match
          Ast_pattern.(parse (single_expr_payload (pexp_ident __')))
            loc
            attr.attr_payload
            Fn.id
        with
        | exception _ -> acc
        | { Location.loc; txt = Lident "never" } ->
          lint_error ~loc "Attribute error: please use [@cold] instead of [@inline never]"
          :: acc
        | _ -> acc)
      else acc
  end
;;

module Comments_checking = struct
  let errorf ~loc fmt =
    Location.raise_errorf ~loc (Stdlib.( ^^ ) "Documentation error: " fmt)
  ;;

  (* Assumption in the following functions: [s <> ""] *)

  let is_cr_comment s =
    let s = String.trim s in
    String.is_prefix s ~prefix:"CR"
    || String.is_prefix s ~prefix:"XX"
    || String.is_prefix s ~prefix:"XCR"
    || String.is_prefix s ~prefix:"JS-only"
  ;;

  let is_mdx_comment s =
    let s = String.trim s in
    String.is_prefix s ~prefix:"$MDX"
  ;;

  let is_cinaps s = Char.equal s.[0] '$'
  let is_doc_comment s = Char.equal s.[0] '*'
  let is_ignored_comment s = Char.equal s.[0] '_'

  let can_appear_in_mli s =
    is_doc_comment s
    || is_ignored_comment s
    || is_cr_comment s
    || is_cinaps s
    || is_mdx_comment s
  ;;

  let syntax_check_doc_comment ~loc comment =
    let odoc_parser =
      (* The loc and comment passed in begin immediately after the opening paren/star of
         the comment. Given that this is a doc comment, we need to skip past that.
      *)
      let skip_padding = 1 in
      let text = String.sub comment ~pos:skip_padding ~len:(String.length comment - 1) in
      let location =
        (* Without the extra 2, odoc's reported error locations are wrongly shifted. I
           don't know why.
        *)
        { loc.Location.loc_start with
          pos_cnum = loc.loc_start.pos_cnum + skip_padding + 2
        }
      in
      Odoc_parser.parse_comment ~location ~text
    in
    List.iter (Odoc_parser.warnings odoc_parser) ~f:(fun warning ->
      (* A whitelist of odoc errors that we've deemed are OK and have grandfathered
         into the linter.

         Try to avoid adding to this list! Instead, fix the odoc syntax error in the
         doc comment. You are invited to remove things from this list -- just note
         that you'll have to go through and fix existing instances of that error message
         in the tree.
      *)
      match warning.message with
      | "Stray '@'." -> ()
      | str
        when String.is_suffix
               str
               ~suffix:"should be followed by space, a tab, or a new line."
             || String.is_substring str ~substring:"bad markup"
             || String.is_substring str ~substring:"Unknown tag"
             || String.is_substring str ~substring:"Unpaired '}' (end of markup)." -> ()
      | message ->
        let warning_loc =
          let { Odoc_parser.Loc.start; end_; file = _ } = warning.location in
          let loc_start = Odoc_parser.position_of_point odoc_parser start in
          let loc_end = Odoc_parser.position_of_point odoc_parser end_ in
          { loc with loc_start; loc_end }
        in
        errorf
          ~loc:warning_loc
          "odoc syntax error.\n\
           %s\n\
           See https://ocaml.github.io/odoc/odoc/odoc_for_authors.html for odoc syntax \
           help."
          message)
  ;;

  let is_intf_dot_ml fname =
    String.is_suffix (Stdlib.Filename.chop_extension fname) ~suffix:"_intf"
  ;;

  let check_all ?(intf = false) () =
    List.iter
      ~f:(fun (comment, loc) ->
        let intf = intf || is_intf_dot_ml loc.Location.loc_start.Lexing.pos_fname in
        if String.( <> ) comment ""
        then (
          (* Ensures that all comments present in the file are either doc comments or
             (*_ *) comments. *)
          if intf && not (can_appear_in_mli comment)
          then
            errorf
              ~loc
              "That kind of comment shouldn't be present in interfaces.\n\
               Either turn it to a documentation comment or use the special (*_ *) form.";
          if is_doc_comment comment then syntax_check_doc_comment ~loc comment))
      (Lexer.comments ())
  ;;
end

let () =
  (* We rely on the fact that let%test and similar things are preprocessed before we run,
     because ppx_driver applies the [~extension] arguments of
     [Driver.register_transformation] before applying the [~impl] argument that
     ppx_js_style uses. It means that [let%test _ = ..] doesn't count as unannotated
     ignore, although [let%bind _ = ..] also doesn't count as unannotated ignore for the
     same reason. *)
  Driver.add_arg
    "-annotated-ignores"
    (Set annotated_ignores)
    ~doc:
      " If set, forces all ignored expressions (either under ignore or inside a \"let _ \
       = ...\") to have a type annotation. (This is the default.)"
;;

let () =
  let disable_annotated_ignores () = annotated_ignores := false in
  Driver.add_arg
    "-allow-unannotated-ignores"
    (Unit disable_annotated_ignores)
    ~doc:
      " If set, allows ignored expressions (either under ignore or inside a \"let _ = \
       ...\") not to have a type annotation."
;;

let () =
  Driver.add_arg
    "-compat-32"
    (Set compat_32)
    ~doc:" If set, checks that all constants are representable on 32bit architectures."
;;

(* Enable warning 50 by default, one can opt-out with
   [-dont-check-doc-comments-attachment] *)
let () =
  (* A bit hackish: as we're running ppx_driver with -pp the parsing is done by ppx_driver
     and not ocaml itself, so giving "-w @50" to ocaml (as we did up to now) had no
     incidence. We want to enable the warning here. For some reason one can't just enable
     a warning programatically, one has to call [parse_options]... *)
  ignore (Ocaml_common.Warnings.parse_options false "+50")
;;

let () =
  let disable_w50 () = ignore (Ocaml_common.Warnings.parse_options false "-50") in
  Driver.add_arg
    "-dont-check-doc-comments-attachment"
    (Unit disable_w50)
    ~doc:" ignore warning 50 on the file."
;;

let () =
  let disable_check_underscored_literal () = check_underscored_literal := false in
  Driver.add_arg
    "-dont-check-underscored-literal"
    (Unit disable_check_underscored_literal)
    ~doc:" do not check position of underscores in numbers."
;;

let () =
  let enable_checks () = check_comments := true in
  Driver.add_arg
    "-check-doc-comments"
    (Unit enable_checks)
    ~doc:
      " If set, ensures that all comments in .mli files are either documentation or (*_ \
       *) comments. Also check the syntax of doc comments."
;;

let () =
  let allow_top_expr () = allow_toplevel_expression := true in
  Driver.add_arg
    "-allow-toplevel-expression"
    (Unit allow_top_expr)
    ~doc:" If set, allow toplevel expression."
;;

let () =
  let enable () = require_dated_deprecation := true in
  let disable () = require_dated_deprecation := false in
  Driver.add_arg
    "-dated-deprecation"
    (Unit enable)
    ~doc:
      {| If set, ensures that all `[@@deprecated]` attributes must contain \
            the date of deprecation, using the format `"[since MM-YYYY] ..."`.|};
  Driver.add_arg
    "-no-dated-deprecation"
    (Unit disable)
    ~doc:" inverse of -dated-deprecation."
;;

let () =
  let allow () = allow_letop_uses := true in
  let forbid () = allow_letop_uses := false in
  Driver.add_arg "-allow-let-operators" (Unit allow) ~doc:{| allow uses of let-operators|};
  Driver.add_arg
    "-forbid-let-operators"
    (Unit forbid)
    ~doc:{| forbid uses of let-operators|}
;;

let () =
  let allow () = cold_instead_of_inline_never := false in
  let forbid () = cold_instead_of_inline_never := true in
  Driver.add_arg
    "-allow-inline-never"
    (Unit allow)
    ~doc:{| allow uses of [@inline never]|};
  Driver.add_arg
    "-forbid-inline-never"
    (Unit forbid)
    ~doc:{| forbid uses of [@inline never]|}
;;

let () =
  Driver.add_arg
    "-allow-redundant-modalities"
    (Set allow_redundant_modalities)
    ~doc:" Do not warn on modalities that are likely incorrectly used."
;;

let () =
  Driver.add_arg
    "-raise-on-lint-error"
    (Set raise_on_lint_error)
    ~doc:
      " Report an error during linting rather than injecting an error node. This is \
       particularly useful when using the [lint] dune stanza, which ignores typical lint \
       errors."
;;

let () =
  Driver.register_transformation
    "js_style"
    ~lint_intf:(fun sg ->
      let lint_modalities_errors =
        if !allow_redundant_modalities
        then []
        else (
          match
            (check_modality_annotations_lint ~raise_on_lint_error:!raise_on_lint_error)
              #signature
              sg
          with
          | Ok () -> []
          | Error errs -> errs)
      in
      List.concat [ lint_modalities_errors ])
    ~lint_impl:(fun st ->
      let lint_cold_errors =
        (* note: we do not use ~impl because we want the check to run before ppx
           processing (ppx_cold will replace `[@cold]` with `[@inline never] ...`) *)
        enforce_cold#structure st []
      in
      let lint_modalities_errors =
        if !allow_redundant_modalities
        then []
        else (
          match
            (check_modality_annotations_lint ~raise_on_lint_error:!raise_on_lint_error)
              #structure
              st
          with
          | Ok () -> []
          | Error errs -> errs)
      in
      List.concat [ lint_cold_errors; lint_modalities_errors ])
    ~intf:(fun sg ->
      check#signature sg;
      if !check_comments then Comments_checking.check_all ~intf:true ();
      sg)
    ~impl:(fun st ->
      check#structure st;
      if !check_comments then Comments_checking.check_all ();
      st)
;;
