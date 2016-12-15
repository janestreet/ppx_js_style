open Ppx_core.Std

let annotated_ignores = ref false;;
let check_comments = ref false;;

let errorf ~loc fmt =
  Location.raise_errorf ~loc
    ("Jane Street style: " ^^ fmt)
;;

module Ignored_reason = struct
  type t = Argument_to_ignore | Underscore_pattern
  let fail ~loc _t =
    errorf ~loc "Ignored expression must come with a type annotation"
end

module Invalid_deprecated = struct
  type t =
    | Not_a_string
    | Missing_date
    | Invalid_month
  let fail ~loc = function
    | Not_a_string ->
      errorf ~loc "Invalid [@@deprecated payload], must be a string"
    | Missing_date ->
      errorf ~loc "deprecated message must start with the date in this format: \
                   [since YYYY-MM]"
    | Invalid_month ->
      errorf ~loc "invalid month in deprecation date"
end

type error =
  | Invalid_deprecated of Invalid_deprecated.t
  | Missing_type_annotation of Ignored_reason.t

let fail ~loc = function
  | Invalid_deprecated e -> Invalid_deprecated.fail e ~loc
  | Missing_type_annotation e -> Ignored_reason.fail e ~loc
;;

let check_deprecated_string ~f ~loc s =
  match Scanf.sscanf s "[since %u-%u]" (fun y m -> (y, m)) with
  | exception _ -> f ~loc (Invalid_deprecated Missing_date)
  | (_year, month) ->
    if month = 0 || month > 12 then f ~loc (Invalid_deprecated Invalid_month)
;;

let not_really_a_binding ~ext_name:s =
  List.mem s [
    "test"; "test_unit"; "test_module";
    "bench"; "bench_fun"; "bench_module";
    "expect"; "expect_test";
  ]
;;

let ignored_expr_must_be_annotated ignored_reason (expr : Parsetree.expression) ~f =
  match expr.pexp_desc with
  (* explicitely annotated -> good *)
  | Pexp_constraint _
  | Pexp_coerce _
  (* no need to warn people trying to silence other warnings *)
  | Pexp_construct _
  | Pexp_ident _
  | Pexp_fun _
  | Pexp_function _
    -> ()
  | _ -> f ~loc:expr.pexp_loc (Missing_type_annotation ignored_reason)
;;

let iter_style_errors ~f = object (self)
  inherit Ast_traverse.iter as super

  method! attribute (name, payload) =
    let loc = loc_of_attribute (name, payload) in
    match name.txt with
    | "ocaml.deprecated" | "deprecated" ->
      begin match
        Ast_pattern.(parse (single_expr_payload (estring __'))) loc payload (fun s -> s)
      with
      | exception _ -> f ~loc (Invalid_deprecated Not_a_string)
      | { Location. loc; txt = s } -> check_deprecated_string ~f ~loc s
      end
    | _ -> ()

  method! value_binding vb =
    if !annotated_ignores then (
      let loc = vb.Parsetree.pvb_loc in
      match Ast_pattern.(parse ppat_any) loc vb.Parsetree.pvb_pat () with
      | exception _ -> ()
      | () -> ignored_expr_must_be_annotated Underscore_pattern ~f vb.Parsetree.pvb_expr
    );
    super#value_binding vb

  method! extension (ext_name, payload as ext) =
    if not !annotated_ignores then super#extension ext else
    if not (not_really_a_binding ~ext_name:ext_name.Location.txt) then
      self#payload payload
    else
      (* We want to allow "let % test _ = ..." (and similar extensions which don't
        actually bind) without warning. *)
      match payload with
      | PStr str ->
        let check_str_item i =
          let loc = i.Parsetree.pstr_loc in
          Ast_pattern.(parse (pstr_value __ __)) loc i
            (fun _rec_flag vbs ->
              List.iter super#value_binding vbs)
        in
        List.iter check_str_item str
      | _ ->
        super#payload payload

  method! expression e =
    if !annotated_ignores then (
      match e with
      | [%expr ignore [%e? ignored]] ->
        ignored_expr_must_be_annotated Argument_to_ignore ~f ignored
      | _ -> ()
    );
    super#expression e
end

let check = iter_style_errors ~f:fail

module Comments_checking = struct
  let errorf ~loc fmt =
    Location.raise_errorf ~loc ("Documentation error: " ^^ fmt)

  (* Assumption in the following functions: [s <> ""] *)

  let is_cr_comment s =
    let s = String.trim s in
    (try String.sub s 0 2 = "CR"  with _ -> false) ||
    (try String.sub s 0 2 = "XX"  with _ -> false) ||
    (try String.sub s 0 3 = "XCR" with _ -> false) ||
    (try String.sub s 0 7 = "JS-only" with _ -> false)

  let is_doc_comment s = s.[0] = '*'

  let is_ignored_comment s = s.[0] = '_'

  let can_appear_in_mli s = is_doc_comment s || is_ignored_comment s || is_cr_comment s

  let syntax_check_doc_comment ~loc comment =
    match Octavius.parse (Lexing.from_string comment) with
    | Ok _ -> ()
    | Error { Octavius.Errors. error ; location } ->
      let octavius_msg = Octavius.Errors.message error in
      let octavius_loc =
        let { Octavius.Errors. start ; finish } = location in
        let loc_start = loc.Location.loc_start in
        let open Lexing in
        let loc_start =
          let pos_bol = if start.line = 1 then loc_start.pos_bol else 0 in
          { loc_start with
            pos_bol;
            pos_lnum = loc_start.pos_lnum + start.line - 1;
            pos_cnum =
              if start.line = 1 then
                loc_start.pos_cnum + start.column
              else
                start.column
          }
        in
        let loc_end =
          let pos_bol = if finish.line = 1 then loc_start.pos_bol else 0 in
          { loc_start with
            pos_bol;
            pos_lnum = loc_start.pos_lnum + finish.line - 1;
            pos_cnum =
              if finish.line = 1 then
                loc_start.pos_cnum + finish.column
              else
                finish.column
          }
        in
        { loc with Location. loc_start; loc_end }
      in
      errorf ~loc:octavius_loc
        "%s\nYou can look at \
         http://caml.inria.fr/pub/docs/manual-ocaml/ocamldoc.html#sec318\n\
         for a description of the recognized syntax."
        octavius_msg

  let is_intf_dot_ml fname =
    let fname  = Filename.chop_extension fname in
    let length = String.length fname in
    length > 5 && String.sub fname (length - 5) 5 = "_intf"

  let check_all ?(intf=false) () =
    List.iter (fun (comment, loc) ->
      let intf = intf || is_intf_dot_ml loc.Location.loc_start.Lexing.pos_fname in
      if (comment <> "") then (
        (* Ensures that all comments present in the file are either ocamldoc comments
           or (*_ *) comments. *)
        if intf && not (can_appear_in_mli comment) then begin
          errorf ~loc
            "That kind of comment shouldn't be present in interfaces.\n\
             Either turn it to a documentation comment or use the special (*_ *) form."
        end;
        if is_doc_comment comment then syntax_check_doc_comment ~loc comment
      )
    ) (Lexer.comments ())
end

let () =
  Ppx_driver.add_arg "-annotated-ignores"
    (Arg.Set annotated_ignores)
    ~doc:" If set, forces all ignored expressions (either under ignore or \
          inside a \"let _ = ...\") to have a type annotation."
;;

let () =
  let enable_checks () =
    check_comments := true;
    (* A bit hackish: as we're running ppx_driver with -pp the parsing is done
       by ppx_driver and not ocaml itself, so giving "-w @50" to ocaml (as we
       did up to now) had no incidence.
       We want to enable the warning here. For some reason one can't just enable
       a warning programatically, one has to call [parse_options]... *)
    Warnings.parse_options false "+50";
  in
  Ppx_driver.add_arg "-check-doc-comments" (Arg.Unit enable_checks)
    ~doc:" If set, ensures that all comments in .mli files are either \
          documentation or (*_ *) comments.\n\
          Also enables warning 50 on the file, and check the syntax of doc comments."
;;

let () =
  Ppx_driver.register_transformation "js_style"
    ~intf:(fun sg ->
      check#signature sg;
      if !check_comments then Comments_checking.check_all ~intf:true ();
      sg
    )
    ~impl:(fun st ->
      check#structure st;
      if !check_comments then Comments_checking.check_all ();
      st
    )
;;
