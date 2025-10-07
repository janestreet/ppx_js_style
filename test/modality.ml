open! Base
open! Expect_test_helpers_base
module Format = Stdlib.Format

module Helpers : sig
  val require_success : here:[%call_pos] -> string -> unit
  val require_failure : here:[%call_pos] -> string -> unit
end = struct
  let check_portable =
    Ppx_js_style.check_modality_annotations ~on_error:(fun ~loc ~message ->
      let message =
        Ppxlib.Location.print Format.str_formatter loc;
        Format.pp_force_newline Format.str_formatter ();
        Format.pp_print_string Format.str_formatter message;
        Format.flush_str_formatter ()
      in
      message, loc)
  ;;

  let cleanup_input str =
    let str = String.chop_prefix_if_exists str ~prefix:"\n" in
    let str = String.chop_suffix_if_exists str ~suffix:"\n" in
    str
  ;;

  let parse_and_lint str =
    Lexing.from_string str ~with_positions:true
    |> Ppxlib.Parse.interface
    |> check_portable#signature
  ;;

  let print_underline_loc str ~(loc : Ppxlib.Location.t) =
    let lines = String.split ~on:'\n' str in
    let start = loc.loc_start in
    let stop = loc.loc_end in
    print_endline "```";
    List.iteri lines ~f:(fun i line ->
      print_endline line;
      let i = i + 1 in
      if start.pos_lnum <= i && i <= stop.pos_lnum
      then (
        let start_col =
          if start.pos_lnum = i then start.pos_cnum - start.pos_bol else 0
        in
        let stop_col =
          if i = stop.pos_lnum then stop.pos_cnum - stop.pos_bol else String.length line
        in
        let string = String.make start_col ' ' ^ String.make (stop_col - start_col) '^' in
        print_endline string));
    print_endline "```"
  ;;

  let print_errors ~original_code errs =
    List.iter errs ~f:(fun (message, loc) ->
      print_endline message;
      print_underline_loc original_code ~loc)
  ;;

  let require_success ~(here : [%call_pos]) str =
    let str = cleanup_input str in
    match parse_and_lint str with
    | Ok () -> print_endline "ok"
    | Error errs ->
      print_cr ~here (Atom "Expected no error, got error:");
      print_errors ~original_code:str errs
  ;;

  let require_failure ~(here : [%call_pos]) str =
    let str = cleanup_input str in
    match parse_and_lint str with
    | Ok () -> print_cr ~here (Atom "Expected error, got none.")
    | Error errs -> print_errors ~original_code:str errs
  ;;
end

open Helpers

let%expect_test "okay portable annotations" =
  (* No modalities *)
  require_success
    {|
val a : int -> int
module T : sig
  val b : int -> int
  module U : sig
    val c : int -> int
  end
  val d : int -> int
end
val e : int -> int
|};
  [%expect {| ok |}];
  (* Portable annotations on individual vals *)
  require_success
    {|
val a : int -> int @@ portable
module T : sig
  val b : int -> int @@ portable
  module U : sig
    val c : int -> int @@ portable
  end
  val d : int -> int @@ portable
end
val e : int -> int @@ portable
|};
  [%expect {| ok |}];
  (* Default portability annotation on outer signature *)
  require_success
    {|
@@ portable
val a : int -> int
module T : sig
  val b : int -> int
  module U : sig
    val c : int -> int
  end
  val d : int -> int
end
val e : int -> int
|};
  [%expect {| ok |}];
  (* Default portability annotation on inner signature *)
  require_success
    {|
val a : int -> int
module T : sig @@ portable
  val b : int -> int
  module U : sig
    val c : int -> int
  end
  val d : int -> int
end
val e : int -> int
|};
  [%expect {| ok |}];
  (* Portable modality on submodule *)
  require_success
    {|
val a : int -> int
module (T @@ portable) : sig
  val b : int -> int
  module U : sig
    val c : int -> int
  end
  val d : int -> int
end
val e : int -> int
|};
  [%expect {| ok |}];
  (* Portable modality on sibling submodules *)
  require_success
    {|
val a : int -> int
module T : sig
  val b : int -> int
  module (U1 @@ portable) : sig
    val c : int -> int
  end
  val d : int -> int
  module (U2 @@ portable) : sig
    val c : int -> int
  end
end
val e : int -> int
|};
  [%expect {| ok |}];
  (* Portable modality on functors *)
  require_success
    {|
module Functor (X : S @ portable) : S @ portable
|};
  [%expect {| ok |}];
  (* Portable modality on other items *)
  require_success
    {|
val a : int -> int
module T : sig
  val b : int -> int @@ portable
  include S @@ portable
  module U : S @@ portable
  include sig
    val c : int -> int
  end @@ portable
  module (Functor @@ portable) (X : S) : S
end
val e : int -> int
|};
  [%expect {| ok |}];
  ()
;;

let%expect_test "okay nonportable annotations" =
  (* Nonportable on various items *)
  require_success
    {|
@@ portable
val x : int -> int @@ nonportable
module (T @@ nonportable) : sig
  val y : int -> int
end
module (F @@ nonportable) (X : S) : S
include S @@ nonportable
include sig
  val z : int -> int
end @@ nonportable
|};
  [%expect {| ok |}];
  (* Nonportable module with portable items *)
  require_success
    {|
@@ portable
module (T @@ nonportable) : sig
  val a : int -> int @@ portable
end
|};
  [%expect {| ok |}];
  (* Nonportable module with default portable signature *)
  require_success
    {|
@@ portable
module (T @@ nonportable) : sig @@ portable
  module (U @@ nonportable) : sig @@ portable
    val a : int -> int @@ nonportable
  end
end
|};
  [%expect {| ok |}];
  ()
;;

let%expect_test "default modality in portable signature" =
  (* portable default modality *)
  require_failure
    {|
module (T @@ portable) : sig @@ portable
  val x : int -> int
end
|};
  [%expect
    {|
    File "", line 1, characters 32-40:
    Modality linting error: This signature is forced portable by a containing signature, so the default modality annotation does nothing.
    ```
    module (T @@ portable) : sig @@ portable
                                    ^^^^^^^^
      val x : int -> int
    end
    ```
    |}];
  (* nonportable default modality *)
  require_failure
    {|
module (T @@ portable) : sig @@ nonportable
  val x : int -> int
end
|};
  [%expect
    {|
    File "", line 1, characters 32-43:
    Modality linting error: This signature is forced portable by a containing signature, so the default modality annotation does nothing.
    ```
    module (T @@ portable) : sig @@ nonportable
                                    ^^^^^^^^^^^
      val x : int -> int
    end
    ```
    |}];
  (* module portable via default *)
  require_failure
    {|
@@ portable
module T : sig @@ portable
  val x : int -> int
end
|};
  [%expect
    {|
    File "", line 2, characters 18-26:
    Modality linting error: This signature is forced portable by a containing signature, so the default modality annotation does nothing.
    ```
    @@ portable
    module T : sig @@ portable
                      ^^^^^^^^
      val x : int -> int
    end
    ```
    |}];
  (* module portable via enclosing module *)
  require_failure
    {|
module (T @@ portable) : sig
  module U : sig @@ portable
    val x : int -> int
  end
end
|};
  [%expect
    {|
    File "", line 2, characters 20-28:
    Modality linting error: This signature is forced portable by a containing signature, so the default modality annotation does nothing.
    ```
    module (T @@ portable) : sig
      module U : sig @@ portable
                        ^^^^^^^^
        val x : int -> int
      end
    end
    ```
    |}];
  ()
;;

let%expect_test "nonportable default modality" =
  (* entire nonportable signature *)
  require_failure
    {|
@@ nonportable
val x : int -> int
|};
  [%expect
    {|
    File "", line 1, characters 3-14:
    Modality linting error: Using [nonportable] as a default modality has no effect.
    ```
    @@ nonportable
       ^^^^^^^^^^^
    val x : int -> int
    ```
    |}];
  (* nonportable submodule default modality *)
  require_failure
    {|
module T : sig @@ nonportable
  val x : int -> int
end
|};
  [%expect
    {|
    File "", line 1, characters 18-29:
    Modality linting error: Using [nonportable] as a default modality has no effect.
    ```
    module T : sig @@ nonportable
                      ^^^^^^^^^^^
      val x : int -> int
    end
    ```
    |}];
  (* functor argument *)
  require_failure
    {|
module F (X : sig @@ nonportable val x : int -> int end) : sig
  val x : int -> int
end
|};
  [%expect
    {|
    File "", line 1, characters 21-32:
    Modality linting error: Using [nonportable] as a default modality has no effect.
    ```
    module F (X : sig @@ nonportable val x : int -> int end) : sig
                         ^^^^^^^^^^^
      val x : int -> int
    end
    ```
    |}];
  ()
;;

let%expect_test "ignored modality annotation" =
  (* portable annotation ignored *)
  require_failure
    {|
module (T @@ portable) : sig
  val x : int -> int @@ portable
end
|};
  [%expect
    {|
    File "", line 2, characters 24-32:
    Modality linting error: This modality annotation is ignored.
    ```
    module (T @@ portable) : sig
      val x : int -> int @@ portable
                            ^^^^^^^^
    end
    ```
    |}];
  (* nonportable annotation ignored *)
  require_failure
    {|
module (T @@ portable) : sig
  val x : int -> int @@ nonportable
end
|};
  [%expect
    {|
    File "", line 2, characters 24-35:
    Modality linting error: This modality annotation is ignored.
    ```
    module (T @@ portable) : sig
      val x : int -> int @@ nonportable
                            ^^^^^^^^^^^
    end
    ```
    |}];
  (* annotation on signature ignored *)
  require_failure
    {|
module (T @@ portable) : sig
  module (U @@ nonportable) : sig
    val x : int -> int
  end
end
|};
  [%expect
    {|
    File "", line 2, characters 15-26:
    Modality linting error: This modality annotation is ignored.
    ```
    module (T @@ portable) : sig
      module (U @@ nonportable) : sig
                   ^^^^^^^^^^^
        val x : int -> int
      end
    end
    ```
    |}];
  (* annotation on include ignored *)
  require_failure
    {|
module (T @@ portable) : sig
  include S @@ portable
end
|};
  [%expect
    {|
    File "", line 2, characters 15-23:
    Modality linting error: This modality annotation is ignored.
    ```
    module (T @@ portable) : sig
      include S @@ portable
                   ^^^^^^^^
    end
    ```
    |}];
  ()
;;

let%expect_test "redundant modalities" =
  (* redundant portable modality *)
  require_failure
    {|
@@ portable
val x : int -> int @@ portable
|};
  [%expect
    {|
    File "", line 2, characters 22-30:
    Modality linting error: This portable annotation is redundant.
    ```
    @@ portable
    val x : int -> int @@ portable
                          ^^^^^^^^
    ```
    |}];
  (* redundant nonportable modality *)
  require_failure
    {|
val x : int -> int @@ nonportable
|};
  [%expect
    {|
    File "", line 1, characters 22-33:
    Modality linting error: This nonportable annotation is redundant.
    ```
    val x : int -> int @@ nonportable
                          ^^^^^^^^^^^
    ```
    |}];
  (* redundant nonportable modality (more complex) *)
  require_failure
    {|
@@ portable
module (T @@ nonportable) : sig
  val x : int -> int @@ nonportable
end
|};
  [%expect
    {|
    File "", line 3, characters 24-35:
    Modality linting error: This nonportable annotation is redundant.
    ```
    @@ portable
    module (T @@ nonportable) : sig
      val x : int -> int @@ nonportable
                            ^^^^^^^^^^^
    end
    ```
    |}];
  ()
;;

let%expect_test "interactions with ppx_template and unrecognized modalities" =
  (* stateless modality *)
  require_success
    {|
module T : sig @@ stateless
  val a : int -> int @@ portable
  val b : int -> int @@ nonportable
end

module (U @@ stateless) : sig
  val a : int -> int @@ stateless
  val b : int -> int @@ stateful
end

module V : sig @@ portable
  val a : int -> int @@ stateless
  val b : int -> int @@ stateful
end
|};
  [%expect {| ok |}];
  (* template is transparent *)
  require_success
    {|
module T : sig @@ portable
  [%%template:
    val x : int -> int @@ nonportable
    [@@@mode.default m = (local, global)]
    val y : int -> int
  ]
end

module%template T : sig @@ portable
  val x : int -> int @@ nonportable
  [@@@mode.default m = (local, global)]
  val y : int -> int
end
|};
  [%expect {| ok |}];
  (* template floating attributes introduce [include sig ... end] *)
  require_failure
    {|
module%template T : sig @@ portable
  [@@@mode m = (local, global)]
  val x : int -> int @@ nonportable
end
|};
  [%expect
    {|
    File "", line 3, characters 24-35:
    Modality linting error: This modality annotation is ignored.
    ```
    module%template T : sig @@ portable
      [@@@mode m = (local, global)]
      val x : int -> int @@ nonportable
                            ^^^^^^^^^^^
    end
    ```
    |}];
  require_failure
    {|
module%template T : sig @@ portable
  [@@@mode m = (local, global)]

  module M : sig @@ portable
    val x : int -> int
  end
end
|};
  [%expect
    {|
    File "", line 4, characters 20-28:
    Modality linting error: This signature is forced portable by a containing signature, so the default modality annotation does nothing.
    ```
    module%template T : sig @@ portable
      [@@@mode m = (local, global)]

      module M : sig @@ portable
                        ^^^^^^^^
        val x : int -> int
      end
    end
    ```
    |}];
  (* template variables over modalities are treated conservatively *)
  require_success
    {|
module%template T : sig @@ portable
  val z : int -> int @@ p
end
[@@modality p = (nonportable, portable)]

module%template U : sig @@ p
  val x : int -> int @@ portable
  val y : int -> int @@ nonportable
  val z : int -> int @@ q
end
[@@modality p = (nonportable, portable), q = (nonportable, portable)]
|};
  [%expect {| ok |}];
  ()
;;
