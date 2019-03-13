ppx_js_style - Enforce Jane Street coding styles
================================================

ppx\_js\_style is an identity ppx rewriter that enforces Jane Street
coding styles.

Coding rules
------------

The following rules are enforced by ppx\_js\_style:

- Enabled by -dated-deprecation:
  `[@@deprecated]` attributes must contain the date of deprecation,
  using the format `"[since MM-YYYY] ..."`
  N.B. this check, on by default at janestreet, but off by default externally,
  can also be disabled with the flag -no-dated-deprecation

- Enabled by -annotated-ignores:
  Ignored expressions must come with a type annotation, such as:
    `ignore (expr : typ)`
    `let _ : type = expr`
  Note that aliases need not be annotated:
    `let _ = Foo.bar in`

- Enabled by -check-doc-comments:
  Comments in mli must either be documentation comments or explicitely
  "ignored":
    `(** documentation comment *)`
    `(*_ ignored comment *)`
  Normal `(* comment *)` comments are disallowed.

  This flag additionally enables warning 50, which checks the placement
  of documentation comments.

  Finally, doc comments are checked to be syntactically valid.

- Enabled by -compat-32:
  Checks that calling ocamlc on the input would produce bytecode that
  works on 32 bits architectures (including js\_of\_ocaml), ie that
  all constant are representable on 32 bits architectures. Compared to
  the compiler flag by the same name, it allows to perform this check
  without building any bytecode.

- Enabled by default, disabled by -dont-check-underscored-literal
  Check for misleading usage of underscores in number
  literals. Currrently it means that underscores must be:
  - in positions that are multiple of 3 for numbers in decimal notation.
  - in positions that are multiple of 2 for numbers in hexadecimal,
    octal or binary notation.

  Two consecutive underscores in a number disables the check for that
  number. This is useful to turn off the check for integers that are
  really fixed point decimals, like `1_000__0000` to represent `1000.0`
  with four implied decimal places.
