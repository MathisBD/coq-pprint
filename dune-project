(lang dune 3.16)

(using coq 0.9)

(name coq-pprint)

; The .opam file is regenerated each time you call dune build.
; To manually regenerate the .opam file, run :
; $ dune build coq-pprint.opam

(generate_opam_files true)

(package
 (name coq-pprint)
 (license MIT)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (homepage "https://github.com/MathisBD/coq-pprint")
 (bug_reports "https://github.com/MathisBD/coq-pprint/issues")
 (synopsis "A modern combinator pretty-printing library for Coq")
 (description
  "A combinator pretty-printing library, in the style of Wadler's \"A Prettier Printer\".\n- Handles utf-8 strings.\n- Supports generic _annotations_ on text (colors, italics, etc).\n- Well documented.")
 (depends
  (coq
   (>= dev))))
