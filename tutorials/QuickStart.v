From Coq Require Import List.
Import ListNotations.

(** Start by importing PPrint. *)
From PPrint Require Import All.

(** PPrint is based on primitive strings. *)
Open Scope pstring.

(** We will use PPrint to pretty-print expressions which consist of :
    - natural numbers [ENat]
    - variables [EVar]
    - function applications [EFunc] *)
Inductive expr := 
  | ENat : nat -> expr 
  | EVar : string -> expr
  | EFunc : string -> list expr -> expr.

(** PPrint is based around documents of type [doc A], where [A] is a type of 
    annotations (e.g. color, text styling, etc) which must be provided by the user.
    We will ignore annotations in this example (using [unit] in place of [A]).

    This is how to pretty-print an expression to a document [doc unit] : *)
Fixpoint print_expr (e : expr) : doc unit :=
  match e with 
  | ENat n => nat10 n
  | EVar s => str s
  | EFunc f es => 
    let contents := separate (break 2) (str f :: List.map print_expr es) in
    group (paren contents)
  end.
(** Most document combinators are straightfoward :
    - [nat10 n] prints [n] in base 10
    - [str s] print the primitive string [s]
    - [separate sep docs] concatenates the documents in [docs] with a separator [sep] *)

(** Use [pp_string] to print a document to a string (ignoring all annotations).
    [pp_string] takes the screen width (in characters) as argument. *)
Definition mk_expr e := EFunc "add" [e ; EFunc "mult" [EVar "n" ; e] ; EVar "x" ].
Definition e := mk_expr (mk_expr (ENat 2)).
Compute pp_string 80 (print_expr e).
Compute pp_string 40 (print_expr e).
Compute pp_string 20 (print_expr e).

(** The rendering algorithm used by PPrint is simple and efficient (in fact 
    it is linear in the size of the document). It is based around two printing modes :
    flat and normal. 
    
    [ifflat] can be used to render a document differently based on the printing mode.
    [ifflat x y] is printed as [x] in flat mode and as [y] in normal mode. 
    For instance [ifflat space hardline] (abbreviated as [break 0]) is a breakable space : it is printed as a space 
    in flat mode and as a newline in normal mode.

    By default rendering happens in normal mode : the [group] combinator
    introduces a choice point. [group x] prints [x] in flat mode if it fits on the 
    current line, and in normal mode otherwise. Note that in flat mode all further [group] 
    combinators are ignored. 
*)

(** Read the tutorial for a more in-depth overview of the features of PPrint. *)