From Coq Require Import List.
Import ListNotations.

(** The coq-pprint API is in module PPrint. *)
From PPrint Require Import All.

(** * Documents. *)

(** PPrint is based around a type of _documents_ `doc A` (`A` is a type of 
    _annotations_ which we will explain later). You can think of a document as 
    a string which can adapt to different screen widths. *)

(** Turning a document into a string is called _rendering_. The easiest way to 
    render a document is to use the function `pp_string`. *)
Check (@pp_string : forall A, nat -> doc A -> string).
(** Ignore the parameter `A` for the moment. `pp_string` takes as arguments : 
    - A maximum screen width, measured in number of characters. A typical value
      is 80 characters.
    - A document to render. *)

(** Most of the API exported by PPrint is about constructing documents.
    [str s] creates a document which is always printed as [s]. *)
Compute pp_string 80 (str "I am an atomic document.").

(** [nat10 n] is printed as the base 10 representation of the natural number [n]. *)
Compute pp_string 80 (nat10 42).

(** Documents can be concatenated just as easily as strings :
    - [x ^^ y] is printed as [x] followed by [y].
    - [x ^+^ y] additionally adds a space between [x] and [y]. *)
Compute pp_string 80 (nat10 3 ^+^ str "is a bad number.").

(** * Adapting to screen width. *)

(** Let's try a slightly more interesting example : printing a sentence (i.e. a list
    of words separated by spaces). *)
Definition sentence : list (doc unit) := 
  List.map str 
    [ "I" ; "am" ; "a" ; "somewhat" ; "long" ; "sentence" ; "which" 
    ; "should" ; "be" ; "printed" ; "on" ; "several" ; "lines." ].
(** We can use the combinators [space] which is printed as a single space, and [separate sep docs] 
    which concatenates the documents in [docs] while separating them with [sep] : *)
Compute pp_string 80 (separate space sentence).
Compute pp_string 10 (separate space sentence).
(** The sentence is printed on a single line no matter the screen width ! *)

(** This is where _printing modes_ come in. There are two printing modes :
    flat and normal. 
    
    The `ifflat x y` combinator can be used to print a document differently depending on the current mode. 
    `ifflat x y` is printed as `x` in flat mode and as `y` in normal mode. 
    
    The `group x` combinator introduces a choice point : `x` is printed in flat mode 
    if it fits on the current line, and in normal mode otherwise. 
    
    By default the rendering engine is in normal mode. Once in flat mode, 
    there is no possibility to return to normal mode, and all `group`s are ignored. *)
Definition breakable_doc : doc unit := 
  group (str "I am a" ^^ ifflat space hardline ^^ str "breakable" ^^ 
         ifflat space hardline ^^ str "document").
Compute pp_string 80 breakable_doc. (** The document fits on the current line and is printed in flat mode. *)
Compute pp_string 20 breakable_doc. (** The document does not fit and is printed in normal mode. *)
(** In fact the document `ifflat space hardline` is so common that it is 
    abbreviated as `break 0`. *)

(** Let's try to render our sentence so that lines breaks are naturally inserted : *)
Compute pp_string 20 (group (separate (break 0) sentence)).
(** This is not quite what we wanted : all words are on a separate line ! 
    This is because we used a single `group` : either we have only spaces, or only newlines.
    Instead we should have a different `group` for each word. This is exactly what `flow` does : *)
Compute pp_string 20 (flow (break 0) sentence).
Compute pp_string 40 (flow (break 0) sentence).
Compute pp_string 80 (flow (break 0) sentence).

(** * Indentation. *)



(** * Annotations. *)

(** * Writing a custom backend. *)

(*- what are documents

!! it is not recommended to use the constructors of [doc] directly.

- adapting to page width : ifflat & group
two printing modes : flat and normal.

- handling indentation : nest & align
there is an implicit "indentation level" [n] : after each newline, 
[n] blank characters are inserted.
The core functions to manipulate the indentation level are `align` and `nest` :
`nest n` increases the current indentation level by `n`.
+ add example.
`align` sets the current indentation level to the current column.
+ add example.

*)