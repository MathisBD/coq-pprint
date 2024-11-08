(** * Tutorial. *)

(** The coq-pprint API is in modules PPrint. *)
From PPrint Require Import All.

(** PPrint is based around a type of _documents_ `doc A` (`A` is a type of 
    _annotations_ which we will explain later). You can think of a document as 
    a string which can adapt to different screen widths. 
*)

(** The empty document is printed as an empty string. *)
Compute pp_string empty.

(** [str] is used to *)
Compute pp_string (str "hello").
Compute

- what are documents

!! it is not recommended to use the constructors of [doc] directly.

- atomic documents & concatenating

str
nat10
space

- adapting to page width : ifflat & group
two main printing modes : flat and normal.

- handling indentation : nest & align
there is an implicit "indentation level" [n] : after each newline, 
[n] blank characters are inserted.
The core functions to manipulate the indentation level are `align` and `nest` :
`nest n` increases the current indentation level by `n`.
+ add example.
`align` sets the current indentation level to the current column.
+ add example.

*)