From Coq Require Import Bool List Uint63 PrimString NArith.BinNat. 
From PPrint Require Import Utils.
Import ListNotations.

(** * Width requirements. *)

(** All documents have a space requirement. This is the document's apparent length, 
    if printed in *flattening* mode. 
    This information is computed in a bottom-up manner when the document is constructed.

    In other words, the space requirement is the number of columns that the
    document needs in order to fit on a single line.
*)
Inductive requirement :=
  (** [Infinity] is used for a document which cannot be printed on single line.
      This happens e.g. if the document contains a hardline. *)
  | Infinity : requirement 
  (** [Width n] is used for a document which takes [n] characters in flat mode. *)
  | Width : nat -> requirement. 

(** [add_requirements r1 r2] adds the requirements [r1] and [r2], 
    taking care that adding infinity results in infinity. *)
Definition add_requirements (r1 r2 : requirement) : requirement :=
  match r1, r2 with 
  | Width w1, Width w2 => Width (w1 + w2)
  | _, _ => Infinity
  end. 

(** * Documents. *)

(** The type of documents, which depends on the type of annotations.
    The only construct which actually uses annotations is [Annot]. *)
Inductive doc (A : Type) : Type :=   
  (** [Empty] is the empty document. *)
  | Empty : doc A
  (** [Blank n] is an atomic document that consists of [n] blank characters. *)
  | Blank : nat -> doc A
  (** [Str len s] is an atomic string [s] of _apparent_ length [len].

      The apparent length of a string is the number of (unicode) code points which appear 
      in the string. In general this might be less than the number of bytes in the string : 
      in UTF8 each code point is encoded using 1 to 4 bytes.
   
      We assume (but do not check) that strings do not contain a newline character. *)
  | Str : nat -> string -> doc A
  (** [IfFlat req d1 d2] turns into the document :
      - [d1] in flattening mode.
      - [d2] in normal mode. 
      In particular [req] is equal to the requirement of [d1].
     
      We maintain the invariant that [d1] should not itself be of the form [IfFlat _ _].
      Users should use the function [ifflat] defined below to ensure this invariant is preserved.
  *)
  | IfFlat : requirement -> doc A -> doc A -> doc A
  (** When in flattening mode, [HardLine] causes a failure, which requires
      backtracking all the way until the stack is empty. When not in flattening
      mode, it represents a newline character, followed with an appropriate
      number of indentation. A common way of using [HardLine] is to only use it
      directly within the right branch of an [IfFlat] construct. *)
  | HardLine
  (** [Cat req doc1 doc2] is the concatenation of the documents [doc1] and [doc2]. 
      The space requirement [req] is the sum of the requirements of [doc1] and [doc2]. *)
  | Cat : requirement -> doc A -> doc A -> doc A
  (** [Nest req n doc] is the document [doc], in which the indentation
      level has been increased by [n], that is in which [n] blanks have been
      inserted after every newline character. 
      The space requirement [req] is the same as the requirement of [doc]. *)
  | Nest : requirement -> nat -> doc A -> doc A
  (** [Group req doc] represents an alternative: it is either a flattened
      form of [doc], in which occurrences of [Group] disappear and occurrences
      of [IfFlat] resolve to their left branch, or [doc] itself. 
      The space requirement [req] is the same as the requirement of [doc]. *)
  | Group : requirement -> doc A -> doc A
  (** [Align req doc] increases the indentation level to reach the current column.
      Thus, the document [doc] is rendered within a box whose upper
      left corner is the current position.
      The space requirement [req] is the same as the requirement of [doc]. *)
  | Align : requirement -> doc A -> doc A
  (** [Annot req ann doc] annotates the document [doc] with annotation [ann].
      The space requirement [req] is the same as the requirement of [doc]. *)
  | Annot : requirement -> A -> doc A -> doc A.

Arguments Empty    {A}%_type_scope.
Arguments Blank    {A}%_type_scope.
Arguments Str      {A}%_type_scope.
Arguments IfFlat   {A}%_type_scope.
Arguments HardLine {A}%_type_scope.
Arguments Cat      {A}%_type_scope.
Arguments Nest     {A}%_type_scope.
Arguments Group    {A}%_type_scope.
Arguments Align    {A}%_type_scope.
Arguments Annot    {A}%_type_scope.

(** Retrieve or compute the space requirement of a doc. This is constant-time. *)
Definition doc_requirement {A} (d : doc A) : requirement :=
  match d with 
  | Empty => Width 0
  | Blank len => Width len
  | Str len _ => Width len
  | IfFlat req _ _ => req
  | HardLine => Infinity
  | Cat req _ _ => req
  | Nest req _ _ => req
  | Group req _ => req
  | Align req _ => req
  | Annot req _ _ => req
  end.

(** Storing requirement information at [Group] nodes is crucial, as it allows us to
    avoid backtracking and buffering.

    Storing this information at other nodes allows the function [doc_requirement]
    to operate in constant time. This means that the bottom-up computation of
    requirements takes linear time. 
*)

(** * Atomic documents. *)
    
Section AtomicDocuments.
Context {A : Type}.

(** [empty] is the empty document. *)
Definition empty : doc A := Empty.

(** [char c] is an atomic document that consists of the single character [c].
    This character must not be a newline character, although we do not check it. *)
Definition char (c : char63) : doc A := 
  Str 1 (PrimString.make 1%int63 c).

(** [str s] is an atomic document which consists of the utf8 primitive string [s]. 
    We assume (but do not check) that [s] does not contain a newline. *)
Definition str (s : PrimString.string) : doc A :=
  Str (utf8_length s) s.

(** [nat2 n] is an atomic document which consists in the binary representation
    of the natural number [n]. *)
Definition nat2 (n : nat) : doc A :=
  str (string_of_binary (N.of_nat n)).

(** [nat10 n] is an atomic document which consists in the base 10 representation
    of the natural number [n]. *)
Definition nat10 (n : nat) : doc A :=
  str (string_of_decimal (Nat.to_uint n)).

(** [nat16 n] is an atomic document which consists in the base 16 representation
    of the natural number [n]. *)
Definition nat16 (n : nat) : doc A :=
  str (string_of_hexadecimal (Nat.to_hex_uint n)).
    
(** Warning : most of the time you should use the higher-level functions [softline] or [break].

    [hardline] represents a forced newline.
    This document has infinite ideal width: thus, if there is a choice between printing it
    in flat mode and printing it in normal mode, normal mode is preferred. 
    In other words, when [hardline] is placed directly inside a group, this
    group is dissolved: [group hardline] is equivalent to [hardline]. 
    This combinator should be seldom used; consider using [break 0] instead. *)
Definition hardline : doc A := HardLine.
    
(** [softline] represents an optional newline :
    - in normal mode it is printed as a newline. 
    - in flat mode it disappears. *)
Definition softline : doc A := IfFlat (Width 0) Empty HardLine.

(** The atomic document [blank n] consists of [n] blank characters. *)
Definition blank n : doc A := 
  match n with 
  | 0 => Empty
  | _ => Blank n
  end.
    
(** [space] is a synonym for [blank 1]. It consists of one blank character. *)
Definition space : doc A := Blank 1.
   
(** [break n] is a breakable space, which is printed as :
    - a space in flat mode, 
    - a newline character followed by [n] spaces in normal mode. *)
Definition break (n : nat) : doc A := 
  (* This is extremely common so I inline some functions. *)
  IfFlat (Width 1) (Blank 1) (Cat Infinity HardLine (Blank n)). 

End AtomicDocuments.

(** * Document combinators. *)

Section Combinators.
Context {A : Type}. 

(** [cat doc1 doc2] or [doc1 ^^ doc2] is the concatenation of the documents [doc1] and [doc2]. *) 
Definition cat doc1 doc2 : doc A :=
  match doc1, doc2 with 
  | Empty, _ => doc2
  | _, Empty => doc1
  | _, _ => Cat (add_requirements (doc_requirement doc1) (doc_requirement doc2)) doc1 doc2
  end.

(** [ifflat doc1 doc2] produces a document which is printed as :
    - [doc1] in flat mode. 
    - [doc2] in normal mode. *)
Definition ifflat doc1 doc2 : doc A :=
  match doc1 with 
  | IfFlat req doc1 _ => IfFlat req doc1 doc2
  | _ => IfFlat (doc_requirement doc1) doc1 doc2
  end.

(** [group doc] encodes a choice. If the document [doc] fits on the current
    line, then it is rendered on a single line, in flat mode. (All [group]
    combinators inside it are then ignored.) Otherwise, this group is
    dissolved and [doc] is rendered in normal mode. There might be more
    groups within [doc], whose presence leads to further choices being
    explored. *)
Definition group d : doc A :=
  match doc_requirement d with
  | Infinity => d
  | req => Group req d
  end.
   
(** Warning : most of the time you want to use [align] instead of [nest].

    To render the document [nest n doc], the printing engine temporarily
    increases the current indentation level by [n], then renders [doc]. 
    The effect of the current indentation level is as follows: every time a
    newline character is emitted, it is immediately followed by [n] blank
    characters, where [n] is the current indentation level. 
    Thus, one may think of [nest n doc] roughly as the document [doc] in which [n] blank
    characters have been inserted after every newline character. *)
Definition nest n d : doc A :=
  Nest (doc_requirement d) n d.

(** To render [align doc], the printing engine sets the current indentation
    level to the current column, then renders [doc]. In other words, the
    document [doc] is rendered within a box whose upper left corner is the
    current position of the printing engine. *)
Definition align d : doc A :=
  Align (doc_requirement d) d.

(** [annotate ann doc] is rendered as [doc], surrounded by the annotation [ann].
    The meaning of annotations is backend-dependent (see below). *)
Definition annotate annot d : doc A := 
  Annot (doc_requirement d) annot d.

Notation "d1 ^^ d2" := (cat d1 d2) (at level 60, right associativity).

(** [repeat n doc] is the document obtained by concatenating [n] copies of
    the document [doc]. *)
Fixpoint repeat n d : doc A :=
  match n with 
  | 0 => empty 
  | S n => d ^^ repeat n d
  end.

(** [concat docs] is the concatenation of the documents in the list [docs]. *)
Fixpoint concat ds : doc A :=
  match ds with 
  | [] => empty 
  | d :: ds => d ^^ concat ds
  end.
    
(** [concat_map f xs] is shorthand for [concat (List.map f xs)]. *)
Definition concat_map {T} (f : T -> doc A) (xs : list T) : doc A :=
  concat (List.map f xs).

(** [separate sep docs] is the concatenation of the documents in the list [docs]. 
    The separator [sep] is inserted between every two adjacent documents. *)
Fixpoint separate sep ds : doc A :=
  match ds with 
  | [] => empty
  | [d] => d
  | d :: ds => d ^^ sep ^^ separate sep ds
  end.

(** [separate_map sep f xs] is shorthand for [separate sep (List.map f xs)]. *)
Definition separate_map {T} sep (f : T -> doc A) (xs : list T) : doc A :=
  separate sep (List.map f xs).

(** [hang n doc] is analogous to [align], but additionally indents all lines
    except the first one by [n] spaces. *)
Definition hang n d : doc A := align (nest n d).
    
(** [flow sep docs] separates the documents in the list [docs] with the
    separator [sep] and arranges for a new line to begin whenever a document
    does not fit on the current line. 
    
    A typical choice of [sep] is [break 0] for free-flowing text
    or [str "," ^^ break 0] for a list. *)
Definition flow sep ds : doc A :=
  match ds with 
  | [] => empty 
  | [d] => d
  | d :: ds => d ^^ concat_map (fun d' => group (sep ^^ d')) ds 
  end.

(** [flow_map sep f docs] is shorthand for [flow sep (List.map f xs)]. *)
Definition flow_map {T} sep (f : T -> doc A) (xs : list T)  : doc A :=
  flow sep (List.map f xs).
  
(** [bracket left doc right] surrounds [doc] with brackets [left] and [right]. 
    In flat mode it simply concatenates everything :
    [
      leftdocright
    ]
    In normal mode it makes sure to increase the indentation level (using [align]), 
    yielding the following layout :
    [
      leftdoc1
          doc2
          doc3right
    ]
*)
Definition bracket lbracket contents rbracket : doc A :=
  str lbracket ^^ align contents ^^ str rbracket.
  
(** [paren doc] surrounds [doc] with parentheses. 
    It sets the indentation level as explained in [bracket]. *)
Definition paren contents : doc A :=
  bracket "(" contents ")".

End Combinators.

(** [x ^^ y] concatenates [x] and [y]. *)
Notation "d1 ^^ d2" := (cat d1 d2) (at level 60, right associativity).

(** [x ^+^ y] separates [x] and [y] with a non-breakable space. *)
Notation "x ^+^ y" := (x ^^ space ^^ y) (at level 60, right associativity).

(** [x ^/^ y] separates [x] and [y] with a breakable space. *)
Notation "x ^/^ y" := (x ^^ break 0 ^^ y) (at level 60, right associativity).

(** [x ^/^ y] separates [x] and [y] with a breakable space [break 2]. *)
Notation "x ^//^ y" := (x ^^ break 2 ^^ y) (at level 60, right associativity).
