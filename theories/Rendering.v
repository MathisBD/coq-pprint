From Coq Require Import List Uint63 PrimString.
From PPrint Require Import Monad Documents.
Import ListNotations.
Open Scope monad_scope.

Set Universe Polymorphism.

(** * Pretty-printing monads. *)

(** The rendering engine does not output strings directly : it is parametric over
    a pretty-printing monad, which provides a low-level output interface.
   
    [MonadPPrint Ann M] states that [M] is a monad which supports pretty-printing documents
    with annotations of type [Ann]. The job of [M] is to :
    - accumulate strings : [add_string].
    - deal with annotations of type [Ann] : [enter_annot], [exit_annot]. 

    Annotations can be nested. For instance :
      [enter_annot a1 ;; add_string "hello" ;; 
       enter_annot a2 ;; add_string "world" ;; 
       exit_annot a2 ;; exit_annot a1]
    will print "hello" with annotation [a1] followed by "world" with annotation [a2].
    Calls to [enter_annot]/[exit_annot] are always well-parenthesized.
*)
Class MonadPPrint (Ann : Type) (M : Type -> Type) :=
{
  add_string : string -> M unit ;
  enter_annot : Ann -> M unit ;
  exit_annot : Ann -> M unit ;
}.

(** * Rendering a document. *)

Section Rendering.

(** The rendering engine is parameterized by a pretty printing monad. *)
Context {Ann : Type} {M : Type -> Type} {MonadM : Monad M} {MonadPPrintM : MonadPPrint Ann M}.

(** [prettyM doc flat width indent col] is the main function in the rendering engine :
    - [doc] is the document we are printing.
    - [flat] is [true] if we are in flat mode, otherwise it is [false].
    - [width] is the maximum character width we are allowed to use.
    - [indent] is the current indentation level : [indent] blank characters are added after each newline.
    - [col] is the current column index, starting at 0.
    The return value contains the updated column index.

    Making this function tail recursive would require a bit more work.
    I would have to define a [MonadTailRec] class (as in PureScript for instance),
    and require a [MonadTailRec] instance on the pretty printing monad [M].
*)
Fixpoint prettyM (doc : doc Ann) (flat : bool) (width indent col : nat) : M nat :=
  match doc with
  | Empty => ret col
  | Str len s => add_string s ;; ret (col + len)
  | Blank n => add_string (PrimString.make (of_nat n) " "%char63) ;; ret (col + n)
  | HardLine => 
    (* We should be in normal mode here. *)
    add_string (PrimString.make 1 10%int63) ;; 
    add_string (PrimString.make (of_nat indent) " "%char63) ;;
    ret indent
  | IfFlat _ doc1 doc2 =>
      (* Print [doc1] or [doc2] depending on the current mode. *)
      prettyM (if flat then doc1 else doc2) flat width indent col
  | Cat _ doc1 doc2 =>
      (* Print [doc1] followed by [doc2], threading the column index. *)
      bind (prettyM doc1 flat width indent col) (fun col =>
        prettyM doc2 flat width indent col)
  | Nest _ n doc => 
      (* Simply increase the indentation amount. *)
      prettyM doc flat width (indent + n) col
  | Group req doc =>
      (* Determine if [doc] should be flattened. *)
      let doc_flat := 
        match req with 
        | Width req => Nat.leb (col + req) width
        | Infinity => false
        end
      in
      (* Take care to stay in flattening mode if we are already in it. *)
      prettyM doc (flat || doc_flat) width indent col
  | Align _ doc => 
      (* Set the indentation amount to the current column. *)
      prettyM doc flat width col col
  | Annot _ ann doc =>
      enter_annot ann ;;
      mlet col <- prettyM doc flat width indent col ;;
      exit_annot ann ;;
      ret col
  end.

(** [pp width doc] pretty-prints the document [doc],
    using a maximum character width of [width]. *)
Definition ppM (width : nat) doc : M unit :=
  (* We start in normal mode, but immediately decide if we should switch to flat mode
     using a [group]. *)
  prettyM (group doc) false width 0 0 ;; ret tt.

End Rendering.

(** * Basic MonadPPrint instance. *)

(** [PPString A] is a monad that supports pretty-printing documents to strings,
    and simply ignores annotations. It is implemented as a state monad, where the 
    state is the list of strings printed so far (with the most recent strings at
    the head of the list). 
    
    Storing strings in this way allows delaying the actual concatenation until 
    the very end, avoiding the classic quadratic issue with repeated string concatenation. *)
Definition PPString A := list string -> A * list string.

(** Monad instance : just a state monad. *)
Instance monad_ppstring : Monad PPString :=
{
  ret _ x ls := (x, ls) ;
  bind _ _ mx mf ls :=
    let (x, ls) := mx ls in
    mf x ls
}.

(** MonadPPrint instance. This works for any annotation type [Ann]. *)
Instance monad_pprint_ppstring {Ann : Type} : MonadPPrint Ann PPString :=
{
  add_string s ls := (tt, s :: ls) ;
  enter_annot _ := ret tt ;
  exit_annot _ := ret tt
}.

(** [pp_string width d] pretty-prints the document [d] to a string, 
    ignoring all annotations. *)
Definition pp_string {Ann} (width : nat) (d : doc Ann) : string :=
  let '(_, output) := @ppM Ann PPString _ _ width d [] in
  List.fold_left PrimString.cat (List.rev output) (PrimString.make 0 0%int63).