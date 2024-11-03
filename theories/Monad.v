(** This file defines the usual monad typeclass. 
    Ideally we would use a generic monad library instead of rolling our own here. *)

Set Universe Polymorphism.

(** The usual monad typeclass. *)
Class Monad (M : Type -> Type) :=
{
  ret : forall A, A -> M A ;
  bind : forall A B, M A -> (A -> M B) -> M B
}.
Arguments ret  {M} {_} {A}.
Arguments bind {M} {_} {A B}.

(** A bit of notation for monads. *)

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Notation "'mlet' x <- e1 ;; e2" := (@bind _ _ _ _ e1 (fun x => e2))
  (at level 100, e1 at next level, right associativity, x pattern) : monad_scope.

Notation "e1 ;; e2" := (@bind _ _ _ _ e1 (fun _ => e2))
  (at level 100, right associativity) : monad_scope.



