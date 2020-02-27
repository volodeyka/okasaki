From mathcomp Require Import ssreflect.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Nat.
Require Import Arith.

(** Lazy evaluation notation *)

(** Sus suspends evaluation of x and memorize it *)
Inductive Suspend {T : Type} :=
  Sus of T.

Notation "$ x" := (Sus x) (at level 0, right associativity).

Definition force {T : Type} (x : @Suspend T) : T := 
  match x with
  ($ y)  => y
  end.

Inductive StreamCell {T : Type} :=
  | Nil
  | Cons (x : T) (S : @Suspend (@StreamCell  T)).
  
Definition Stream {T : Type} := @Suspend (@StreamCell T).

(** TODO: fix definitiom of Stream with "with" *)

(* Inductive StreamCell {T : Type} :=
  | Nil
  | Cons (x : T) (S : Stream)
  with  Stream {T : Type} := @Suspend ( @StreamCell T).
 *)

Fixpoint append {T : Type} (s t : @Stream T) {struct s} : @Stream T :=
  $ match s with
    | $ Nil => force t
    | $ (Cons x s1) => Cons x (append s1 t)
    end.

(** Queue repsentet by two lists: fist contains the front elements
     in correct order and sencon contains the rear in reverse
     order *)
Definition Queue (T : Type) : Type := (list T) * (list T).

Definition Invariant {T : Type} (Q : Queue T) : Prop :=
  fst Q = [] -> snd Q = [].

Definition isEmptyP {T : Type} (Q : (Queue T)) :  Prop := 
  match fst Q with
  | [] => True
  | _ => False
  end.
  
Notation "()" := ([], []).

Definition queue {T : Type} (f r : list T) : Queue T :=
  match f, r with
  | [], r => (rev r, [])
  | f, r => (f, r)
  end.

(* rev snoc = cons *)
Definition snoc {T : Type} (Q : (Queue T)) (x : T) :=
  let (f, r) := Q in
  queue f (x :: r).
  
Definition head_opt {T : Type} (Q : Queue T) : option T :=
  match Q with
  | ([], _) => None
  | (x :: f, r) => Some x
  end.
  
Definition tail_opt {T : Type} (Q : Queue T) : option (Queue T) := 
  match Q with
  | ([], _) => None
  | (x :: f, r) => Some (queue f r)
  end.

Definition tail_nil {T : Type} (Q : Queue T) : Queue T := 
  match Q with
  | ([], _) => ()
  | (x :: f, r) => queue f r
  end.


Compute snoc ([], [5; 8]) 9.
