From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import Lia.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Set Implicit Arguments.

Module STACK.
  Record class (stack : Type -> Type) := Class
  {
    (* original from Okasaki *)
    (*stack (T : Type) :  Type;*)
    Empty {T : Type} : stack T;
    IsEmpty {T : Type} : (stack T) -> bool;

    Cons {T : Type} : T -> stack T -> stack T;
    Head {T : Type} : stack T -> option T;
    Tail {T : Type} : stack T -> stack T;

    (* for proofs *)
    Length {T : Type} : stack T -> nat;
    Spec_isEmpty {T : Type} :
        forall (st : stack T), (IsEmpty st = true) <-> Length st = 0;
    Spec_len {T : Type} : forall (st : stack T), Length (Tail st) = (Length st).-1
  }.
  Structure type := Pack { sort : Type -> Type; class_of : class sort }.

  Section Exports. 
    Local Coercion sort : type >-> Funclass.
    Variables T : Type.
    Variables stack : type.
        
    Definition isEmpty : stack T -> bool := IsEmpty (class_of stack).

    Definition length : stack T -> nat := Length (class_of stack).

    Definition head : stack T -> option T := Head (class_of stack).

    Definition tail : stack T -> stack T := Tail (class_of stack).

    Definition cons : T -> stack T -> stack T := Cons (class_of stack).

    Definition empty : stack T := Empty (class_of stack).    

    Definition spec_isEmpty : forall (st : stack T), (isEmpty st = true) <-> length st = 0
    := Spec_isEmpty (class_of stack).

    Definition spec_len : forall (st : stack T), length (tail st) = (length st).-1
    := Spec_len (class_of stack).

  End Exports.
    
  Arguments cons {_ _}.
  Arguments length {_ _}.
  Arguments tail {_ _}.
  Arguments head {_ _}.
  Arguments empty {_ _}.
  Arguments isEmpty {_ _}.
  Arguments spec_isEmpty {_ _}.
  Arguments spec_len {_ _}.

  Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
  Notation "[]" := empty.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

  Section Operations.
    Variables stack : type.

    Coercion sort : type >-> Funclass.

    (** TODO: ssreflect proof *)
    Program Fixpoint append {T : Type} (st1 st2 : stack T) {measure (length st1)} : stack T :=
      if (isEmpty st1) is true then st2 else 
      if head st1 is Some x then x :: (append (tail st1) st2)
      else st1.
    Next Obligation.
    Proof.    
      - rewrite spec_len.
        assert (length st1 <> 0).
        move=> se; apply: H. symmetry.
        by apply spec_isEmpty.
      by lia.
    Qed.

    Notation "st1 ++ st2" := (append st1 st2) (at level 60, right associativity).
    
    (* Returns empty if cannot update *)
    Fixpoint update {T : Type} (st : stack T) (i : nat) (x : T) {struct i} : stack T :=
      if isEmpty st is true then [] else
      if i is i'.+1 then 
      update (tail st) i' x else
      x :: (tail st).

  (** TODO: ssreflect proof *)
    Program Fixpoint suffixes {T : Type} (st : stack T) {measure (length st)} : stack (stack T) :=
      if isEmpty st is true then [] else st :: (suffixes (tail st)).
    Next Obligation.
    Proof.
      - rewrite spec_len.
        assert (length st <> 0).
        move=> se; apply: H. symmetry.
        by apply spec_isEmpty.
      by lia.
    Qed.

  End Operations.
  
End STACK.
(** TODO: instanses *)
