From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import Lia.

Set Implicit Arguments.

Module ORDERED.

  Record class (T : Type) := Class
  {
      Eq : T -> T -> bool;
      Lt : T -> T -> bool;
      Leq : T -> T -> bool
  }.
  Structure type := Pack { sort : Type; class_of : class sort }.

  Section Exports.

  Coercion sort : type >-> Sortclass.
  Variables (ord : type).
  Definition eq := Eq (class_of ord).
  Definition lt := Lt   (class_of ord).
  Definition leq := Leq (class_of ord).

  End Exports.

  Notation ordType := type.
  Arguments eq {_}.
  Arguments lt {_}.
  Arguments leq {_}.
End ORDERED.

Module SET.

Record class (S : Type) := Class
{
    Element : Type;

    Empty : S;
    Insert : Element -> S -> S;
    Member : Element -> S -> bool
}.
Structure type := Pack { sort : Type; class_of : class sort }.

Section Exports.

Coercion sort : type >-> Sortclass.
Variables (S : type).
Definition element := Element (class_of S).
Definition insert := Insert (class_of S).
Definition member := Member (class_of S).

End Exports.
Arguments Class {_}.

End SET.

Export ORDERED.

Section TreeDef.
Variables Elem : ordType.

Inductive Tree : Type :=
  | E : Tree
  | T : Tree -> Elem -> Tree -> Tree.

  Definition empty : Tree := E.

  Fixpoint member (x : Elem) (Tr : Tree) : bool :=
    if Tr is (T a y b) then 
        if 
          lt x y then member x a
        else 
          if lt y x 
            then member x b
          else true
    else false.

  Fixpoint member_candidate' (x : Elem) (Tr : Tree) (candidate : option Elem) : bool :=
  if Tr is T a y b then
    if lt x y then 
      member_candidate' x a candidate
    else
      member_candidate' x b (Some y)
  else
    if candidate is Some cand then
      if eq x cand then
        true
      else false
    else false.

  Definition member_candidate (x : Elem) (Tr : Tree) := member_candidate' x Tr None.

  Theorem member_eqviv : forall x Tr, member x Tr = member_candidate x Tr.
  Proof.
  Admitted.
  

  Fixpoint insert (x : Elem) (Tr : Tree) : Tree :=
  if Tr is (T a y b) then 
    if lt x y then
      T (insert x a) y b
    else 
      if lt y x then
        T a y (insert x b)
      else T a y b
  else T E x E.

End TreeDef.

Arguments Tree   {_}.
Arguments member {_}.
Arguments insert {_}.
Arguments empty {_}.
Print SET.Pack.

Definition UnbalancedClass (Elem : ordType) : SET.class Tree := SET.Class Elem empty insert member.
Canonical UnbalancedSet (Elem : ordType) : SET.type := SET.Pack (UnbalancedClass Elem).
