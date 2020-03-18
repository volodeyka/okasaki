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
(* TODO: Invariant of Binary Search Trees *)
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

(* In the worst case, member performs ap-
proximately 2d comparisons, where d is the depth of the tree. memder_candidate
takes no more than d + 1 comparisons by keeping track of a candidate ele-
ment that might be equal to the query element (the last element for which
< returned false) and checking for equality only when hits the bottom of the tree. *)
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
  
(* Inserting an existing element into a binary search tree copies the
entire search path even though the copied nodes are indistinguishable from the
originals. insert_except uses option to avoid this copying. Established only
one handler per insertion rather than one handler per iteration. *)
Fixpoint insert (x : Elem) (Tr : Tree) : Tree :=
if Tr is T a y b then 
  if lt x y then
    T (insert x a) y b
  else 
    if lt y x then
      T a y (insert x b)
    else T a y b
else T E x E.

Fixpoint insert_except' (x : Elem) (Tr : Tree) : option Tree :=
if Tr is T a y b then 
  if lt x y then
    if insert_except' x a is Some t then
      Some (T t y b)
    else None
  else
    if lt y x then
      if insert_except' x b is Some t then
        Some (T a y t)
      else None
    else None
else Some (T E x E).

Definition insert_except (x : Elem) (Tr : Tree) : Tree :=
if insert_except' x Tr is Some t then t else Tr.

(* Combined the ideas of the previous two exercises to obtain a ver-
sion of insert that performs no unnecessary copying and uses no more than
d + 1 comparisons. *)
Fixpoint insert_except_candidate' (x : Elem) (Tr : Tree) (candidate : option Elem) : option Tree :=
if Tr is  T a y b then
  if lt x y then
    if insert_except_candidate' x a candidate is Some t then
      Some (T t y b)
    else None
  else insert_except_candidate' x b (Some y)
else
  if candidate is Some cand then
    None
  else Some (T E x E).

Definition insert_except_candidate (x : Elem) (Tr : Tree) : Tree :=
  if insert_except_candidate' x Tr None is Some t then t else Tr.

Theorem insert_eqviv1 : forall x y Tr, 
  member x (insert y Tr) = member x (insert_except y Tr).
Proof.
Admitted.

Theorem insert_eqviv2 : forall x y Tr, 
  member x (insert y Tr) = member x (insert_except_candidate y Tr).
Proof.
Admitted.
    
(*  Sharing can also be useful within a single object, not just be-
tween objects. For example, if the two subtrees of a given node are identical,
then they can be represented by the same tree. *)

(*Using this idea, function complete of type Elem x int -> Tree
where complete (x, d) creates a complete binary tree of depth d with x
stored in every node.*)

Fixpoint complete (x : Elem) (d : nat) : Tree :=
  if d is d'.+1 then let t := complete x d' in T t x t
  else E.

(* ctreate extends comlete to create balanced trees of arbitrary size. These trees
  will not always be complete binary trees, but should be as balanced as
  possible: for any given node, the two subtrees should differ in size by at
  most one. This function runs in O(log n) time (considering thet division and 
  submision takes O(1)). *)
Fixpoint div2 (n : nat) :=
  match n with
  | S (S n) => div2 n
  | _       => O
  end.

Program Fixpoint create (x : Elem) (m : nat) {mesure m} : Tree :=
  if m is m'.+1 then
    let n := div2 m' in
    if eqn n (m' - n) then
      let t := complete x n in T t x t
    else T (create x n) x (create x (n.+1))
  else E.
Next Obligation.
  exact nat.
Qed.

End TreeDef.

Arguments Tree   {_}.
Arguments member {_}.
Arguments insert {_}.
Arguments empty {_}.
Print SET.Pack.

Definition UnbalancedClass (Elem : ordType) : SET.class Tree := SET.Class Elem empty insert member.
Canonical UnbalancedSet (Elem : ordType) : SET.type := SET.Pack (UnbalancedClass Elem).
