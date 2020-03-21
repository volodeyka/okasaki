From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import Psatz.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
From Coq Require Import Lists.List.
Import ListNotations.

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

Module FINITEMAP.
  Record class (Map : Type -> Type) := Class
  {
    KEY : Type;

    Empty {T : Type} : Map T ;
    Bind {T : Type} : KEY -> T -> Map T -> Map T;
    Lookup {T : Type} : KEY -> Map T -> option T
  }.
  Structure type := Pack { sort : Type -> Type; class_of : class sort }.

  Section Exports.

  Coercion sort : type >-> Funclass.

  Variables (M : type).
  Definition Key : Type := KEY (class_of M).

  Variables (T : Type).
  Definition empty : M T := Empty (class_of M).
  Definition lookup : Key -> M T -> option T := Lookup (class_of M).
  Definition bind : Key -> T -> M T -> M T := Bind (class_of M).
  
  End Exports.

  Arguments Class {_}.

End FINITEMAP.

Export ORDERED.

Module BINSRCTREE_SET.

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

Definition UnbalancedClass : SET.class Tree := SET.Class Elem empty insert member.
Canonical UnbalancedSet : SET.type := SET.Pack UnbalancedClass.
End TreeDef.


End BINSRCTREE_SET.

Module BINSRCTREE_MAP.

Section FinMapDef.
Variables (Key : ordType) (A : Type).

Inductive Tree :=
| E : Tree
| T : Tree -> Key -> A -> Tree -> Tree.

Fixpoint bind (k : Key) (x : A) (Tr : Tree) : Tree :=
  if Tr is T a k' y b then
    if lt k k' then
       T (bind k x a) k' y b
    else 
      if lt k' k then
        T a k' y (bind k x b)
      else 
        T a k' y b
  else
    T E k x E.
  
Fixpoint lookup (k : Key) (Tr : Tree) : option A :=
  if Tr is T a k' y b then
    if lt k k' then
      lookup k a
    else
      if lt k' k then
        lookup k b
      else Some y
  else None.

  Definition empty := E.

End FinMapDef.

Arguments Tree {_}.
Arguments bind {_}.
Arguments lookup {_}.
Arguments empty {_}.

Definition UnbalancedMap (Key : ordType) : FINITEMAP.class Tree :=
  FINITEMAP.Class Key empty bind lookup.
Canonical UnbalancedSet (Key : ordType) : FINITEMAP.type := FINITEMAP.Pack (UnbalancedMap Key).

End BINSRCTREE_MAP.

Module REDBLACKSET.
  Section RedBlackSet.
  Variables Elem : ordType.
  
  Inductive Color : Type := R | B.

  Inductive Tree := E | T : Color -> Tree -> Elem -> Tree -> Tree.

  Fixpoint member (x : Elem) (Tr : Tree) : bool :=
    if Tr is T _ a y b then
      if lt x y then
        member x a
      else 
        if lt y x then
          member x b
        else true
    else false.
  
    Definition balance (C : Color) (a : Tree) (x : Elem) (b : Tree) : Tree :=
      match C, a, x, b with
      | B, T R (T R a x b) y c, z, d => T R (T  B a x b) y (T B c z d)
      | B, T R a x (T R b y c), z, d => T R (T  B a x b) y (T B c z d)
      | B, a, x, T R (T R b y c) z d => T R (T  B a x b) y (T B c z d)
      | B, a, x, T R b y (T R c z d) => T R (T  B a x b) y (T B c z d) 
      | C, a, x, b                   => T C a x b
      end.
    
  Fixpoint ins (x : Elem) (s : Tree) : Tree :=
    if s is T color a y b then
      if lt x y then
        balance color (ins x a) y b
      else
        if lt y x then
          balance color a y (ins x b)
        else s
    else T R E x E.
  
  Definition insert (x : Elem) (s : Tree) :=
    if ins x s is T _ a y b then T B a y b else E.
  
  Program Fixpoint balance' (l : list (Color * Elem * Tree)) {measure (length l)} : list (Color * Elem * Tree) :=
    match l with 
    | [(R, v1, t1)] => [(B, v1, t1)]
    | (R, v1, t1) :: (R, v2, t2) :: (B, v3, t3) :: xs => 
      (B, v1, t1) :: (balance' ((R, v2, (T B t3 v3 t2)) :: xs))
    | xs => xs
    end.
  Next Obligation.
    by move=> /=; lia.
  Qed.
  Solve All Obligations with done.

  Fixpoint ins' (ts : list (Color * Elem * Tree)) (l : list Elem) :=
  match ts, l with 
  | ts, x :: xs => ins' (balance' ((R, x, E)::ts)) xs
  | ts, [] => ts
  end.

  Fixpoint toTree (Tr : Tree) (l : list (Color * Elem * Tree)) : Tree :=
  match Tr, l with 
  | t, [] => t
  | t, (color, v, t') :: ts => toTree (T color t' v t) ts
  end.

  Definition fromOrdList (l : list Elem) : Tree := toTree E (ins' [] l).

  Definition lbalance (C : Color) (a : Tree) (x : Elem) (b : Tree) : Tree :=
  match C, a, x, b with
  | B, T R (T R a x b) y c, z, d => T R (T  B a x b) y (T B c z d)
  | B, T R a x (T R b y c), z, d => T R (T  B a x b) y (T B c z d)
  | C, a, x, b                   => T C a x b
  end.

  Definition rbalance (C : Color) (a : Tree) (x : Elem) (b : Tree) : Tree :=
  match C, a, x, b with
  | B, a, x, T R (T R b y c) z d => T R (T  B a x b) y (T B c z d)
  | B, a, x, T R b y (T R c z d) => T R (T  B a x b) y (T B c z d) 
  | C, a, x, b                   => T C a x b
  end.

  Fixpoint insrl (x : Elem) (s : Tree) : Tree :=
  if s is T color a y b then
    if lt x y then
      lbalance color (insrl x a) y b
    else
      if lt y x then
        rbalance color a y (insrl x b)
      else s
  else T R E x E.

  Definition insertrl (x : Elem) (s : Tree) :=
    if insrl x s is T _ a y b then T B a y b else E.
  
  Definition balance'' (C : Color) (a : Tree) (x : Elem) (b : Tree) : Tree :=
  match C, a, x, b with
    | B, T R (T R a x b) y c, z, d => T R (T  B a x b) y (T B c z d) 
    | C, a, x, b                     => T C a x b
    end.

  Fixpoint ins'' (x : Elem) (s : Tree) : Tree :=
    if s is T color a y b then
      if lt x y then
        balance'' color (ins'' x a) y b
      else
        if lt y x then
          balance'' color (ins'' x b) y a
        else s
    else T R E x E.
  
  Definition insert' (x : Elem) (s : Tree) :=
    if ins'' x s is T _ a y b then T B a y b else E.

Definition RedBlackClass : SET.class Tree := SET.Class Elem E insert member.
Canonical RedBlackSet : SET.type := SET.Pack RedBlackClass.
  End RedBlackSet.
End REDBLACKSET.
