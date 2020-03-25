From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype.
Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
(*Open Scope order_scope.*)

Module REDBLACKSET.
  Section RedBlackSet.
  Notation ordType := (orderType tt).
  
  Inductive Color : Type := R | B.
  
  Inductive Tree := E | T : Color -> Tree -> ordType -> Tree -> Tree.

(*  Inductive Red : Tree -> Prop :=
  | RedN : forall (x : ordType) (t1 t2 : Tree), Red (T R t1 x t2).*)
  
(*  Inductive Black : Tree -> Prop :=
  | BlackN : forall (x : ordType) (t1 t2 : Tree), Black (T B t1 x t2)
  | BlackE : Black E.
  
  Inductive Invariant1 : Tree -> Prop :=
  | CBB : forall (x : ordType) (C : Color) (t1 t2 : Tree)
    (Invarr : Invariant1 t1) (Invarl : Invariant1 t2)
    (Bt1 : Black t1) (Bt2: Black t2), Invariant1 (T C t1 x t2)
  | BCC : forall (x : ordType) (t1 t2 : Tree)
    (Invarr : Invariant1 t1) (Invarl : Invariant1 t2), 
    Invariant1 (T B t1 x t2).*)
  
  
(*  Inductive BST_odered : Tree -> Prop :=*)
  Inductive side := r | l.
  
  Definition colored_path := seq (Color * side).
  Inductive path_in : colored_path -> Tree -> Prop :=
  | Nil_E : path_in nil E
  | Trr_seq : forall (x : ordType) (tr tl : Tree) (p : colored_path)
                     (Pathr : path_in p tr) (c : Color),
                     path_in ((c, r) :: p) (T c tr x tl)
  | Trl_seq : forall (x : ordType) (tr tl : Tree) (p : colored_path)
                     (Pathr : path_in p tl) (c : Color),
                     path_in ((c, l) :: p) (T c tr x tl).
  
  Inductive No_RR : colored_path -> Prop :=
  | N : No_RR nil
  | Bl : forall s, No_RR [:: (B, s)]
  | BC : forall c s1 s2 p (H : No_RR ((c, s2) :: p)),
    No_RR ((B, s1) :: (c, s2) :: p)
  | RB : forall s1 s2 p (H : No_RR ((B, s2) :: p)),
    No_RR ((R, s1) :: (B, s2) :: p).
  
  Inductive last_black : colored_path -> Prop :=
  | End : forall c, last_black [:: (B, c)]
  | St : forall p x (H : last_black p), last_black (x :: p).
  
  Definition Invariant1 (Tr : Tree) : Prop :=
    forall p, path_in p Tr -> No_RR p.
  
  Fixpoint black_length (p : colored_path) : nat :=
    if p is (c, s) :: x then
      if c is B then
        S (black_length x)
      else
        black_length x
    else O.
  
  Definition Invariant2 (Tr : Tree) : Prop :=
    forall p1 p2, path_in p1 Tr -> path_in p2 Tr ->
    black_length p1 = black_length p2.
  
  Definition All_leavs_balck (Tr : Tree) : Prop :=
    forall p, path_in p Tr -> last_black p.
    
  Definition RedBlackTree (Tr : Tree) : Prop :=
    Invariant1 Tr /\ Invariant2 Tr /\ All_leavs_balck Tr.

  Lemma black_length_le_length : forall p, black_length p <= length p.
  Proof.
    elim=> [|[[s l /(@leq_trans _ _ (length l).+1)|]//=]] //; apply=> //.
  Qed.

  Definition list_ind2 := 
  fun (A : Type) (P : seq A -> Prop) (f : P [::]) (f' : forall x, P [:: x])
    (f0 : forall (a b : A) (l : seq A), P l -> P (a :: b :: l)) =>
  fix F (l : seq A) : P l :=
    match l as l0 return (P l0) with
    | [::] => f
    | [:: x] => f' x
    | x :: y :: l0 => f0 x y l0 (F l0)
    end.

  Lemma length_le_2black_length : 
    forall p, No_RR p -> length p <= (black_length p).*2.
  Proof.
    elim/list_ind2=> [//|x H|[[] s [] [] s' l IHl H]] //=;
    inversion H=> //; inversion H1=> //.
    - move: H6 H5=> -> /IHl //.
    - move: H7 H6=> -> /IHl //.
    move: H7 H6=> -> /IHl //.
    rewrite doubleS -addn1 -addn1 -addn2 -addnA leq_add2r=>
    /(@leq_trans _ _ ((black_length l).+1).*2). apply.
    rewrite doubleS.
    by ssrnatlia. 
  Qed.
  
  Theorem path_in_RBT : forall Tr : Tree, RedBlackTree Tr ->
    forall p1 p2, path_in p1 Tr -> path_in p2 Tr ->
    length p1 <= 2 * length p2.
  Proof.
    move=> Tr RBT p1 p2 Pp1 Pp2.
    
  Qed.

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

End REDBLACKSET.
