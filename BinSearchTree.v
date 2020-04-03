From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path eqtype order.
Require Import Psatz.
Import Order.TTheory.
Open Scope order_scope.


Module BST.
  Section BinSearchTree.
  Notation ordType := (orderType tt).
  Variable Elem : ordType.

  Inductive Tree := E | T : Tree -> Elem -> Tree -> Tree.

  Definition EmptyTree := E.

  Inductive LE (x : Elem) : Tree -> Prop :=
    | LE_E : LE x E
    | LE_T : forall y l r (LEQ : x <= y) (LEL : LE x l) (LER : LE x r), LE x (T l y r).

  Inductive GE (x : Elem) : Tree -> Prop :=
    | GE_E : GE x E
    | GE_T : forall y l r (GEQ : x >= y) (GEL : GE x l) (GER : GE x r), GE x (T l y r).

  Inductive BSTOrder : Tree -> Prop :=
    | TO_E : BSTOrder E
    | TO_T : forall x l r (G : GE x l) (L : LE x r) 
              (TOL : BSTOrder l) (TOR : BSTOrder r),
              BSTOrder (T l x r).

  Lemma TOC l x r :
    BSTOrder (T l x r) ->
    GE x l /\ LE x r /\ (BSTOrder l) /\ (BSTOrder r).
  Proof. by move=> H; inversion H. Qed.

  Lemma LEC x l y r :
    LE x (T l y r) ->
    (x <= y) /\ LE x l /\ LE x r.
  Proof. by move=> H; inversion H. Qed.

  Lemma GEC x l y r :
    GE x (T l y r) ->
    (x >= y) /\ GE x l /\ GE x r.
  Proof. by move=> H; inversion H. Qed.

  Lemma LEG (x x' : Elem) (Tr : Tree) : (x' <= x) /\ LE x Tr -> LE x' Tr.
  Proof.
    elim: Tr=> [_ | l IHl y r IHr [x'x L]]; first by apply: LE_E.
    move: (LEC _ _ _ _ L)=> [xy] [Ll] Lr; constructor; first by apply: le_trans x'x xy.
    - by apply: IHl.
    by apply: IHr.
  Qed.

  Lemma GEL (x x' : Elem) (Tr : Tree) : (x' >= x) /\ GE x Tr -> GE x' Tr.
  Proof.
    elim: Tr=> [_ | l IHl y r IHr [x'x G]]; first by apply: GE_E.
    move: (GEC _ _ _ _ G)=> [yx] [Gl] Gr; constructor; first by apply: le_trans yx x'x.
    - by apply: IHl.
    by apply: IHr.
  Qed.

  Fixpoint member (x : Elem) (Tr : Tree) : Prop :=
    match Tr with
    | E => false
    | T a y b => if x < y then member x a else if x > y then member x b else true
    end.

  (** member function with at most d + 1 comparisons where d is the depth of a tree*)
  Fixpoint candidate (x : Elem) (Tr : Tree) (cand : option Elem) : Prop :=
    match Tr with
    | E => if cand is Some c then if x == c then true else false
           else false
    | T a y b => if x < y then candidate x a cand else candidate x b (Some y)
    end.

  Definition member' (x : Elem) (Tr : Tree) : Prop := candidate x Tr None.
(** TODO: finish memberE proof *)
  Lemma memberE (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr = candidate x Tr None.
  Proof.
  Admitted.

  Fixpoint insert (x : Elem) (Tr : Tree) : Tree :=
    match Tr with
    | E => T E x E
    | T a y b => if x < y then T (insert x a) y b else
                   if x > y then T a y (insert x b) else T a y b
    end.

  Lemma member_LE (x x' : Elem) (Tr : Tree) : LE x Tr /\ (member x' Tr) -> x <= x'.
  Proof.
    elim: Tr=> [|l IHl y r IHr /= [L M]]; first by elim.
    move: (LEC _ _ _ _ L)=> [LEQ] [Ll] Lr. case: (ltgtP x' y).
    - by move=> x'y; rewrite x'y in M; rewrite IHl.
    - by move=> yx'; rewrite yx' in M; rewrite lt_gtF in M; rewrite ?IHr.
    by move=> xy; rewrite -xy in LEQ.
  Qed.

  Lemma member_GE (x x' : Elem) (Tr : Tree) : GE x Tr /\ (member x' Tr) -> x >= x'.
  Proof.
    elim: Tr=> [|l IHl y r IHr /= [G M]]; first by elim.
    move: (GEC _ _ _ _ G)=> [GEQ] [Gl] Gr. case: (ltgtP x' y).
    - by move=> x'y; rewrite x'y in M; rewrite IHl.
    - by move=> yx'; rewrite yx' in M; rewrite lt_gtF in M; rewrite ?IHr.
    by move=> xy; rewrite -xy in GEQ.
  Qed.

  Lemma insert_LE (x x' : Elem) (Tr : Tree) : LE x Tr /\ (x <= x') -> LE x (insert x' Tr).
  Proof.
    elim: Tr=> [[L LEQ] | l IHl y r IHr /= [L M]]; first by constructor.
    move: (LEC _ _ _ _ L)=> [LEQ] [Ll] Lr.
    case: (ltgtP x' y); try by [].
    - move=> x'y; constructor; try by []; by apply: IHl.
    - move=> yx'; constructor; try by []; by apply: IHr.
  Qed.

  Lemma insert_GE (x x' : Elem) (Tr : Tree) : GE x Tr /\ (x >= x') -> GE x (insert x' Tr).
  Proof.
    elim: Tr=> [[G GEQ] | l IHl y r IHr /= [G M]]; first by constructor.
    move: (GEC _ _ _ _ G)=> [GEQ] [Gl] Gr.
    case: (ltgtP x' y); try by [].
    - move=> x'y; constructor; try by []; by apply: IHl.
    - move=> yx'; constructor; try by []; by apply: IHr.
  Qed.

  Theorem BSTOrder_preserved (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : BSTOrder (insert x Tr).
  Proof.
    elim: BS=> [| x' l t Gl Lr TOL TOLx TOR TORx /=]; first by constructor; constructor.
    case: ltgtP.
      - move=> xx'; constructor; try by [].
        apply: insert_GE; split. by []. by apply: (ltW xx').
      - move=> x'x; constructor; try by [].
        apply: insert_LE; split. by []. by apply: (ltW x'x).
      by constructor.
  Qed.

  End BinSearchTree.
End BST.
