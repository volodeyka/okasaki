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

Fixpoint LT (x : Elem) (Tr : Tree) : bool :=
if Tr is T l y r then (LT x l) && (LT x r) && (x < y) else true.

Fixpoint GT (x : Elem) (Tr : Tree) : bool :=
if Tr is T l y r then (GT x l) && (GT x r) && (x > y) else true.

Fixpoint BSTOrder (Tr : Tree) : bool :=
if Tr is T l x r then (GT x l) && (LT x r) && (BSTOrder l) && (BSTOrder r) else true.

Lemma TOC l x r :
BSTOrder (T l x r) ->
GT x l /\ LT x r /\ (BSTOrder l) /\ (BSTOrder r).
Proof. by move=> /= /andP[/andP[/andP[]]]. Qed.

Lemma LTC x l y r :
LT x (T l y r) ->
(x < y) /\ LT x l /\ LT x r.
Proof. by move=> /= /andP[/andP[]]. Qed.

Lemma GTC x l y r :
GT x (T l y r) ->
(x > y) /\ GT x l /\ GT x r.
Proof. by move=> /= /andP[/andP[]]. Qed.

Lemma LEG (x x' : Elem) (Tr : Tree) : (x' < x) /\ LT x Tr -> LT x' Tr.
Proof.
elim: Tr=> [_ | l IHl y r IHr [x'x L]]; first by [].
move: (LTC _ _ _ _ L)=> [xy] [Ll] Lr /=. apply/andP; split. apply/andP; split.
- by apply: IHl.
- by apply: IHr.
by apply: (lt_trans x'x xy).
Qed.

Lemma GTL (x x' : Elem) (Tr : Tree) : (x' > x) /\ GT x Tr -> GT x' Tr.
Proof.
elim: Tr=> [_ | l IHl y r IHr [x'x G]]; first by [].
move: (GTC _ _ _ _ G)=> [xy] [Gl] Gr /=. apply/andP; split. apply/andP; split.
- by apply: IHl.
- by apply: IHr.
by apply: (lt_trans xy x'x).
Qed.

Fixpoint member (x : Elem) (Tr : Tree) : bool :=
match Tr with
| E => false
| T a y b => if x < y then member x a else if x > y then member x b else true
end.

(** member function with at most d + 1 comparisons where d is the depth of a tree*)
Fixpoint candidate (x : Elem) (Tr : Tree) (cand : option Elem) : bool :=
match Tr with
| E => if cand is Some c then if x == c then true else false
       else false
| T a y b => if x < y then candidate x a cand else candidate x b (Some y)
end.

Definition member' (x : Elem) (Tr : Tree) : bool := candidate x Tr None.

Lemma nhd_member (x x' : Elem) (Tr : Tree) (BS : BSTOrder Tr) (NEQ : x != x') :
      candidate x Tr None = candidate x Tr (Some x').
Proof.
elim: Tr BS=> /=. by rewrite ifN_eq.
move=> l IHl y r IHr /andP[/andP[/andP[Gl Lr] BSl] BSr]. case: ltgtP.
- move=> xy. by apply: IHl.
- by [].
by [].
Qed.

Lemma mem_in_hd (x : Elem) (Tr: Tree) (L : LT x Tr) : candidate x Tr (Some x).
Proof.
elim: Tr L=> [| l IHl x' r IHr L /=]; first by rewrite /= eqxx.
move: (LTC _ _ _ _ L)=> [x'x [Gl Gr]]. by rewrite x'x IHl.
Qed.

Lemma memberE_aux (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr = candidate x Tr None.
Proof.
elim: Tr BS=> [| l IHl x' r IHr BS /=]; first by [].
move: (TOC _ _ _ BS)=> [G [L [BSl BSr]]].
case: ltgtP.
- move=> xx'. by apply: IHl.
- move=> x'x. rewrite IHr; try by []. apply nhd_member; first by [].
  by rewrite neq_lt; apply/orP; right.
move=> eq. rewrite eq. by rewrite mem_in_hd.
Qed.

Theorem memberE (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr = member' x Tr.
Proof.
by rewrite memberE_aux.
Qed.

Fixpoint insert (x : Elem) (Tr : Tree) : Tree :=
match Tr with
| E => T E x E
| T a y b => if x < y then T (insert x a) y b else
               if x > y then T a y (insert x b) else T a y b
end.

Lemma member_LT (x x' : Elem) (Tr : Tree) : LT x Tr /\ (member x' Tr) -> x < x'.
Proof.
elim: Tr=> [|l IHl y r IHr /= [L M]]; first by elim.
move: (LTC _ _ _ _ L)=> [LEQ] [Ll] Lr. case: (ltgtP x' y).
- by move=> x'y; rewrite x'y in M; rewrite IHl.
- by move=> yx'; rewrite yx' in M; rewrite lt_gtF in M; rewrite ?IHr.
by move=> xy; rewrite -xy in LEQ.
Qed.

Lemma member_GT (x x' : Elem) (Tr : Tree) : GT x Tr /\ (member x' Tr) -> x > x'.
Proof.
elim: Tr=> [|l IHl y r IHr /= [G M]]; first by elim.
move: (GTC _ _ _ _ G)=> [GEQ] [Gl] Gr. case: (ltgtP x' y).
- by move=> x'y; rewrite x'y in M; rewrite IHl.
- by move=> yx'; rewrite yx' in M; rewrite lt_gtF in M; rewrite ?IHr.
by move=> xy; rewrite -xy in GEQ.
Qed.

Lemma insert_LT (x x' : Elem) (Tr : Tree) : LT x Tr /\ (x < x') -> LT x (insert x' Tr).
Proof.
elim: Tr=> [[L LEQ] | l IHl y r IHr /= [L M]]; first by [].
move: (LTC _ _ _ _ L)=> [LEQ] [Ll] Lr.
case: (ltgtP x' y); try by [].
- move=> x'y /=; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
  by apply: IHl.
- move=> yx' /=; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
  by apply: IHr.
Qed.

Lemma insert_GT (x x' : Elem) (Tr : Tree) : GT x Tr /\ (x > x') -> GT x (insert x' Tr).
Proof.
elim: Tr=> [[G GEQ] | l IHl y r IHr /= [G M]]; first by [].
move: (GTC _ _ _ _ G)=> [GEQ] [Gl] Gr.
case: (ltgtP x' y); try by [].
- move=> x'y /=; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
  by apply: IHl.
- move=> yx' /=; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
  by apply: IHr.
Qed.

Theorem BSTOrder_preserved (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : BSTOrder (insert x Tr).
Proof.
elim: Tr BS=> [| l IHl x' r IHr /andP[/andP[/andP[Gl Lr] BSl] BSr]] /=; first by [].
case: ltgtP.
- move=> xx' /=; try by [].
  apply/andP; split; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
  apply: insert_GT; split; by []. apply IHl. by apply BSl.
- move=> x'x /=; try by [].
  apply/andP; split; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
  apply: insert_LT; split; by []. apply IHr. by apply BSr.
move=> eq. rewrite -eq /=.
apply/andP; split; try by []. apply/andP; split; try by []. apply/andP; split; try by [].
by rewrite eq. by rewrite eq.
Qed.

End BinSearchTree.
End BST.
