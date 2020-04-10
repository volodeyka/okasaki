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
move=> l IHl y r IHr /andP[/andP[/andP[Gl Lr] BSl] BSr]. case: ltgtP=> // xy.
by apply: IHl.
Qed.

Lemma mem_in_hd (x : Elem) (Tr: Tree) (L : LT x Tr) : candidate x Tr (Some x).
Proof.
elim: Tr L=> [| l IHl x' r IHr L /=]; first by rewrite /= eqxx.
move: (LTC _ _ _ _ L)=> [x'x [Gl Gr]]. by rewrite x'x IHl.
Qed.

Lemma memberE (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr = member' x Tr.
Proof.
rewrite/member'.
elim: Tr BS=> [| l IHl x' r IHr BS /=]; first by [].
move: (TOC _ _ _ BS)=> [G [L [BSl BSr]]].
case: ltgtP.
- move=> xx'. by apply: IHl.
- move=> x'x. rewrite IHr //. apply: nhd_member=> //.
  by rewrite neq_lt; apply/orP; right.
move=> eq. rewrite eq. by rewrite mem_in_hd.
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
case: (ltgtP x' y)=> //.
- move=> x'y //. apply/andP; split=> //. apply/andP; split=> //.
  by apply: IHl.
- move=> yx' //. apply/andP; split=> //. apply/andP; split=> //.
  by apply IHr.
Qed.

Lemma insert_GT (x x' : Elem) (Tr : Tree) : GT x Tr /\ (x > x') -> GT x (insert x' Tr).
Proof.
elim: Tr=> [[G GEQ] | l IHl y r IHr /= [G M]]; first by [].
move: (GTC _ _ _ _ G)=> [GEQ] [Gl] Gr.
case: (ltgtP x' y)=> //.
- move=> x'y //=. apply/andP; split=> //. apply/andP; split=> //.
  by apply: IHl.
- move=> yx' //=. apply/andP; split=> //. apply/andP; split=> //.
  by apply: IHr.
Qed.

Theorem BSTOrder_preserved (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : BSTOrder (insert x Tr).
Proof.
elim: Tr BS=> [| l IHl x' r IHr /andP[/andP[/andP[Gl Lr] BSl] BSr]] /=; first by [].
case: ltgtP.
- move=> xx' //=.
  apply/andP; split=> //. apply/andP; split=> //. apply/andP; split=> //.
  apply: insert_GT; split=> //. apply IHl. by apply BSl.
- move=> x'x //=.
  apply/andP; split=> //. apply/andP; split=> //. apply/andP; split=> //.
  apply: insert_LT; split; by []. apply IHr. by apply BSr.
move=> eq. rewrite -eq /=.
apply/andP; split=> //. apply/andP; split=> //. apply/andP; split=> //.
by rewrite eq. by rewrite eq.
Qed.

Fixpoint makelist (Tr : Tree) :=
match Tr with
| E => [::]
| T l x r => makelist l ++ x :: makelist r
end.

Fixpoint makelist_aux (Tr : Tree) (m : seq Elem) :=
match Tr with
| E => m
| T l x r => makelist_aux l (x :: makelist_aux r m)
end.

Definition makelist' (Tr : Tree) := makelist_aux Tr [::].

Lemma makelistE (Tr : Tree) (BS : BSTOrder Tr) : makelist Tr = makelist' Tr.
Proof.
have: (forall m, makelist_aux Tr m = makelist Tr ++ m).
- elim: Tr BS=> //= l IHl x r IHr /andP[/andP[/andP[GTl LTr] BSl] BSr] m.
  rewrite IHl; last by []. rewrite IHr; last by []. by rewrite -catA.
move=> aux. rewrite/makelist'. by rewrite aux cats0.
Qed.

Lemma list_of_tree_sorted (Tr : Tree) (BS : BSTOrder Tr) : sorted <=%O (makelist Tr).
Proof.
elim: Tr BS=> //= l IHl x r IHr /andP[/andP[/andP[GTl LTr] BSl] BSr].
have: (merge <=%O (makelist l) (x :: makelist r) = makelist l ++ x :: makelist r).
admit.
move=> aux. rewrite -aux. apply: merge_sorted=> //=; first by apply: le_total.
- by rewrite IHl.
rewrite path_sortedE; last by apply: le_trans.
apply/andP; split; last by rewrite IHr.
rewrite makelistE=> //.
elim: (r) LTr=> //= l' IHl' x' r' IHr' /andP[/andP[LTl' LTr'] lt].
have: (forall m, all (>= x) (makelist_aux l' m) = all (>= x) (makelist_aux l' [::] ++ m)).
- elim: (l') LTl'=> //= l'' IHl'' x'' r'' IHr'' /andP[/andP[LTl'' LTr''] xs] m.
  rewrite IHl''=> //. rewrite !all_cat !IHl''=> //=. rewrite !all_cat !IHr''=> //=.
  rewrite ltW=> //=. rewrite all_cat. rewrite Bool.andb_true_r.
  apply/andP/andP; first by move=> [H1 /andP[H2 H3]]; split=> //; apply/andP.
  by move=> [/andP[H1 H2] H3]; split=> //; apply/andP.
move=> aux'. rewrite/makelist'=> /=. rewrite aux'. rewrite all_cat.
apply/andP; split; first by apply IHl'=> /=. apply/andP; split; first by apply: ltW.
rewrite/all in IHr'. by rewrite IHr'.
Admitted.

Lemma mem_hVtr (x y : Elem) (Tr : Tree) (BS : BSTOrder Tr) :
  member x (insert y Tr) = (x == y) || (member x Tr).
Proof.
elim: Tr BS=> [_ | l IHl x' r IHr BS].
- case: ltgtP=> neq //=; first by rewrite neq.
  - by rewrite lt_gtF neq.
  by rewrite neq ltxx.
move=> /=. case: ltgtP=> x'y //=; case: ltgtP=> xx' //=;
move: (TOC _ _ _ BS)=> [G [L [BSl BSr]]].
- by apply: IHl.
- rewrite gt_eqF=> //; by rewrite (lt_trans x'y xx').
- by case: (x == y).
- rewrite lt_eqF=> //; by rewrite (lt_trans xx' x'y).
- by apply: IHr.
- by case: (x == y).
- rewrite lt_eqF=> //; by rewrite -x'y in xx'.
- rewrite gt_eqF=> //; by rewrite -x'y in xx'.
by case: (x == y).
Qed.

Lemma already_mem (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr -> insert x Tr = Tr.
Proof.
elim: Tr BS=> //= l IHl y r IHr /andP[/andP[/andP[GTl LTr] BSl] BSr].
case: ltgtP=> xy //=.
- move=> Mxl. by rewrite (IHl BSl Mxl).
move=> Mxr. by rewrite (IHr BSr Mxr).
Qed.

End BinSearchTree.
End BST.
