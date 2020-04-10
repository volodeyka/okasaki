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
if Tr is T l y r then [&& LT x l, LT x r & (x < y)] else true.

Fixpoint GT (x : Elem) (Tr : Tree) : bool :=
if Tr is T l y r then [&& GT x l, GT x r & (x > y)] else true.

Fixpoint BSTOrder (Tr : Tree) : bool :=
if Tr is T l x r then [&& GT x l, LT x r, BSTOrder l & BSTOrder r] else true.

Lemma TOC l x r :
BSTOrder (T l x r) ->
[&& GT x l, LT x r, (BSTOrder l) & (BSTOrder r)].
Proof. by []. Qed.

Lemma LTC x l y r :
LT x (T l y r) ->
[&& LT x l, LT x r & (x < y)].
Proof. by []. Qed.

Lemma GTC x l y r :
GT x (T l y r) ->
[&& GT x l, GT x r & (x > y)].
Proof. by []. Qed.

Lemma LEG (x x' : Elem) (Tr : Tree) : (x' < x) && LT x Tr -> LT x' Tr.
Proof.
elim: Tr=> //= l IHl y r IHr /and4P[x'x LTl LTr xy].
apply/and3P; split.
- apply: IHl; by apply/andP.
- apply: IHr; by apply/andP.
by apply: (lt_trans x'x xy).
Qed.

Lemma GTL (x x' : Elem) (Tr : Tree) : (x' > x) && GT x Tr -> GT x' Tr.
Proof.
elim: Tr=> //= l IHl y r IHr /and4P[xx' GTl GTr yx].
apply/and3P; split.
- apply: IHl; by apply/andP.
- apply: IHr; by apply/andP.
by apply: (lt_trans yx xx').
Qed.

Fixpoint member (x : Elem) (Tr : Tree) : bool :=
if Tr is T l y r then
  if x < y then member x l
  else if x > y then member x r else true 
else false.

(** member function with at most d + 1 comparisons where d is the depth of a tree*)
Fixpoint candidate (x : Elem) (Tr : Tree) (cand : option Elem) : bool :=
if Tr is T l y r then
  if x < y then candidate x l cand
  else candidate x r (Some y)
else if cand is Some c then
       if x == c then true else false
     else false.

Definition member' (x : Elem) (Tr : Tree) : bool := candidate x Tr None.

Lemma nhd_member (x x' : Elem) (Tr : Tree) (BS : BSTOrder Tr) (NEQ : x != x') :
      candidate x Tr None = candidate x Tr (Some x').
Proof.
elim: Tr BS=> /= [| l IHl y r IHr /and4P[GTl GTr BSl BSr]]; first by rewrite ifN_eq.
case: ltgtP=> // xy; by apply: IHl.
Qed.

Lemma mem_in_hd (x : Elem) (Tr: Tree) (L : LT x Tr) : candidate x Tr (Some x).
Proof.
elim: Tr L=> [| l IHl x' r IHr L /=]; first by rewrite /= eqxx.
move: (LTC _ _ _ _ L)=> /and3P [LTl LTr xx']; by rewrite xx' IHl.
Qed.

Lemma memberE (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr = member' x Tr.
Proof.
rewrite/member'.
elim: Tr BS=> //= l IHl x' r IHr BS.
move: (TOC _ _ _ BS)=> /and4P[G L BSl BSr]. case: ltgtP.
- move=> xx'; by apply: IHl.
- move=> x'x; rewrite IHr //; apply: nhd_member=> //.
  by rewrite neq_lt; apply/orP; right.
move=> eq; by rewrite eq mem_in_hd.
Qed.

Fixpoint insert (x : Elem) (Tr : Tree) : Tree :=
if Tr is T a y b then
  if x < y then T (insert x a) y b
  else if x > y then T a y (insert x b)
  else T a y b
else T E x E.

Lemma member_LT (x x' : Elem) (Tr : Tree) : LT x Tr && (member x' Tr) -> x < x'.
Proof.
elim: Tr=> //= l IHl y r IHr /andP[/and3P[LTl LTr xy] M]. case: (ltgtP x' y).
- by move=> x'y; rewrite x'y in M; rewrite IHl //; apply/andP.
- by move=> yx'; rewrite yx' in M; rewrite lt_gtF in M; rewrite ?IHr //; apply/andP.
by move=> x'y; rewrite -x'y in xy.
Qed.

Lemma member_GT (x x' : Elem) (Tr : Tree) : GT x Tr && (member x' Tr) -> x > x'.
Proof.
elim: Tr=> //= l IHl y r IHr /andP[/and3P[GTl GTr yx] M]. case: (ltgtP x' y).
- by move=> x'y; rewrite x'y in M; rewrite IHl //; apply/andP.
- by move=> yx'; rewrite yx' in M; rewrite lt_gtF in M; rewrite ?IHr //; apply/andP.
by move=> x'y; rewrite -x'y in yx.
Qed.

Lemma insert_LT (x x' : Elem) (Tr : Tree) : LT x Tr && (x < x') -> LT x (insert x' Tr).
Proof.
elim: Tr=> //= l IHl y r IHr /andP[/and3P[LTl LTr xy] xx']. case: (ltgtP x' y).
- by move=> x'y //; apply/and3P; split=> //; apply: IHl; apply/andP.
- by move=> yx' //; apply/and3P; split=> //; apply: IHr; apply/andP.
by move=> eq /=; apply/and3P.
Qed.

Lemma insert_GT (x x' : Elem) (Tr : Tree) : GT x Tr && (x > x') -> GT x (insert x' Tr).
Proof.
elim: Tr=> //= l IHl y r IHr /andP[/and3P[GTl GTr yx] x'x]. case: (ltgtP x' y).
- by move=> x'y //; apply/and3P; split=> //; apply: IHl; apply/andP.
- by move=> yx' //; apply/and3P; split=> //; apply: IHr; apply/andP.
by move=> eq /=; apply/and3P.
Qed.

Theorem BSTOrder_preserved (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : BSTOrder (insert x Tr).
Proof.
elim: Tr BS=> //= l IHl x' r IHr /and4P[Gl Lr BSl BSr]. case: ltgtP.
- move=> xx' //=; apply/and4P; split=> //=. apply insert_GT; by apply/andP. by apply IHl.
- move=> x'x //=; apply/and4P; split=> //=. apply insert_LT; by apply/andP. by apply IHr.
move=> eq; rewrite -eq /=; apply/and4P; split=> //; by rewrite eq.
Qed.

Fixpoint makelist (Tr : Tree) :=
if Tr is T l x r then
  makelist l ++ x :: makelist r
else [::].

Fixpoint makelist_aux (Tr : Tree) (m : seq Elem) :=
if Tr is T l x r then
  makelist_aux l (x :: makelist_aux r m)
else m.

Definition makelist' (Tr : Tree) := makelist_aux Tr [::].

Lemma makelistE (Tr : Tree) (BS : BSTOrder Tr) : makelist Tr = makelist' Tr.
Proof.
have: (forall m, makelist_aux Tr m = makelist Tr ++ m).
- elim: Tr BS=> //= l IHl x r IHr /and4P[GTl LTr BSl BSr] m.
  by rewrite IHl // IHr // -catA.
move=> aux. rewrite/makelist'. by rewrite aux cats0.
Qed.

Lemma list_of_tree_sorted (Tr : Tree) (BS : BSTOrder Tr) : sorted <=%O (makelist Tr).
Proof.
elim: Tr BS=> //= l IHl x r IHr /and4P[GTl LTr BSl BSr].
have: (merge <=%O (makelist l) (x :: makelist r) = makelist l ++ x :: makelist r).
admit.
move=> aux; rewrite -aux. apply: merge_sorted=> //=; first by apply: le_total.
- by rewrite IHl.
rewrite path_sortedE; last by apply: le_trans.
apply/andP; split; last by rewrite IHr.
rewrite makelistE //.
elim: (r) LTr=> //= l' IHl' x' r' IHr' /and3P[LTl' LTr' lt].
have: (forall m, all (>= x) (makelist_aux l' m) = all (>= x) (makelist_aux l' [::] ++ m)).
- elim: (l') LTl'=> //= l'' IHl'' x'' r'' IHr'' /and3P[LTl'' LTr'' xs] m.
  rewrite IHl'' // !all_cat !IHl'' //=  !all_cat !IHr'' //= ltW //= all_cat Bool.andb_true_r.
  apply/andP/andP; first by move=> [H1 /andP[H2 H3]]; split=> //; apply/andP.
  by move=> [/andP[H1 H2] H3]; split=> //; apply/andP.
move=> aux'. rewrite/makelist' /= aux' all_cat.
apply/andP; split; first by apply: IHl'=> /=. apply/andP; split; first by apply: ltW.
rewrite/all in IHr'; by rewrite IHr'.
Admitted.

Lemma mem_hVtr (x y : Elem) (Tr : Tree) (BS : BSTOrder Tr) :
  member x (insert y Tr) = (x == y) || (member x Tr).
Proof.
elim: Tr BS=> [_ | l IHl x' r IHr BS].
- case: ltgtP=> neq //=; first by rewrite neq.
  - by rewrite lt_gtF neq.
  by rewrite neq ltxx.
move=> /=. 
case: ltgtP=> x'y //=; case: ltgtP=> xx' //=; move: (TOC _ _ _ BS)=> /and4P[G L BSl BSr];
by [apply: IHl | rewrite gt_eqF // (lt_trans x'y xx') | case: (x == y) |
 rewrite lt_eqF // (lt_trans xx' x'y) | apply: IHr | case: (x == y) |
 rewrite lt_eqF //; rewrite -x'y in xx' | rewrite gt_eqF //; rewrite -x'y in xx' |
 case: (x == y)].
Qed.

Lemma already_mem (x : Elem) (Tr : Tree) (BS : BSTOrder Tr) : member x Tr -> insert x Tr = Tr.
Proof.
elim: Tr BS=> //= l IHl y r IHr /and4P[GTl LTr BSl BSr]. case: ltgtP=> xy //=.
- move=> Mxl. by rewrite (IHl BSl Mxl).
move=> Mxr. by rewrite (IHr BSr Mxr).
Qed.

End BinSearchTree.
End BST.
