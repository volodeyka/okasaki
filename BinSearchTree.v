From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path eqtype order.
Import Order.TTheory.
Open Scope order_scope.

Lemma orlastelim : forall a b, [ || a, b | true] = true.
Proof. by case; case. Qed.

Lemma orsndelim : forall a b, [ || a, true | b] = true.
Proof. by case; case. Qed.

Lemma swap : forall a b c, [ || a, b | c] = [ || b, a | c].
Proof. by case; case; case. Qed.

Hint Resolve orlastelim orsndelim swap : core.

Module BST.
Section BinSearchTree.
Notation ordType := (orderType tt).
Variable Elem : ordType.

Inductive Tree := E | T : Tree -> Elem -> Tree -> Tree.

Definition EmptyTree := E.

Implicit Type t : Tree.

(* equality *)
Fixpoint eqtree t1 t2 :=
match t1, t2 with
| E, E => true
| T l1 x1 r1, T l2 x2 r2 => [&& (x1 == x2), eqtree l1 l2 & eqtree r1 r2]
| _, _ => false
end.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
elim=> [|? IHl ?? IHr] /= [] *; try by constructor.
by apply: (iffP idP)=> [/and3P[/eqP-> /IHl-> /IHr->]|[/IHl-> /eqP-> /IHr->]].
Qed.
Canonical tree_eqMixin := EqMixin eqtreeP.
Canonical tree_eqType := Eval hnf in EqType Tree tree_eqMixin.

Lemma eqtreeE : eqtree = eq_op.
Proof. by []. Qed.

(* membership predicat *)
Fixpoint mem_tree t :=
  if t is T l x r then xpredU1 x (xpredU (mem_tree l) (mem_tree r)) else xpred0.

Definition tree_eqclass := Tree.
Identity Coercion tree_of_eqclass : tree_eqclass >-> Tree.
Coercion pred_of_tree (t : tree_eqclass) : {pred Elem} := mem_tree t.
Canonical tree_predType := PredType pred_of_tree.
(* The line below makes mem_seq a canonical instance of topred. *)
Canonical mem_seq_predType := PredType mem_tree.


Fixpoint LT (x : Elem) t : bool :=
  if t is T l y r then [&& LT x l, LT x r & (x < y)] else true.

Fixpoint GT (x : Elem) t : bool :=
  if t is T l y r then [&& GT x l, GT x r & (x > y)] else true.

Fixpoint BSTOrder t : bool :=
  if t is T l x r then [&& GT x l, LT x r, BSTOrder l & BSTOrder r] else true.

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

Lemma LEG (x x' : Elem) t : (x' < x) && LT x t -> LT x' t.
Proof.
elim: t=> //= l IHl y r IHr /and4P[x'x ?? /(lt_trans x'x)->].
by rewrite IHl ?IHr // x'x.
Qed.

Lemma GTL (x x' : Elem) t : (x' > x) && GT x t -> GT x' t.
Proof.
elim: t=> //= l IHl y r IHr /and4P[xx' ?? /lt_trans->] //.
by rewrite IHl ?IHr // xx'.
Qed.

Lemma is_member x l y r : x \in T l y r = [|| x == y, x \in l | x \in r].
Proof. by []. Qed.

Lemma is_left l r (x y : Elem) (bst : BSTOrder (T l y r)) :
  x < y -> x \in T l y r = (x \in l).
Proof.
move=> xy. rewrite is_member. apply/or3P. move: bst=> /= /and4P[? L ??].
case: ifP=> ->; first by apply/or3P.
apply/or3P=> /=. rewrite negb_or. apply/andP; split; first by rewrite lt_eqF.
elim: (r) L=> //= l' IHl' x' r' IHr' /and3P[LTl' LTr' yx'].
by rewrite is_member !negb_or (lt_eqF (lt_trans xy yx')) ?IHl' ?IHr'.
Qed.

Lemma is_right l r (x y : Elem) (bst : BSTOrder (T l y r)) :
  x > y -> x \in T l y r = (x \in r).
Proof.
move=> yx. rewrite is_member. apply/or3P. move: bst=> /= /and4P[G ???].
case: ifP=> ->; first by apply/or3P.
apply/or3P. rewrite !negb_or /=. apply/and3P; split=> //; first by rewrite gt_eqF.
elim: (l) G=> //= l' IHl' x' r' IHr' /and3P[GTl' GTr' x'y].
by rewrite is_member !negb_or (gt_eqF (lt_trans x'y yx)) ?IHl' ?IHr'.
Qed.

(** member function with at most d + 1 comparisons where d is the depth of a tree*)
Fixpoint candidate (x : Elem) t (cand : option Elem) : bool :=
  if t is T l y r then
    if x < y then candidate x l cand
    else candidate x r (Some y)
  else if cand is Some c then x == c
       else false.

Definition member' (x : Elem) t : bool := candidate x t None.

Lemma nhd_member (x y : Elem) t (bst : BSTOrder t) :
  x != y -> candidate x t None = candidate x t (Some y).
Proof.
move=> neq_xy.
elim: t bst=> /= [_ | l IHl z r IHr /and4P[*]]; first by rewrite (negbTE neq_xy).
case: ltgtP=> // xy; by apply: IHl.
Qed.

Lemma mem_in_hd (x : Elem) t (L : LT x t) :
  candidate x t (Some x).
Proof.
elim: t L=> /= [| ? IHl ??? /and3P[?? xx']]; first by rewrite /= eqxx.
by rewrite xx' IHl.
Qed.

Lemma memberE (x : Elem) t (bst : BSTOrder t) : x \in t = member' x t.
Proof.
rewrite/member'.
elim: t bst=> //= ? IHl ? ? IHr bst.
move: (TOC _ _ _ bst)=> /and4P[*]. case: ltgtP.
- move=> *. rewrite is_left //. by apply: IHl.
- move=> *. rewrite is_right // IHr //; apply: nhd_member=> //. by rewrite gt_eqF.
move=> ->; rewrite mem_in_hd // is_member eq_refl //.
Qed.

Fixpoint insert (x : Elem) t :=
  if t is T a y b then
    if x < y then T (insert x a) y b
    else if x > y then T a y (insert x b)
    else T a y b
  else T E x E.

Lemma member_LT (x x' : Elem) t (bst : BSTOrder t) : LT x t -> (x' \in t) -> x < x'.
Proof.
elim: t bst=> // ? IHl y ? IHr bst /and3P[?? xy] M. case: (ltgtP x' y);
move: (TOC _ _ _ bst)=> /and4P[????].
- by move=> x'y; rewrite is_left in M=> //; rewrite IHl.
- by move=> yx'; rewrite is_right in M=> //; rewrite IHr.
by move=> x'y; rewrite -x'y in xy.
Qed.

Lemma member_GT (x x' : Elem) t (bst : BSTOrder t) : GT x t -> (x' \in t) -> x > x'.
Proof.
elim: t bst=> //= ? IHl y ? IHr bst /and3P[?? yx] M. case: (ltgtP x' y);
move: (TOC _ _ _ bst)=> /and4P[????].
- by move=> x'y; rewrite is_left in M=> //; rewrite IHl.
- by move=> yx'; rewrite is_right in M; rewrite ?IHr.
by move=> x'y; rewrite -x'y in yx.
Qed.

Lemma insert_LT (x x' : Elem) t : LT x t -> (x < x') -> LT x (insert x' t).
Proof.
elim: t=> //= ? IHl y ? IHr /and3P[LTl LTr xy] xx'.
by case: (ltgtP x' y); move=> xy' /=; rewrite ?IHl ?IHr ?LTl ?LTr ?xy'.
Qed.

Lemma insert_GT (x x' : Elem) t : GT x t -> (x > x') -> GT x (insert x' t).
Proof.
elim: t=> //= ? IHl y ? IHr /and3P[GTl GTr yx] x'x.
by case: (ltgtP x' y); move=> xy' /=; rewrite ?IHl ?IHr ?GTl ?GTr ?xy'.
Qed.

Theorem BSTOrder_preserved (x : Elem) t (bst : BSTOrder t) : BSTOrder (insert x t).
Proof.
elim: t bst=> //= l IHl x' r IHr /and4P[]. by case: ltgtP; last (by move=><- /=->->->->);
move=> /= ? G L BSl BSr; rewrite (insert_GT, insert_LT) // (IHl, IHr) // (L, G) (BSr, BSl).
Qed.

Fixpoint makelist t :=
  if t is T l x r then
    makelist l ++ x :: makelist r
  else [::].

Fixpoint makelist_aux t (m : seq Elem) :=
  if t is T l x r then
    makelist_aux l (x :: makelist_aux r m)
  else m.

Definition makelist' t := makelist_aux t [::].

Lemma makelistE t : makelist t = makelist' t.
Proof.
have: (forall m, makelist_aux t m = makelist t ++ m).
- elim: t=> //= l IHl x r IHr m.
  by rewrite IHl // IHr // -catA.
move=> aux. rewrite/makelist'. by rewrite aux cats0.
Qed.

Lemma inlist t (x : Elem) :
  (x \in makelist t) = (x \in t).
Proof.
elim: t=> //= l IHl y r IHr.
by rewrite mem_cat in_cons is_member -IHl -IHr.
Qed.

Lemma bstlr l r (x a b : Elem) : BSTOrder (T l x r) -> a \in l -> b \in r -> a < b.
Proof.
move=> /= /and4P[GTl LTr BSl BSr] al br.
have: x < b.
- apply: member_LT; first by exact: BSr. exact: LTr. exact: br.
have: a < x. 
- apply: member_GT; first by exact: BSl. exact: GTl. exact: al.
move=> /lt_trans; apply.
Qed.

Lemma mlistlr l r (x a b : Elem) :
  BSTOrder (T l x r) -> a \in makelist l -> b \in makelist r -> a < b.
Proof.
move=> BS. rewrite !inlist.
apply: bstlr. exact: BS.
Qed.

Lemma list_of_tree_sorted t (bst : BSTOrder t) :
  sorted <=%O (makelist t).
Proof.
elim: t bst=> //= l IHl x r IHr /and4P[GTl LTr BSl BSr].
move: (IHl BSl) (IHr BSr)=> Sl Sr.
have: sorted <=%O (x :: makelist r).
- rewrite /= path_sortedE; last by apply: le_trans. apply/andP. split; last by [].
  elim: (r) LTr=> //= l' IHl' y r' IHr' /and3P[LTl' LTr' xy].
  rewrite all_cat IHl' //= IHr' ?ltW //.
move=> /= Sxr.
case E: (makelist l)=> [// |y l']. move: (Sl).
rewrite E cat_cons /= cat_path=> -> /=.
have: (last y l') \in makelist l.
- rewrite E. apply: mem_last.
rewrite inlist=> lyl. apply/andP. split.
- apply: ltW. apply: member_GT. exact: BSl. exact: GTl. exact: lyl.
exact: Sxr.
Qed.

Lemma mem_hVtr (x y : Elem) t (bst : BSTOrder t) :
  x \in (insert y t) = (x == y) || (x \in t).
Proof.
elim: t bst=> [_ | l IHl x' r IHr bst].
- case: ltgtP=> neq //=; rewrite !is_member /=; first by rewrite lt_eqF.
  - by rewrite gt_eqF.
  by rewrite neq eq_refl.
case: ltgtP=> xy /=; case: ltgtP=> x'y; rewrite !is_member //=;
move: (TOC _ _ _ bst)=> /and4P[*];
by rewrite ?IHl ?IHr ?(lt_eqF xy) ?(gt_eqF xy) // xy ?x'y ?eq_refl.
Qed.

Lemma already_mem (x : Elem) t (bst : BSTOrder t) :
  x \in t -> insert x t = t.
Proof.
elim: t bst=> //= l IHl y r IHr /and4P[GTl LTr BSl BSr]. case: ltgtP=> xy //= xint;
rewrite (IHl BSl, IHr BSr) // -(is_left l r x y, is_right l r x y) //; by apply/and4P.
Qed.

Fixpoint insert_aux (x : Elem) t : option Tree :=
  if t is T l y r then
    if x < y then
      if insert_aux x l is Some l' then
        Some (T l' y r)
      else None
    else if x > y then
           if insert_aux x r is Some r' then
             Some (T l y r')
           else None
         else
           Some (T l y r)
  else
    Some (T E x E).

Definition insert' (x : Elem) t :=
  if insert_aux x t is Some t then t else E.

Lemma insertE (x : Elem) t : insert x t = insert' x t.
Proof.
have: Some (insert x t) = insert_aux x t.
- elim: t=> //= l IHl y r IHr. by case: ltgtP=> //; rewrite -(IHl, IHr).
rewrite/insert'. by move=> <-.
Qed.

End BinSearchTree.
End BST.
