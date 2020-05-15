From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path eqtype order.
Import Order.TTheory.
Open Scope order_scope.

Lemma orlastelim : forall a b, [ || a, b | true] = true.
Proof. by case; case. Qed.

Lemma orsndelim : forall a b, [ || a, true | b] = true.
Proof. by case; case. Qed.

Hint Resolve orlastelim orsndelim : core.

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

Lemma LEG (x x' : Elem) t : (x' <= x) && LT x t -> LT x' t.
Proof.
elim: t=> //= l IHl y r IHr /and4P[x'x ?? /(le_lt_trans x'x)->].
by rewrite IHl ?IHr // x'x.
Qed.

Lemma GTL (x x' : Elem) t : (x' >= x) && GT x t -> GT x' t.
Proof.
elim: t=> //= l IHl y r IHr /and4P[xx' ?? /lt_le_trans->] //.
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

Lemma nhd_member (x y : Elem) t :
  x != y -> candidate x t None = candidate x t (Some y).
Proof.
move=> neq_xy.
elim: t => /= [ | l IHl z r IHr]; first by rewrite (negbTE neq_xy).
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
by rewrite mem_cat in_cons is_member -IHl -IHr orbCA.
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

Fixpoint omin t :=
  if t is T l y r then
    if l is T l' x r' then
      omin l
    else if l is T E x r' then Some x
    else Some y
  else None.

Arguments omin : simpl nomatch.

Lemma nonemptymin t : t != E -> exists x, omin t = Some x.
Proof.
elim: t=> //= l IHl x r IHr _.
case: l IHl=> //= [* | l' y r' IHl]; first by exists x. by apply: IHl.
Qed.

Lemma minint t x : omin t = Some x -> x \in t.
Proof.
elim: t=> //= l IHl y r IHr min. rewrite is_member.
case: (l) IHl min=> /= [_ [->]| ??? IHl ?]; first by rewrite eq_refl.
by rewrite IHl.
Qed.

Lemma ismin t y (bst : BSTOrder t) :
  omin t = Some y -> forall x, x \in t -> y <= x.
Proof.
elim: t bst=> //= l IHl x r IHr /and4P[GTl LTr BSl BSr] min x'.
rewrite is_member=> /or3P[/eqP -> | x'l | x'r]; case eq: (l) IHl BSl min=> IHl BSl /=.
- by move=> [->].
- move=> min. apply: ltW. apply: member_GT; first by exact: BSl. by rewrite -eq. exact: minint.
- move=> [<-]. apply: ltW. apply: member_LT; first by exact: BSl. by []. by rewrite eq in x'l.
- move=> min. by rewrite IHl // -eq.
- move=> [<-]. apply: ltW. apply: member_LT; first by exact: BSr. by []. by [].
move=> min. rewrite -eq in min. rewrite -eq in BSl. move: (minint l y min)=> yl.
apply: ltW. apply: bstlr=> /=. apply/and4P. split; first by exact: GTl.
exact: LTr. by []. by []. by []. by [].
Qed.

Fixpoint treewithoutmin t :=
  if t is T l y r then
    if l is T l' x r' then
      T (treewithoutmin l) y r
    else r
  else E.

Arguments treewithoutmin : simpl nomatch.

Lemma hNleft l r x (bst : BSTOrder (T l x r)) : x \notin l.
Proof.
elim: l bst=> //= l' IHl' y r' IHr' /and4P[/and3P[???] ? /and4P[*]].
by rewrite is_member !negb_or gt_eqF ?IHl' ?IHr' //; apply/and4P; split.
Qed.

Lemma hNright l r x (bst : BSTOrder (T l x r)) : x \notin r.
Proof.
elim: r bst=> // l' IHl' y r' IHr' /= /and4P[] ? /and3P[] ???? /and4P[*].
by rewrite is_member !negb_or lt_eqF ?IHl' ?IHr' //=; apply/and4P; split.
Qed.

Lemma nomin t y (bst : BSTOrder t) : omin t = Some y -> y \notin (treewithoutmin t).
Proof.
elim: t bst=> //= l IHl x r IHr /and4P[GTl LTr BSl BSr] min.
case eq: (l) IHl BSl min=> [| l' x' r'] //.
- move=> _ _ /= [<-]. apply: hNright=> /=. apply/and4P.
  split; first by exact: GTl. by []. by rewrite eq. by [].
move=> IHl BSl min. rewrite is_member !negb_or.
have: y \in T l' x' r'.
- by rewrite minint.
move=> yl. apply/and3P. split.
- rewrite lt_eqF //. apply: member_GT. exact: BSl. by rewrite -eq. by [].
- by rewrite IHl.
apply: contra_eqN. move=> yr.
have: y != y.
- rewrite lt_eqF //. apply: bstlr=> /=. apply/and4P.
  split; first by exact: GTl. exact: LTr. by rewrite eq. by []. by rewrite eq. by [].
move=> yy. exact: yy. by [].
Qed.

Lemma stillinbst t x y (bst : BSTOrder t) :
  omin t = Some y -> x \in t -> x != y -> x \in (treewithoutmin t).
Proof.
elim: t bst=> //= l IHl x' r IHr /and4P[GTl LTr BSl BSr min].
rewrite is_member=> /or3P[/eqP xx' | xl | xr] /eqP neq_xy;
case eq: l IHl GTl BSl min=> [| l' y' r'] //=.
- move=> _ _ _ [x'y]. by move: x'y xx' neq_xy=>->->.
- move=> IHl GTl BSl min. by rewrite is_member xx' eq_refl.
- move=> _ _ _ _. by move: eq xl=>->.
- move=> IHl GTl BSl min. rewrite is_member IHl // -?eq //; by apply/eqP.
move=> IHl GTl BSl min. by rewrite is_member xr.
Qed.

Lemma wasinbst t x : x \in (treewithoutmin t) -> x \in t.
Proof.
elim: t=> // l IHl y r IHr xtt.
case: l IHl xtt=> /= [_ xr | l' x' r' IHl]; first by rewrite is_member xr.
rewrite is_member is_member=> /or3P[/eqP ->| xtl | ->] //; first by rewrite eq_refl.
by rewrite IHl.
Qed.

Lemma LTeq x t : LT x t <-> forall y, y \in t -> x < y.
Proof.
elim: t=> //= l IHl x' r IHr. split.
- move=> /and3P[LTl LTr xx'] y. rewrite is_member=> /or3P[/eqP -> // ||]; move: y; by rewrite -(IHl, IHr).
move=> H. apply/and3P. 
by split; rewrite (IHl, IHr, H) ?is_member ?eq_refl // => y yt; rewrite H ?is_member ?yt.
Qed.

Lemma GTeq x t : GT x t <-> forall y, y \in t -> x > y.
Proof.
elim: t=> //= l IHl x' r IHr. split.
- move=> /and3P[GTl GTr x'x] y. rewrite is_member=> /or3P[/eqP -> // ||]; move: y; by rewrite -(IHl, IHr).
move=> H. apply/and3P.
by split; rewrite (IHl, IHr, H) ?is_member ?eq_refl // => y yt; rewrite H ? is_member ?yt.
Qed.

Lemma stillbst t (bst : BSTOrder t) : BSTOrder (treewithoutmin t).
Proof.
elim: t bst=> //= l IHl x r IHr /and4P[GTl LTr BSl BSr].
case: (l) IHl BSl GTl=> //= l' y r' IHl BSl GTl. apply/and4P.
split; rewrite ?IHl ?GTeq //.
have: forall y' : Elem, y' \in (T l' y r') -> y' < x.
- by rewrite -GTeq.
by move=> H y' y't; rewrite H // wasinbst.
Qed.

Fixpoint delete x t :=
  if t is T l y r then
    if x < y then
      T (delete x l) y r
    else if x > y then
      T l y (delete x r)
    else
      if omin r is Some z then
        T l z (treewithoutmin r)
      else l
  else E.

Lemma LTnmem x t : LT x t -> x \notin t.
Proof.
elim: t=> //= l IHl y r IHr /and3P[LTl LTr xy].
by rewrite is_member !negb_or lt_eqF ?IHl ?IHr.
Qed.

Lemma GTnmem x t : GT x t -> x \notin t.
Proof.
elim: t=> //= l IHl y r IHr /and3P[GTl GTr yx].
by rewrite is_member !negb_or gt_eqF ?IHl ?IHr.
Qed.

Lemma deleted x t (bst : BSTOrder t) : x \notin (delete x t).
Proof.
elim tr: t bst=> [| l IHl y r IHr] //= /and4P[GTl LTr BSl BSr]. case: ltgtP=> xy;
rewrite ?is_member ?negb_or (IHl, IHr, xy) //=.
- rewrite lt_eqF //=.
  elim: (r) xy LTr=> //= l' IHl' x' r' IHr' xy /and3P[LTl' LTr' yx'].
  by rewrite is_member !negb_or (lt_eqF (lt_trans xy yx')) /= IHl' ?IHr'.
- rewrite gt_eqF //= andbT.
  elim: (l) xy GTl=> //= l' IHl' x' r' IHr' yx /and3P[GTl' GTe' x'y].
  by rewrite is_member !negb_or (gt_eqF (lt_trans x'y yx)) /= IHl' ?IHr'.
case eqr: (r)=> [| l' x' r'] //=; first by rewrite GTnmem.
have: exists m, omin (T l' x' r') = Some m.
- by apply: nonemptymin.
move=> [m min]. rewrite min -eqr is_member !negb_or.
have: m \in r. by rewrite minint // eqr.
move=> mr.
have: y < m. by move: LTeq LTr=> ->->.
 move=> ym. rewrite lt_eqF //=.
rewrite (hNleft l r) /=; last by apply/and4P; split.
rewrite (hNright l (treewithoutmin r)) //= GTl BSl /= stillbst // andbT LTeq=> y' y't.
move: (LTeq y r) LTr=> ->-> //. by rewrite wasinbst.
Qed.

Lemma reminbst x t y (bst : BSTOrder t): x \in t -> x != y -> x \in (delete y t).
Proof.
elim: t bst=> //= l IHl x' r IHr /and4P[GTl LTr BSl BSr].
case: ltgtP=> x'y; rewrite !is_member.
- by move=> /or3P[->| xl neq_xy |-> neq_xy] //; rewrite IHl.
- by move=> /or3P[->|-> neq_xy| xr neq_xy] //; rewrite IHr.
case eqr: (r)=> [| l' y' r'] //=.
- by move=> /or3P[/eqP->||] //; rewrite x'y eq_refl.
have: exists m, omin (T l' y' r') = Some m.
- by apply: nonemptymin.
move=> [m min]. rewrite min=> /or3P[/eqP->| xl neq_xy | xt neq_xy].
- by rewrite x'y eq_refl.
- by rewrite is_member xl.
rewrite is_member. case: ltgtP=> xm; last by [].
- by rewrite -eqr (stillinbst r x m) // ?eqr // lt_eqF.
by rewrite -eqr (stillinbst r x m) // ?eqr // gt_eqF.
Qed.

Lemma delwasinsbt x y t (bst : BSTOrder t) : x \in (delete y t) -> x \in t.
Proof.
elim: t bst=> //= l IHl x' r IHr /and4P[GTl LTr BSl BSr].
case: ltgtP=> x'y; rewrite !is_member.
- by move=> /or3P[->| xdl |->] //; rewrite IHl.
- by move=> /or3P[->|->| xdr] //; rewrite IHr.
case eq: (r)=> /= [| l' y' r']; first by move=> ->.
have: exists m, omin r = Some m.
- by apply: nonemptymin; rewrite eq.
move=> [m min].
rewrite -eq min is_member=> /or3P[/eqP -> |->| xtr] //; first by rewrite [m \in r]minint.
by rewrite [x \in r]wasinbst.
Qed.

Lemma abs_min x y t (bst: BSTOrder t) : omin t = Some y -> x \in (treewithoutmin t) -> y < x.
Proof.
elim: t bst=> //= l IHl x' r IHr /and4P[GTl LTr BSl BSr].
case eq: l IHl GTl BSl=> [| l' y' r'] IHl GTl BSl /=.
- move=> [<-] xr. by rewrite (member_LT x' x r).
move=> ?. rewrite is_member=> /or3P[/eqP ->| xtl | xr].
- by rewrite (member_GT x' y l) ?eq //; apply: minint.
- by rewrite IHl.
rewrite (bstlr l r x' y x) //= eq; first by apply/and4P; split.
by apply minint.
Qed.

Lemma delisbst x t (bst : BSTOrder t) : BSTOrder (delete x t).
Proof.
elim: t bst=> //= l IHl y r IHr /and4P[GTl LTr BSl BSr].
case: ltgtP=> xy /=.
- rewrite LTr BSr IHl //= andbT GTeq=> y' ydl.
  move: (GTeq y l) GTl=>->-> //. by rewrite (delwasinsbt y' x l).
- rewrite GTl BSl IHr //= andbT LTeq=> y' ydr.
  move: (LTeq y r) LTr=>->-> //. by rewrite (delwasinsbt y' x r).
case eq: (r)=> [| l' y' r'] //.
have: exists m, omin (T l' y' r') = Some m.
- by apply: nonemptymin.
move=> [m min]. rewrite min /= BSl stillbst //; last by rewrite -eq.
move=> /=. apply/and3P; split=> //.
- rewrite (GTL y m l) // GTl andbT.
  have: m \in r.
  - by apply: minint; rewrite eq.
  move=> mr. rewrite ltW //. move: (LTeq y r)=> [H1 H2]. by apply: H1.
rewrite LTeq=> z ytr. by rewrite (abs_min z m r) // eq.
Qed.

End BinSearchTree.
End BST.
