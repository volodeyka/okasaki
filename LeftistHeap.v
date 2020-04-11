From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype. 
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).
Import Order.NatOrder.

Open Scope order_scope.

Lemma snd_true a b : a || true || b.
Proof.
by case: a.
Qed.

Lemma trd_true a b : b || a || true.
Proof.
by case: a; case b.
Qed.
Hint Resolve trd_true snd_true lexx : core.


Module leftistheap.
(*Leftist heaps are heap-ordered binary trees that satisfy the
leftist property: the rank of any left child is at least as large as the rank of its
right sibling. The rank of a node is defined to be the length of its right spine
(i.e., the rightmost path from the node in question to an empty node). A simple
consequence of the leftist property is that the right spine of any node is always
the shortest path to an empty node.*)
Section LeftistDef.
Variables (T: ordType).

Inductive heap :=
| Emp : heap
| Node : nat -> T-> heap -> heap -> heap.

End LeftistDef.
Arguments Node {T}.
Arguments Emp {T}.
Notation "[ tl | n , x | tr ]" := (Node n x tl tr) (at level 0).
Notation "'[|,|]'" := Emp (at level 200).

Module Measure.
Structure mixin_of {T : ordType} (measure : heap T -> nat) :=
  Mixin {
    measure1            : nat;
    f                   : nat -> nat -> nat;
    measureNode         : forall tl tr n x, measure [tl| x, n |tr] = f (measure tl) (measure tr);
    measure_NodexEE     : f (measure ([|,|])) (measure ([|,|])) = measure1;
    measure_Node_E      : forall h1 h2 n x, (measure ([|,|]) < measure [h1 | n, x | h2])%N
  }.

Notation class_of := mixin_of (only parsing).

Section classdef.

Structure type T := Pack { sort; _ : @class_of T sort }.

Local Coercion sort : type >-> Funclass.

Variables (T : ordType) (cT : (type T)).

(** Projection out of [type] *)
Definition class :=
  let: Pack _ c := cT return class_of cT in c.

End classdef.
Module Exports.

Coercion sort : type >-> Funclass.
(** Some shorthands *)
Notation measureType := type.

Notation MeasureMixin := Mixin.

End Exports.
End Measure.

Section Specifications.
Export Measure.Exports.
Variables (T : ordType).
Implicit Type h : heap T.

Fixpoint eqheap h1 h2 :=
  match h1, h2 with
  | Emp, Emp => true
  | Node n1 x1 tl1 tr1, Node n2 x2 tl2 tr2 => [&& (n1 == n2), (x1 == x2), eqheap tl1 tl2 & eqheap tr1 tr2]
  | _, _ => false
  end.

Lemma eqheapP : Equality.axiom eqheap.
Proof.
elim=> [|n x tl IHh1 tr IHh2] [|m y h1 h2] /=; try by constructor.
by apply: (iffP and4P); case=> [/eqP-> /eqP-> /IHh1-> /IHh2->].
Qed.

Canonical heap_eqMixin := EqMixin eqheapP.
Canonical heap_eqType := Eval hnf in EqType (heap T) heap_eqMixin.

Lemma eqheapE : eqheap = eq_op. Proof. by []. Qed.

Lemma eqheap_Node (x1 x2 : T) n1 n2 tr1 tr2 tl1 tl2 :
  ([tl1 | n1, x1 | tr1] == [tl2 | n2, x2 | tr2]) = [&& (n1 == n2), (x1 == x2), eqheap tl1 tl2 & eqheap tr1 tr2].
Proof. by []. Qed.

Lemma eqNode1xEE x y: ([[|,|]| 1, x |[|,|]] == [[|,|] | 1, y |[|,|]]) = (x == y).
Proof.
by rewrite eqheap_Node !eq_refl; case (x == y).
Qed.

Fixpoint mem_heap h :=
  if h is Node _ y tl tr then xpredU1 y (xpredU (mem_heap tl) (mem_heap tr)) else xpred0.

Definition heap_eqclass := heap T.
Identity Coercion heap_of_eqclass : heap_eqclass >-> heap.
Coercion pred_of_heap (h : heap_eqclass) : {pred T} := mem_heap h.

Canonical heap_predType := PredType pred_of_heap.
(* The line below makes mem_seq a canonical instance of topred. *)
Canonical mem_seq_predType := PredType mem_heap.

Lemma in_Node x y n tl tr: 
  x \in [tl | n, y | tr] = [|| x == y, x \in tl | x \in tr].
Proof. by []. Qed.

Section Conut.
Variables a : pred T.

Fixpoint count h : nat := if h is [tl| _, x |tr] then a x + count
 tl + count tr else 0.

Lemma count_Node tl tr y n: count [tl| n, y |tr] = a y + count tl + count tr.
Proof. by []. Qed.

Lemma count_E : count ([|,|]) = 0.
Proof. by []. Qed.

Lemma count_NodexEE n y : count [[|,|]| n, y |[|,|]] = a y.
Proof. move=> /=. by rewrite !addn0. Qed.

Let countE := (count_Node, count_E, count_NodexEE).
End Conut.

Lemma in_count x h: x \in h = (0 < count (xpred1 x) h)%N.
Proof.
elim h=> // n y h1 IHh1 h2 IHh2; rewrite in_Node /= !addn_gt0 IHh1 IHh2 eq_sym; by case: (y == x).
Qed.


Definition empty h :=
if h is Emp then true else false.

Theorem emptyP h : reflect (h = Emp) (empty h).
Proof. case h; by constructor. Qed.

Definition LE x h : bool := 
if h is Node n y a b then (x <= y) else true.

Section Measure.
Variables measure : measureType T.
Definition measure1 : nat := Measure.measure1 _ (Measure.class T measure).
Definition measure_NodexEE := Measure.measure_NodexEE _ (Measure.class T measure).
Definition measureNode := Measure.measureNode _ (Measure.class T measure).
Definition measure_Node_E := Measure.measure_Node_E _ (Measure.class T measure).
Definition f := Measure.f _ (Measure.class T measure).
Hint Resolve measure_Node_E : core.

Fixpoint measure_inv h : bool :=
match h with
| [tl| n, x |tr] => [&& (n == measure h), (measure_inv tl) & (measure_inv tr)]
| [|,|]            => true
end.

Lemma measure_inv_NodexEE x : measure_inv [[|,|]| measure1, x |[|,|]].
Proof.
  move=> /=. by rewrite measureNode measure_NodexEE eq_refl.
Qed.
Hint Resolve measure_inv_NodexEE : core.

Fixpoint heap_ordered h : bool :=
if h is Node n x tl tr then
  [&& (LE x tl), (LE x tr), (heap_ordered tl) & (heap_ordered tr)]
else true.

Fact heap_ordered_NodexEE n x : heap_ordered [[|,|]| n, x | [|,|]].
Proof. by []. Qed.
Hint Resolve heap_ordered_NodexEE: core.
Fact heap_ordered_E : heap_ordered ([|,|]). Proof. by []. Qed.

Fact measure_E : measure_inv ([|,|]). Proof. by []. Qed.

Fixpoint leftist_inv h : bool :=
if h is Node n x tl tr then
  [&& (measure tr <= measure tl)%N, (leftist_inv tl) & (leftist_inv tr)]
else true.

Fact leftist_inv_NodexEE n x : leftist_inv [[|,|]| n, x | [|,|]].
Proof. move=> /=; by rewrite leqnn. Qed.
Hint Resolve leftist_inv_NodexEE : core.

Fact leftist_inv_E : leftist_inv ([|,|]). Proof. by []. Qed.

Variant side := r | l.

Definition spine := seq side.

Fixpoint spine_in p h : bool :=
match p, h with
| r :: p, Node _ _ _ tr => spine_in p tr
| l :: p, Node _ _ tl _ => spine_in p tl
| [::],   Emp          => true
| _,      _          => false
end.

Fixpoint Right p : bool :=
match p with
| r :: p' => Right p'
| l :: _  => false
| [::]    => true
end.

Lemma rigth_correct : forall x s, Right (x :: s) -> ((x = r) * Right s).
Proof. move=> [] //=. Qed.

Lemma case_spine_in : forall side s n x tl tr, 
spine_in (side :: s) (Node n x tl tr) -> 
if side is r then spine_in s tr else spine_in s tl.
Proof. move=> [] //=. Qed.

Definition leftist_measure_inv h := leftist_inv h && measure_inv h.

Lemma case_leftist_measure_inv_r n x tl tr :
leftist_measure_inv (Node n x tl tr) -> leftist_measure_inv tr.
Proof.
by rewrite /leftist_measure_inv /= => /and3P[/and3P[_ _ -> _ /andP[]]].
Qed.

Lemma case_leftist_measure_inv_rl n x tl tr:
leftist_measure_inv (Node n x tl tr) -> 
[&& leftist_measure_inv tr, leftist_measure_inv tl & (measure tr <= measure tl)%N].
Proof.
by rewrite /leftist_measure_inv => /andP[] /= => /and3P[->->-> /and3P[_ ->->]].
Qed.

Lemma case_measure_inv n y h1 h2 : 
measure_inv (Node n y h1 h2) -> [&& (n == f (measure h1) (measure h2)), (measure_inv h1) & (measure_inv h2)].
Proof. move=> /=; by rewrite measureNode. Qed.

Lemma case_leftist_measure_inv n x tl tr: 
leftist_measure_inv (Node n x tl tr) -> (n == f (measure tl) (measure tr)) &&
[&& leftist_measure_inv tr, leftist_measure_inv tl & (measure tr <= measure tl)%N].
Proof.
move=> LI. move: LI (LI)=> /case_leftist_measure_inv_rl -> /andP[_] /= /and3P[]; 
by rewrite measureNode=>->.
Qed.

Lemma case_heap_ordered n y h1 h2 : 
heap_ordered (Node n y h1 h2) ->
[&& LE y h1, LE y h2, (heap_ordered h1) & (heap_ordered h2)].
Proof. by []. Qed.      


Ltac merge_cases := match goal with 
| H : (?x <= ?y) = true |- _ => move: (H)=> /= ->; rewrite ?H
| H : (?x <= ?y) = false |- _ => move: (H)=> /merge_a /= ->; rewrite ?H
end. 

Ltac merge_casesxy x y := case H : (x <= y); merge_cases.
Lemma swap_tact {A B C} : (A -> B -> C) -> (B -> A -> C).
Proof.
move=> H b /H; by apply.
Qed.

Ltac swapg := apply swap_tact.

Lemma case_leftist_inv n y h1 h2 : 
leftist_inv (Node n y h1 h2) -> [&& (measure h2 <= measure h1)%N, leftist_inv h1 & leftist_inv h2].
Proof. by []. Qed.

Lemma right_spine_ex : forall h, exists s, Right s && spine_in s h.
Proof.
elim=> [|n s hl _ hr [] s'].
- by exists nil.
by exists (r :: s').
Qed.

Lemma spine_in_E s : spine_in s Emp -> s = [::].
Proof. by case: s=> [|[]] //=. Qed.

Definition makeT (x : T) h1 h2 :=
let m1 := measure h1 in
  let m2 := measure h2 in
      if (m2 <= m1)%N then [h1| f m1 m2, x |h2] else [h2| f m2 m1, x |h1] .

Ltac makeT_cases := match goal with
| H : (?a <= ?b)%N = _ |- _ => rewrite /makeT; move : H => /= ->
end.

Ltac makeT_casesxy x y := case fresh : (x <= y)%N; makeT_cases.

Lemma makeT_preserves_LI_inv x tl tr :
leftist_inv tl -> leftist_inv tr ->
leftist_inv (makeT x tl tr).
Proof. 
rewrite /makeT; case: ifP=> H /=->->.
- by rewrite H.
- suffices: (measure tl <= measure tr)%N => [->|] //; move: H.
move=> /neq0_lt0n; by ssrnatlia.
Qed.

Lemma makeT_preserves_rk_inv x tl tr :
measure_inv tl -> measure_inv tr ->
measure_inv (makeT x tl tr).
Proof.
by rewrite /makeT; case: ifP=> /= _ ->->; rewrite measureNode eq_refl. 
Qed.

Lemma makeT_peserves_HO_inv x tl tr :
heap_ordered tl -> heap_ordered tr ->
LE x tl -> LE x tr ->
heap_ordered (makeT x tl tr).
Proof.
rewrite /makeT; by case: ifP => _ /=->->->->.
Qed.

Definition leftistheap h :=
[&& leftist_inv h, measure_inv h & heap_ordered h].

Fact leftistheap_NodexEE x : leftistheap [[|,|]| measure1, x | [|,|]].
Proof. by rewrite /leftistheap measure_inv_NodexEE heap_ordered_NodexEE leftist_inv_NodexEE. Qed.
Hint Resolve leftistheap_NodexEE : core.

Fact leftistheap_E : leftistheap ([|,|]).
Proof. by rewrite /leftistheap. Qed.
Hint Resolve leftistheap_E : core.

Fixpoint merge a :=
if a is Node n x a1 b1 then
let fix merge_a b :=
  if b is Node m y a2 b2 then
    if x <= y then 
      makeT x a1 (merge b1 b)
    else
      makeT y a2 (merge_a b2)
  else a in
merge_a
else id.

Arguments merge !tl !tr : rename.

Lemma merge_E_h: forall h, merge Emp h = h.
Proof.  by case. Qed.

Lemma merge_h_E: forall h, merge h Emp = h.
Proof. by case. Qed.

Lemma measure_inv_r n x tl tr:
measure_inv (Node n x tl tr) -> measure_inv tr.
Proof. by move=> /and3P[]. Qed.

Lemma measure_inv_l n x tl tr :
measure_inv (Node n x tl tr) -> measure_inv tl.
Proof. by move=> /and3P[]. Qed.

Lemma merge_a nl nr x y tll tlr trr trl :
(x <= y) = false -> 
merge (Node nl x tll tlr) (Node nr y trl trr) = 
makeT y trl (merge  (Node nl x tll tlr) trr).
Proof.
move=> /= ->.
by elim: trr.
Qed.

Lemma merge_preserve_measure_inv : forall h1 h2,
measure_inv h1 -> measure_inv h2 -> measure_inv (merge h1 h2) .
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr] //.
merge_casesxy x y => /= /and3P[??? /and3P[*]];
apply: makeT_preserves_rk_inv=> //; 
[apply: IHhr|apply: IH'hr]=> //=; apply/and3P; by split.
Qed.

Lemma case_heap_ordered_l n x tl tr :
heap_ordered (Node n x tl tr) -> (heap_ordered tl && LE x tl).
Proof. by move=> /= /and4P[-> _ ->]. Qed.

Lemma case_heap_ordered_r n x tl tr :
heap_ordered (Node n x tl tr) -> (heap_ordered tr && LE x tr).
Proof. by move=> /= /and4P[_ -> _ ->]. Qed.

Lemma case_LE x y n tr tl :
LE x (Node n y tl tr) -> x <= y.
Proof. by []. Qed.

Lemma merge_preserve_LE : forall h1 h2 x,
LE x h1 -> LE x h2 -> LE x (merge h1 h2).
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr x' /case_LE HH1 /case_LE HH2] //.
by merge_casesxy x y;
[makeT_casesxy (measure (merge tlr (Node nr y trl trr))) (measure tll)|
  makeT_casesxy (measure (merge (Node nl x tll tlr) trr)) (measure trl)].
Qed.

Lemma merge_preserve_HO_inv : forall h1 h2,
heap_ordered h1 -> heap_ordered h2 -> heap_ordered (merge h1 h2).
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr H1 H2] //.
move : (H1) (H2)=>
        /case_heap_ordered /and4P[L1 L2 HH1 HH2]
        /case_heap_ordered /and4P[L'1 L'2 HH'1 HH'2] //;
merge_casesxy x y; apply makeT_peserves_HO_inv=> //.
1 : apply: IHhr=> //.
2 : apply: IH'hr=> //.
all : apply: merge_preserve_LE=> //=.
move: (negbT H).
by rewrite -ltNge lt_def=> /andP[_ ->].
Qed.

Lemma case_leftist_inv_l n x tl tr : leftist_inv (Node n x tl tr) -> leftist_inv tl.
Proof. by move=> /and3P[].  Qed.

Lemma case_leftist_inv_r n x tl tr : leftist_inv (Node n x tl tr) -> leftist_inv tr.
Proof. by move=> /and3P[].  Qed.

Lemma merge_preserve_LI_inv : forall h1 h2,
leftist_inv h1 -> leftist_inv h2 -> leftist_inv (merge h1 h2).
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr H1 H2] //.
move : (H1) (H2) =>  /and3P[_ HH1 HH2] /and3P[_ HH'1 HH'2].
merge_casesxy x y; apply: makeT_preserves_LI_inv=> //.
- by apply: IHhr.
by apply: IH'hr.
Qed.    

Theorem merge_preserve_LH h1 h2 :
leftistheap h1 -> leftistheap h2 -> leftistheap (merge h1 h2).
Proof.
move=> /and3P[LI1 RR1 HO1] /and3P[LI2 RR2 HO2]; apply/andP; split.
- by apply: merge_preserve_LI_inv.
- apply/andP; split.
- by apply: merge_preserve_measure_inv.
by apply: merge_preserve_HO_inv. 
Qed.

Lemma makeT_spec h1 h2 x a: 
count a (makeT x h1 h2) = a x + count a h1 + count a h2.
Proof.
by makeT_casesxy (measure h2) (measure h1)=> /=; ssrnatlia.
Qed.

Lemma makeT_in_spec h1 h2 x y :
x \in (makeT y h1 h2) = ((x == y) || (x \in h1) || (x \in h2)).
Proof.
by rewrite !in_count makeT_spec eq_sym; case : (x == y)=> /=; rewrite !addn_gt0.
Qed.

Theorem merge_spec h1 h2 a: 
  count a (merge h1 h2) = count a h1 + count a h2.
Proof.
elim: h1 h2=> [h2|n x h1 IHh1 h2 IHh2]; rewrite ?merge_E_h //.
elim=> [/=|m y h21 IHh21 h22 IHh22]; first by ssrnatlia.
- by merge_casesxy x y; rewrite makeT_spec; rewrite ?(IHh2, IHh22) /=; ssrnatlia.
Qed.

Theorem merge_in_spec  h1 h2 x :
x \in (merge h1 h2) = ((x \in h1) || (x \in h2)).
Proof.
by rewrite !in_count merge_spec !addn_gt0.
Qed.

Definition insert (x : T) h := 
merge [[|,|]| measure1, x |[|,|]] h.


Lemma insert_preserve_measure_inv : forall h x,
measure_inv h -> measure_inv (insert x h).
Proof.
by move=> h x Rh; apply: merge_preserve_measure_inv.
Qed.

Lemma insert_preserve_HO_inv : forall h x,
heap_ordered h -> heap_ordered (insert x h).
Proof.
by move=> h x Rh; apply: merge_preserve_HO_inv.
Qed.

Lemma insert_preserve_LI_inv : forall h x,
leftist_inv h -> leftist_inv (insert x h).
Proof.
by move=> h x Rh; apply: merge_preserve_LI_inv.
Qed.

Theorem insert_preserve_LH : forall h x,
leftistheap h -> leftistheap (insert x h).
Proof.
by move=> h x Rh; apply: merge_preserve_LH.
Qed.

Theorem insert_spec h x a : 
  count a (insert x h) = a x + count a h.
Proof.
by rewrite merge_spec /=; ssrnatlia.
Qed.

Theorem insert_in_spec h x y :
x \in (insert y h) = ((x == y) || (x \in h)).
Proof.
rewrite merge_in_spec /= !in_Node; case (x == y); by case (x \in h).
Qed.

Definition findmin h := 
if h is Node _ x _ _ then Some x else None.

Theorem findmin_correct1 : forall h,
None = findmin h <-> h = Emp.
Proof. split=> [|-> //]. by case : h. Qed.

Lemma LE_correct : forall h x y,
heap_ordered h -> x \in h -> LE y h -> y <= x.
Proof.
elim=> [x y _ H| n x h1 IHh1 h2 IHh2 x' y' /= /and4P[L1 L2 H1 H2]] //
 /or3P[/eqP ->|/(IHh1 _ _ H1)/(_ L1)|/(IHh2 _ _ H2)/(_ L2)] //; swapg; exact: le_trans.
Qed.

Theorem findmin_correct2 : forall h, heap_ordered h ->
forall z, Some z = findmin h -> forall x, x \in h -> z <= x.
Proof.
case=> [//| n x h1 h2 HO z /= [->] y /or3P[/eqP ->||]] // H. 
- by move: HO=> /case_heap_ordered_l /andP[/LE_correct - /(_ _ x H)].
by move: HO=> /case_heap_ordered_r /andP[/LE_correct - /(_ _ x H)].
Qed.

Lemma findmin_cases : forall h, (exists x, Some x = findmin h) \/ (h = Emp).
Proof.
case=> [|n z h1 h2 /=]; first by right.
by left; exists z.
Qed.

Theorem findmin_LE_correct : forall x h,
heap_ordered h ->
((x \in h) && LE x h) <-> (Some x = findmin h).
Proof.
split=> [/andP[]|]; move: h H=> [] //.
- move=> n y h1 h2 /= /and4P[L1 L2 H1 H2]
  /or3P[/eqP-> //|/(LE_correct _ _ _ H1)/(_ L1)|/(LE_correct _ _ _ H2)/(_ L2)] XY YX;
  suffices: x = y=> [-> //|]; apply: le_anti; rewrite XY YX //.
move=> n s h1 h2 HO [] ->; apply/andP; split=> //=. 
by rewrite in_Node eq_refl.
Qed.

Definition deletemin h :=
if h is Node _ _ a b then merge a b else Emp.

Lemma measure_inv_eq n x h1 h2 :
measure_inv (Node n x h1 h2) -> n = f (measure h1) (measure h2).
Proof. by move=> /= /and3P[/eqP]; rewrite measureNode. Qed.

Lemma case_LE' x y h1 h2 n :
LE x (Node n y h1 h2) -> ((x <= y) = true).
Proof. by move=> /= ->. Qed.

Lemma case_leftistheap_l n x h1 h2 :
leftistheap (Node n x h1 h2) -> leftistheap h1.
Proof.
by rewrite /leftistheap=> /and3P[/case_leftist_inv_l-> /=/and3P[_ -> _] /and4P[]].
Qed.

Lemma case_leftistheap_r n x h1 h2 :
leftistheap (Node n x h1 h2) -> leftistheap h2.
Proof. 
by rewrite /leftistheap=> /and3P[/case_leftist_inv_r-> /=/and3P[_ _ -> /and4P[]]].
Qed.

Lemma deletemin_preserve_rk_inv : forall h, 
measure_inv h -> measure_inv (deletemin h).
Proof.
by case=> //=n x h1 h2 H; apply merge_preserve_measure_inv; move: H=> /and3P[].
Qed.

Lemma deletemin_preserve_HO_inv : forall h, 
heap_ordered h -> heap_ordered (deletemin h).
Proof.
case=> //=n x h1 h2 H; apply merge_preserve_HO_inv; by move: H=> /and4P[].
Qed.

Lemma deletemin_preserve_LI_inv : forall h, 
leftist_inv h -> leftist_inv (deletemin h).
Proof.
by case=> //=n x h1 h2 H; apply merge_preserve_LI_inv; move: H=> /and3P[].
Qed.

Lemma deletemin_correct : forall h, 
leftistheap h -> leftistheap (deletemin h).
Proof.
case=> //=n x h1 h2 H; apply merge_preserve_LH; move: H.
- by move/case_leftistheap_l.
by move/case_leftistheap_r.
Qed.

Theorem deletemin_spec h x: 
  Some x = findmin h -> (count^~ (insert x (deletemin h)) =1 count^~ h).
Proof.
by case: h=> // n y h1 h2 /= [->] a; rewrite insert_spec merge_spec addnA.
Qed.

Theorem deletemin_in_spec : forall h x y,
Some x = findmin h -> (y \in (insert x (deletemin h))) = (y \in h).
Proof.
case=> [//=|n x h1 h2 y z [->]].
by rewrite insert_in_spec /deletemin merge_in_spec //= orbA.
Qed.

Fixpoint insert' (x : T) h :=
if h is Node n y a b then
let h' := Node n y a b in 
  if x <= y then
    Node (f (measure h') (measure ([|,|]))) x h' Emp
  else makeT y a (insert' x b)
else Node measure1 x Emp Emp.

Theorem insertE x h : measure_inv h -> leftist_inv h -> insert' x h = insert x h.
Proof.
rewrite /insert.
elim h=> [//|n y h1 IHh1 h2 IHh2 MI LI] //.
merge_casesxy x y=> //; rewrite ?IHh2 //.
- rewrite /makeT.
  have: (measure [h1 | n, y | h2] <= measure ([|,|]) = false)%N.
- by apply/negbTE; rewrite -ltnNge. 
- by move=>->.
- by move: MI=> /= /and3P[].
by move: LI=> /= /and3P[].
Qed.

Implicit Type hh : seq (option (heap T)).

Fixpoint seq_to_seqheap (st : seq T) :=
if st is h :: t then
  cons [[|,|]| measure1, h |[|,|]] (seq_to_seqheap t)
else [::].

Fixpoint count_sseq a hh := 
  if hh is sh :: hh' then 
    if sh is some h then count a h + count_sseq a hh' 
    else count_sseq a hh'
  else 0.

Fixpoint count_seq a (sh : seq (heap T)) := 
  if sh is h :: sh' then count a h + count_seq a sh' else 0.

Theorem seq_to_seqheap_spec s: count_seq^~ (seq_to_seqheap s) =1 seq.count^~ s.
Proof.
move=> a; elim: s=> //= x s->; ssrnatlia.
Qed.

Fixpoint fromseqheap_push h1 hh :=
  match hh with
  | None :: hh' | [::] as hh' => (some h1) :: hh'
  | (some h2) :: hh' => None :: fromseqheap_push (merge h2 h1) hh'
  end.

Fixpoint fromseqheap_pop h1 hh :=
  if hh is sh2 :: hh' then
    let h2 := if sh2 is some h then h else  [|,|] in
   fromseqheap_pop (merge h2 h1) hh' else h1.

Fixpoint fromseqheap_rec hh sh  :=
  match sh with
  | [:: x1, x2 & h'] => let h1 := merge x1 x2 in
    fromseqheap_rec (fromseqheap_push h1 hh) h'
  | [:: h] => fromseqheap_pop h hh
  | [::] => fromseqheap_pop ( [|,|]) hh
  end.

Definition fromseqheap := (fromseqheap_rec [::]).

Fixpoint fromseqheap_rec1 hh sh :=
  if sh is x :: h then fromseqheap_rec1 (fromseqheap_push x hh) h else fromseqheap_pop ( [|,|]) hh.

Lemma fromseqheapE sh : fromseqheap sh = fromseqheap_rec1 [::] sh.
Proof.
transitivity (fromseqheap_rec1 [:: None] sh); last by case: sh.
rewrite /fromseqheap; move: [::] {2}_.+1 (ltnSn (size sh)./2) => hh n.
elim: n => // n IHn in hh sh *. case: sh => [|x [|y s]] //=; by rewrite ?merge_h_E=> //= /IHn->.
Qed.

Definition fromseq := fromseqheap \o seq_to_seqheap.

Lemma fromseqheap_pop_spec a h hh : 
  count a (fromseqheap_pop h hh) = count_sseq a hh + count a h.
Proof.
elim: hh => [|[h'|] shh IHhh] //= in h *; by rewrite IHhh merge_spec; ssrnatlia.
Qed.

Lemma fromseqheap_push_spec h hh a: 
  count_sseq a (fromseqheap_push h hh )= count a h + count_sseq a hh.
Proof.
elim: hh=> [|[sh|] hh' IHhh] //= in h *. by rewrite IHhh merge_spec; ssrnatlia.
Qed.


Lemma fromseqheap_rec1_spec sh hh a: 
  count a (fromseqheap_rec1 hh sh) = count_sseq a hh + count_seq a sh.
Proof.
elim: sh => [|h sh IHsh] /= in hh *.
  rewrite ?fromseqheap_pop_spec //. by rewrite IHsh fromseqheap_push_spec; ssrnatlia.
Qed.

Lemma fromseqheap_spec sh : 
 count^~ (fromseqheap sh) =1 count_seq^~ sh.
Proof.
move=> a; by rewrite fromseqheapE fromseqheap_rec1_spec.
Qed.

Theorem fromseq_cspec (s : seq T): 
  seq.count^~ s =1 count^~ (fromseq s).
Proof.
move=> a; by rewrite /fromseq /= fromseqheap_spec seq_to_seqheap_spec.
Qed.

Section Invariant.
Definition invariant := heap T -> bool.

Variables inv : invariant.

Hypothesis merge_preserve_invariat : forall h1 h2, inv h1 -> inv h2 -> inv (merge h1 h2).
Hypothesis inv_E : inv ([|,|]).
Hypothesis inv_NodexEE : forall x, inv [ [|,|]| measure1, x | [|,|]].
Hint Resolve inv_E : core.

Definition some_inv sh := if sh is some h then inv h else true.

Lemma inv_fromseqheap_pop h sh: 
  (all some_inv sh) -> inv h -> inv (fromseqheap_pop h sh).
Proof.
elim: sh => [|[h'|] shh IHhh] //= in h *=> /andP[HH' ASH HH]; apply: IHhh=> //.
by apply: merge_preserve_invariat.
Qed.

Lemma all_inv_fromseqheap_push h hh:
  inv h -> (all some_inv hh) ->
  all some_inv (fromseqheap_push h hh) = (inv h) && (all some_inv hh).
Proof.
by elim: hh=> [|[sh|] hh' IHhh] //= in h *=> HH /andP[SH AHH];
 rewrite IHhh ?merge_preserve_invariat // HH SH.
Qed.

Lemma inv_fromseqheap_rec1 hh sh : 
(all some_inv  hh) -> (all inv sh) -> (inv (fromseqheap_rec1 hh sh)).
Proof.
elim: sh => [|h sh IHsh] /= in hh *=> AHH; rewrite ?inv_fromseqheap_pop //.
move=> /andP[HH AHS]. by apply: IHsh; rewrite ?all_inv_fromseqheap_push ?HH ?AHS ?AHH.
Qed.


Lemma inv_fromseqheap sh : 
all inv sh -> inv (fromseqheap sh).
Proof.
move=> ASH; by rewrite fromseqheapE inv_fromseqheap_rec1.
Qed.

Lemma all_inv_seq_toseqheap s : 
all inv (seq_to_seqheap s).
Proof. elim: s=> //= a h->; by rewrite inv_NodexEE. Qed.

Lemma inv_fromseq s : inv (fromseq s).
Proof.
by rewrite /fromseq /= inv_fromseqheap // all_inv_seq_toseqheap.
Qed.
End Invariant.

Lemma measure_inv_E : measure_inv ([|,|]).
Proof. by []. Qed.


Definition rank_rk_fromseq : forall s, measure_inv (fromseq s) := 
  inv_fromseq measure_inv merge_preserve_measure_inv measure_inv_E measure_inv_NodexEE.

Definition heap_ordered_fromseq : forall s, heap_ordered (fromseq s) := 
  inv_fromseq heap_ordered merge_preserve_HO_inv heap_ordered_E (heap_ordered_NodexEE measure1).

Definition leftist_inv_fromseq : forall s, leftist_inv (fromseq s) := 
  inv_fromseq leftist_inv merge_preserve_LI_inv leftist_inv_E (leftist_inv_NodexEE measure1).

Definition leftistheap_fromseq : forall s, leftistheap (fromseq s) := 
  inv_fromseq leftistheap merge_preserve_LH leftistheap_E leftistheap_NodexEE.
End Measure.

Fixpoint rank h : nat := if h is Node _ _ _ b then (rank b).+1 else O.

Definition f1 (x y : nat) := y.+1.

Lemma rank__NodexEE : f1 (rank ([|,|])) (rank ([|,|])) = 1%N.
Proof. by []. Qed.

Lemma rankNode : forall tl tr n x, rank [tl| x, n |tr] = f1 (rank tl) (rank tr).
Proof. by []. Qed.

Lemma rank_Node_E : forall h1 h2 n x, (rank ([|,|]) < rank [h1 | n, x | h2])%N.
Proof. by []. Qed.

Definition rank_measureMixin : Measure.mixin_of rank := Measure.Mixin T rank 1%N f1 rankNode rank__NodexEE rank_Node_E.
Canonical rank_measureType : measureType T := Measure.Pack T rank rank_measureMixin.

Fixpoint size h : nat :=
if h is Node _ _ a b then (size a) + (size b) + 1 else O.

Definition f2 (x y : nat) := x + y + 1.

Lemma sizeNode : forall tl tr n x, size [tl| x, n |tr] = f2 (size tl) (size tr).
Proof. by []. Qed.
Lemma size__NodexEE : f2 (size ([|,|])) (size ([|,|])) = 1%N.
Proof. by []. Qed.
Lemma size_Node_E : forall h1 h2 n x, (size ([|,|]) < size [h1 | n, x | h2])%N.
Proof. move=> /= h1 h2 n x. rewrite addn_gt0; apply/orP; by right. Qed.

Definition size_measureMixin : Measure.mixin_of size := Measure.Mixin T size 1%N f2 sizeNode size__NodexEE size_Node_E.
Canonical size_measureType : measureType T := Measure.Pack T size size_measureMixin.

Definition leftist_rank_inv := (leftist_measure_inv rank_measureType).
Definition case_leftist_rank_inv := (case_leftist_measure_inv rank_measureType).
Definition case_leftist_rank_inv_r := (case_leftist_measure_inv_r rank_measureType).
Definition case_leftist_rank_inv_rl := (case_leftist_measure_inv_rl rank_measureType).

Lemma rank_correct x n tl tr : measure_inv rank_measureType [tl| n, x |tr] -> n == (rank tr).+1.
Proof. by move=> /= /and3P[]. Qed.

Section Grank.

(** The (general) rank of a tree is the length of the shortest path from the root to leaves *)
Fixpoint grank h : nat :=
  if h is Node _ _ tl tr then
    (minn (grank tl) (grank tr)).+1
  else 0.

Theorem grank_rk h : leftist_rank_inv  h -> grank h = rank h.
Proof.
elim: h=> // n x h1 IHh1 h2 IHh2
          /case_leftist_rank_inv/andP[]. rewrite /f /= /f1=>_ /and3P[L1 L2].
rewrite IHh1 // IHh2 //. by rewrite minnC ?Order.NatOrder.minnE=> ->.
Qed.

End Grank.

Section Spine.

Lemma length_right_spine : forall h s, 
leftist_rank_inv h -> Right s -> spine_in s h -> length s = rank h.
Proof.
move=> h s /andP [] _ RC.
elim: h s RC=> 
[[|[]]|n x tl IHhl tr IHtr [_ _|[s /= /and3P[_ RRl RRr] |]]] //= R S.
apply/eqnP=> /=. apply/eqP. by apply: IHtr.
Qed.

Theorem rigth_spine_shortest : 
forall H s1 s2, Right s1 -> leftist_rank_inv H -> spine_in s1 H -> spine_in s2 H ->
(length s1 <= length s2)%nat.
Proof. 
elim=>
[s1 s2 _ _ /spine_in_E->|
n x tl IHtl tr IHtr [//|
a s1 [ _ _ _ |[]
s2 /rigth_correct [] ->]]] //= => [Rs1 /case_leftist_rank_inv_r LI|
Rs1 /case_leftist_rank_inv_rl /and3P[LI1 LI2 LE]] => SI1 SI2.
- rewrite -addn1 -[(length s2).+1]addn1 leq_add2r. by apply IHtr.
rewrite (length_right_spine tr s1) //.
case: (right_spine_ex tl)=> s /andP [] Rs SIstl.
suffices: (rank tl <= length s2)%N. move: LE=> /=; ssrnatlia.
rewrite -(length_right_spine tl s) //.
apply: IHtl=> //.
Qed.
End Spine.
End Specifications.
End leftistheap.