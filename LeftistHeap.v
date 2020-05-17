From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype. 
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).
Import Order.NatOrder.
From Equations Require Import Equations.

Open Scope order_scope.

Lemma snd_true3 a b : a || true || b.
Proof. by case: a. Qed.

Lemma trd_true3 a b : b || a || true.
Proof. by case: a; case b. Qed.

Lemma snd_true2 a : a || true.
Proof. by case: a. Qed.

Lemma add_lt_le a b c d: (a < c)%N -> (b <= d)%N -> (a + b < c + d)%N.
Proof. by move=> *; rewrite [a + b]addnC -ltn_subRL -addnBA // ltn_addr. Qed.

Lemma add_le_lt a b c d: (a <= c)%N -> (b < d)%N -> (a + b < c + d)%N.
Proof. move=> *; rewrite [a + b]addnC [c + d]addnC. by apply: add_lt_le. Qed.


Hint Resolve trd_true3 snd_true3 snd_true2 lexx ltxx : core.

Module leftistheap.
(* Leftist heaps are heap-ordered binary trees that satisfy the                         *)
(* leftist property: the rank of any left child is at least as large as the rank of its *)
(* right sibling. The rank of a node is defined to be the length of its right spine     *)
(* (i.e., the rightmost path from the node in question to an empty node).               *)
Section LeftistDef.
Variables (T: ordType).

Inductive heap :=
| Emp : heap
| Node : nat -> T-> heap -> heap -> heap.

End LeftistDef.
Arguments Node {T}.
Arguments Emp {T}.
Notation "[ tl | n , x | tr ]" := (Node n x tl tr) (at level 0).
Notation "'[||]'" := Emp.

(* Definition of arbitrary measure on Heaps *)
Module Measure.
Structure mixin_of {T : ordType} (measure : heap T -> nat) :=
  Mixin {
    measure1            : nat;
    f                   : nat -> nat -> nat;
    measureNode         : forall tl tr n x, measure [tl| x, n |tr] = f (measure tl) (measure tr);
    measure_NodexEE     : f (measure [||]) (measure [||]) = measure1;
    measure_Node_E      : forall h1 h2 n x, (measure [||] < measure [h1 | n, x | h2])%N
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

Definition empty h :=
if h is Emp then true else false.

Theorem emptyP h : reflect (h = Emp) (empty h).
Proof. case h; by constructor. Qed.


(* Definition of decidable equality on Heaps  *)
Fixpoint eqheap h1 h2 :=
  match h1, h2 with
  | Emp, Emp => true
  | Node n1 x1 tl1 tr1, Node n2 x2 tl2 tr2 => [&& (n1 == n2), (x1 == x2), eqheap tl1 tl2 & eqheap tr1 tr2]
  | _, _ => false
  end.

Lemma eqheapP : Equality.axiom eqheap.
Proof.
elim=> [|??? IHh1 ? IHh2] [|*] /=; try by constructor.
by apply: (iffP and4P); case=> [/eqP-> /eqP-> /IHh1-> /IHh2->].
Qed.

Canonical heap_eqMixin := EqMixin eqheapP.
Canonical heap_eqType := Eval hnf in EqType (heap T) heap_eqMixin.

Lemma eqheapE : eqheap = eq_op. Proof. by []. Qed.

Fixpoint mem_heap h :=
  if h is Node _ y tl tr then xpredU1 y (xpredU (mem_heap tl) (mem_heap tr)) else xpred0.

Definition heap_eqclass := heap T.
Identity Coercion heap_of_eqclass : heap_eqclass >-> heap.
Coercion pred_of_heap (h : heap_eqclass) : {pred T} := mem_heap h.

Canonical heap_predType := PredType pred_of_heap.
(* The line below makes mem_heap a canonical instance of topred. *)
Canonical mem_heap_predType := PredType mem_heap.

Lemma in_node x y n tl tr: 
  x \in [tl | n, y | tr] = [|| x == y, x \in tl | x \in tr].
Proof. by []. Qed.

(* Definition of rank and size and simple properties *)
Section Mesures.

Fixpoint rank h : nat := if h is Node _ _ _ b then (rank b).+1 else O.

Definition f1 (x y : nat) := y.+1.

Lemma rank__NodexEE : f1 (rank [||]) (rank  [||]) = 1%N.
Proof. by []. Qed.

Lemma rankNode tl tr n x : rank [tl| x, n |tr] = f1 (rank tl) (rank tr).
Proof. by []. Qed.

Lemma rank_Node_E h1 h2 n x : (rank  [||] < rank [h1 | n, x | h2])%N.
Proof. by []. Qed.

Fixpoint size h : nat :=
if h is Node _ _ a b then (size a) + (size b) + 1 else O.

Definition f2 (x y : nat) := x + y + 1.

Lemma sizeNode tl tr n x : size [tl| x, n |tr] = f2 (size tl) (size tr).
Proof. by []. Qed.

Lemma size__NodexEE : f2 (size  [||]) (size  [||]) = 1%N.
Proof. by []. Qed.
Lemma size_Node_E h1 h2 n x : (size  [||] < size [h1 | n, x | h2])%N.
Proof. by rewrite addn_gt0 leqnn. Qed.

End Mesures.

(* Definition of count, all and simple properties *)
Section HeapCount.
Variables a : pred T.

Fixpoint count h : nat := if h is [tl| _, x |tr] then a x + count
 tl + count tr else 0.

Lemma count_Node tl tr y n: count [tl| n, y |tr] = a y + count tl + count tr.
Proof. by []. Qed.

Lemma count_E : count [||] = 0.
Proof. by []. Qed.

Lemma count_NodexEE n y : count [[||]| n, y | [||]] = a y.
Proof. by rewrite /= !addn0. Qed.

Fixpoint all h := 
if h is [tl| _, x |tr] then [&& a x, (all tl) & all tr] else true.

End HeapCount.

Lemma count_a_predT a h : (count a h <= count predT h)%N.
Proof. elim: h=> //= n s *; case: (a s); by repeat apply: leq_add. Qed.
Hint Resolve count_a_predT: core.

Lemma size_count h : size =1 count predT.
Proof. by elim=> //= n x h1 -> h2->; ssrnatlia. Qed.

Lemma allE h a : reflect (count a h = size h) (all a h).
Proof.
rewrite size_count //.
elim: h => /= [| _ s h1 /(sameP eqP) <- h2 /(sameP eqP) <-]; first by constructor.
apply/introP => [/and3P[-> /eqP-> /eqP->]|] // H.
suffices: ((a s) + count a h1 + count a h2 < 1 + count predT h1 + count predT h2)%N.
- by move=> LE EQ; move: EQ LE=>->; rewrite ltnn.
move: H=> /nandP[/negPf->|/nandP[] H] //=.
- apply: add_lt_le=> //; apply : add_lt_le=> //.
1: have: (count a h1 < count predT h1)%N=>*.
3: have: (count a h2 < count predT h2)%N=>*.
1,3: rewrite ltn_neqAle; apply/andP; by split.
- apply: add_lt_le=> //; apply add_le_lt=> //; by case (a s).
- apply: add_le_lt=> //. apply leq_add=> //; by case (a s).
Qed.

Lemma in_count x h: x \in h = (0 < count (xpred1 x) h)%N.
Proof.
elim h=> // ??? IHh1 ? IHh2; by rewrite in_node /= !addn_gt0 IHh1 IHh2 eq_sym lt0b orbA.
Qed.

(* if h is heap oredered (see below) LE x h is same as   *)
(* x is less or equal then all elements in heaps         *)
Definition LE x h : bool := 
if h is Node n y a b then (x <= y) else true.

Lemma LE_trans y x h: LE y h -> (x <= y) -> LE x h.
Proof. by case: h=> //= ???? H /le_trans/(_ H). Qed.

(* Definition of heap ordered heaps and simpl properties *)
Fixpoint heap_ordered h : bool :=
if h is Node n x tl tr then
  [&& (LE x tl), (LE x tr), (heap_ordered tl) & (heap_ordered tr)]
else true.

Lemma LE_correct h x y: heap_ordered h -> x \in h -> LE y h -> y <= x.
Proof.
by elim: h x y=> [| n x h1 IHh1 h2 IHh2 x' y' /= /and4P[L1 L2 H1 H2]] //
/or3P[/eqP ->|/(IHh1 _ _ H1)/(_ L1)|/(IHh2 _ _ H2)/(_ L2)] // H /le_trans/(_ H).
Qed.

Lemma LE_spec x h : heap_ordered h -> LE x h -> all (>= x) h.
Proof.
elim h=> // n y h1 IHh1 h2 IHh2 /= /and4P[???? XY].
by rewrite XY IHh1 // ?IHh2 // ?(LE_trans y).
Qed.

Fact heap_ordered_NodexEE n x : heap_ordered [ [||]| n, x |  [||]].
Proof. by []. Qed.
Hint Resolve heap_ordered_NodexEE: core.
Fact heap_ordered_E : heap_ordered [||]. Proof. by []. Qed.

(* Some basic definitions for reasoning about spines in heaps *)
Variant side := R | L.

Definition spine := seq side.

Fixpoint spine_in p h : bool :=
match p, h with
| R :: p, Node _ _ _ tr => spine_in p tr
| L :: p, Node _ _ tl _ => spine_in p tl
| [::],   Emp          => true
| _,      _          => false
end.

Fixpoint right p : bool :=
match p with
| R :: p' => right p'
| L :: _  => false
| [::]    => true
end.

Lemma rigth_correct x s: right (x :: s) -> ((x = R) * right s).
Proof. by case: s; case x. Qed.

Lemma right_spine_ex h: exists s, right s && spine_in s h.
Proof.
elim: h=> [|n s hl _ hr [] s']; by [exists nil| exists (R :: s')].
Qed.

Lemma spine_in_E s : spine_in s Emp -> s = [::].
Proof. by case: s=> [|[]] //=. Qed.

(* Theory for heaps with leftist measure *)

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
| [||]           => true
end.

Lemma measure_inv_NodexEE x : measure_inv [ [||]| measure1, x | [||]].
Proof. by rewrite /= measureNode measure_NodexEE eq_refl. Qed.
Hint Resolve measure_inv_NodexEE : core.

Fact measure_E : measure_inv [||]. Proof. by []. Qed.

(* leftist invariant for arbitrary mesure and defonition of leftist heap *)
Fixpoint leftist_inv h : bool :=
if h is Node n x tl tr then
  [&& (measure tr <= measure tl)%N, (leftist_inv tl) & (leftist_inv tr)]
else true.

Fact leftist_inv_NodexEE n x : leftist_inv [[||]| n, x |  [||]].
Proof. move=> /=; by rewrite leqnn. Qed.
Hint Resolve leftist_inv_NodexEE : core.

Fact leftist_inv_E : leftist_inv [||]. Proof. by []. Qed.

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

Lemma case_leftist_measure_inv n x tl tr: 
leftist_measure_inv (Node n x tl tr) -> (n == f (measure tl) (measure tr)) &&
[&& leftist_measure_inv tr, leftist_measure_inv tl & (measure tr <= measure tl)%N].
Proof.
move=> LI. move: LI (LI)=> /case_leftist_measure_inv_rl -> /andP[_] /= /and3P[]; 
by rewrite measureNode=>->.
Qed. 

Definition leftistheap h :=
[&& leftist_inv h, measure_inv h & heap_ordered h].

Fact leftistheap_NodexEE x : leftistheap [[||]| measure1, x |[||]].
Proof. by rewrite /leftistheap measure_inv_NodexEE heap_ordered_NodexEE leftist_inv_NodexEE. Qed.
Hint Resolve leftistheap_NodexEE : core.

Fact leftistheap_E : leftistheap  [||].
Proof. by rewrite /leftistheap. Qed.
Hint Resolve leftistheap_E : core.

(* makeT takes two heaps and element and make heap from them *)
(* with correct mesure                                       *)
Definition makeT (x : T) h1 h2 :=
let m1 := measure h1 in
  let m2 := measure h2 in
      if (m2 <= m1)%N then [h1| f m1 m2, x |h2] else [h2| f m2 m1, x |h1] .

Lemma makeT_LI_inv x tl tr : leftist_inv tl -> leftist_inv tr ->
leftist_inv (makeT x tl tr).
Proof. 
rewrite /makeT; case: ifP=> H /=->->; first by rewrite H.
- suffices: (measure tl <= measure tr)%N => [->|] //; move: H.
move=> /neq0_lt0n; by ssrnatlia.
Qed.

Lemma makeT_rk_inv x tl tr : measure_inv tl -> measure_inv tr ->
measure_inv (makeT x tl tr).
Proof.
by rewrite /makeT; case: ifP=> /= _ ->->; rewrite measureNode eq_refl. 
Qed.

Lemma makeT_peserve_HO_inv x tl tr :
heap_ordered tl -> heap_ordered tr -> LE x tl -> LE x tr ->
 heap_ordered (makeT x tl tr).
Proof. rewrite /makeT; by case: ifP => _ /=->->->->. Qed.

Lemma makeT_spec h1 h2 x a:
count a (makeT x h1 h2) = a x + count a h1 + count a h2.
Proof. rewrite /makeT; case: ifP=> /=; ssrnatlia. Qed.

Lemma makeT_in_spec h1 h2 x y :
x \in (makeT y h1 h2) = ((x == y) || (x \in h1) || (x \in h2)).
Proof.
by rewrite !in_count makeT_spec eq_sym; case : (x == y)=> /=; rewrite !addn_gt0.
Qed.

(* fuction merge makes from two heaps nwe one that contains *)
(* same elements (see merge_spec)                           *)
(* Here your can see special total realization of merge     *)
Fixpoint merge' a :=
if a is Node n x a1 b1 then
let fix merge_a b :=
  if b is Node m y a2 b2 then
    if x <= y then 
      makeT x a1 (merge' b1 b)
    else
      makeT y a2 (merge_a b2)
  else a in
merge_a
else id.

Arguments merge' !tl !tr : rename.
Definition merge := nosimpl merge'.

Ltac merge_cases := match goal with 
| H : (?x <= ?y) = true |- _ => move: (H); rewrite /merge /= =>->; rewrite ?H
| H : (?x <= ?y) = false |- _ => move: (H)=> /merge_a /= ->; rewrite ?H
end. 

Ltac merge_casesxy x y := case H : (x <= y); merge_cases.

Lemma merge_E_h h: merge Emp h = h.
Proof. by []. Qed.

Lemma merge_h_E h: merge h Emp = h.
Proof. by case: h. Qed.

Lemma merge_a nl nr x y tll tlr trr trl : (x <= y) = false -> 
merge (Node nl x tll tlr) (Node nr y trl trr) = 
makeT y trl (merge  (Node nl x tll tlr) trr).
Proof. rewrite /merge /= => ->. by elim: trr. Qed.

Lemma merge_measure_inv h1 h2:
measure_inv h1 -> measure_inv h2 -> measure_inv (merge h1 h2) .
Proof.
elim: h1 h2=> // ? x ??? IHhr. elim=> // ? y ??? IH'hr.
merge_casesxy x y => /and3P[E M M' /and3P[EQ M1 M2]];
by rewrite makeT_rk_inv // (IHhr, IH'hr) //= (EQ, E) (M1, M) (M2, M').
Qed.

Lemma merge_LE h1 h2 x: LE x h1 -> LE x h2 -> LE x (merge h1 h2).
Proof.
elim: h1 h2 x => // ? x ????. elim=> // ? y *. 
by merge_casesxy x y; rewrite /makeT; case: ifP.
Qed.

Lemma merge_HO_inv h1 h2:
heap_ordered h1 -> heap_ordered h2 -> heap_ordered (merge h1 h2).
Proof.
elim: h1 h2=> // ? x ??? IHhr. elim=> // ? y ??? IH'hr H1 H2.
move : (H1) (H2)=> /and4P[???? /and4P[????]]. by merge_casesxy x y;
rewrite makeT_peserve_HO_inv ?IHhr ?IH'hr ?merge_LE //=; move: H; case: ltgtP.
Qed.

Lemma merge_LI_inv h1 h2:
 leftist_inv h1 -> leftist_inv h2 -> leftist_inv (merge h1 h2).
Proof.
elim: h1 h2=> // ? x ??? IHhr. elim=> // ? y ??? IH'hr H1 H2.
move : (H1) (H2) => /and3P[??? /and3P[*]]. merge_casesxy x y; 
by rewrite makeT_LI_inv ?IHhr ?IH'hr.
Qed.

Theorem merge_LH h1 h2 :
leftistheap h1 -> leftistheap h2 -> leftistheap (merge h1 h2).
Proof.
move=> /and3P[???/and3P[*]].
by rewrite /leftistheap merge_LI_inv ?merge_measure_inv ?merge_HO_inv.
Qed.

Theorem merge_spec h1 h2 a:  count a (merge h1 h2) = count a h1 + count a h2.
Proof.
elim: h1 h2=> [?|? x ??? IHh2] //. elim=> [/=|? y ??? IHh22]; first by ssrnatlia.
by merge_casesxy x y; rewrite makeT_spec ?IHh2 ?IHh22 /=; ssrnatlia.
Qed.

Lemma merge_size h1 h2 : size (merge h1 h2) = size h1 + size h2.
Proof. by rewrite !size_count ?merge_spec. Qed.

Theorem merge_in_spec  h1 h2 x : x \in (merge h1 h2) = ((x \in h1) || (x \in h2)).
Proof. by rewrite !in_count merge_spec !addn_gt0. Qed.

(* Two defenition of insert, their equality and some properties *)
Definition insert (x : T) h :=  merge [[||]| measure1, x | [||]] h.

Fixpoint insert' (x : T) h :=
if h is Node n y a b then
let h' := Node n y a b in 
  if x <= y then
    Node (f (measure h') (measure [||])) x h' Emp
  else makeT y a (insert' x b)
else Node measure1 x Emp Emp.

Lemma insert_measure_inv h x: measure_inv h -> measure_inv (insert x h).
Proof. by move=> *; apply: merge_measure_inv. Qed.

Lemma insert_HO_inv h x: heap_ordered h -> heap_ordered (insert x h).
Proof. by move=> *; apply: merge_HO_inv. Qed.

Lemma insert_LI_inv h x: leftist_inv h -> leftist_inv (insert x h).
Proof. by move=> *; apply: merge_LI_inv. Qed.

Theorem insert_LH h x: leftistheap h -> leftistheap (insert x h).
Proof. by move=> *; apply: merge_LH. Qed.

Theorem insert_spec h x a : count a (insert x h) = a x + count a h.
Proof. by rewrite merge_spec /=; ssrnatlia. Qed.

Lemma insert_size h x: size (insert x h) = (size h).+1.
Proof. by rewrite !size_count ?merge_spec. Qed.

Theorem insertE x h : measure_inv h -> leftist_inv h -> insert' x h = insert x h.
Proof.
rewrite /insert. elim h=> // n y h1 IHh1 h2 IHh2 /= /and3P[??? /and3P[*]].
merge_casesxy x y=> //; rewrite ?IHh2 // /makeT.
have: (measure [h1 | n, y | h2] <= measure [||] = false)%N=> [|->] //.
by apply/negbTE; rewrite -ltnNge. 
Qed.

Theorem insert_in_spec h x y : x \in (insert y h) = ((x == y) || (x \in h)).
Proof. 
rewrite merge_in_spec /= !in_node; case (x == y); by case (x \in h).
Qed.


(* Properties of findmin function *)
Definition findmin h := 
if h is Node _ x _ _ then Some x else None.

Theorem findmin_None h: None = findmin h <-> h = [||].
Proof. split=> [|-> //]. by case : h. Qed.

Theorem findmin_Some h z: heap_ordered h ->
Some z = findmin h -> all (>= z) h.
Proof. 
case: h=> //= _ ??? /and3P[?? /andP[?? [->]]]; by rewrite lexx ?LE_spec. 
Qed.

Lemma findmin_cases h: (exists x, Some x = findmin h) \/ (h = Emp).
Proof. case: h=> [|n z h1 h2 /=]; first by right. by left; exists z. Qed.

Theorem findmin_spec x h: heap_ordered h -> 
((x \in h) && LE x h) <-> (Some x = findmin h).
Proof.
split=> [/andP[]|]; move: h H=> [] //.
- move=> n y h1 h2 /= /and4P[L1 L2 H1 H2]
  /or3P[/eqP-> //|/(LE_correct _ _ _ H1)/(_ L1)|/(LE_correct _ _ _ H2)/(_ L2)] XY YX;
suffices: x = y=> [-> //|]; apply: le_anti; rewrite XY YX //.
move=> ????? [->]. by rewrite in_node eq_refl /=.
Qed.

(* Properties of findmin function *)
Definition deletemin h := if h is Node _ _ a b then merge a b else Emp.

Lemma case_leftistheap n x h1 h2 :
leftistheap (Node n x h1 h2) -> leftistheap h1 && leftistheap h2.
Proof.
by rewrite/leftistheap=>/and3P[/=/and3P[_->->/=/and3P[_->->/and4P[_ _->->]]]].
Qed.

Lemma deletemin_rk_inv h: measure_inv h -> measure_inv (deletemin h).
Proof. case: h=> //= ???? /and3P[*]; by rewrite merge_measure_inv. Qed.

Lemma deletemin_ho_inv h: heap_ordered h -> heap_ordered (deletemin h).
Proof. case: h=> //= ???? /and4P[*]. by rewrite merge_HO_inv. Qed.


Lemma deletemin_LI_inv h: leftist_inv h -> leftist_inv (deletemin h).
Proof. case: h=> //= ???? /and3P[*]. by rewrite merge_LI_inv. Qed.

Lemma deletemin_correct h:
leftistheap h -> leftistheap (deletemin h).
Proof.
by case: h=> //=???? H; apply merge_LH; move: H=> /case_leftistheap/andP[].
Qed.

Theorem deletemin_spec h x: 
  Some x = findmin h <-> (count^~ (insert x (deletemin h)) =1 count^~ h).
Proof.

case: h=> /=; first (split=> // /(_ (pred1 x)) /=; by rewrite eq_refl).
move=> _ s??; split=> [[-> a]|/(_ (pred1 x))]; 
rewrite insert_spec merge_spec addnA // -2?addnA=> /eqP; 
rewrite eqn_add2r/= eq_refl=> /eqP/esym. case E: (s == x)=> //. by rewrite (eqP E).
Qed.

Lemma deletemin_size h : size (deletemin h) = (size h).-1.
Proof. case: h=> // n x tl tr; by rewrite ?size_count //= merge_spec. Qed.

Theorem deletemin_in_spec h x y:
Some x = findmin h -> (y \in (insert x (deletemin h))) = (y \in h).
Proof.
case: h=> // ???? [->]. 
by rewrite insert_in_spec /deletemin merge_in_spec // orbA.
Qed.

(* In this section we define heapsort and prove it's properties *)
(* heapsort fist translates sequense of elements into heap and  *)
(* than takes the minimal element of the heap while it is not   *)
(* empty                                                        *)
Section Heapsort.
Implicit Type hh : seq (option (heap T)).

Fixpoint seq_to_seqheap (st : seq T) :=
if st is h :: t then cons [ [||]| measure1, h | [||]] (seq_to_seqheap t)
else [::].

Fixpoint count_sseq a hh := 
  if hh is sh :: hh' then 
    if sh is some h then count a h + count_sseq a hh' 
    else count_sseq a hh'
  else 0.

Fixpoint count_seq a (sh : seq (heap T)) := 
  if sh is h :: sh' then count a h + count_seq a sh' else 0.

Theorem seq_to_seqheap_spec s: count_seq^~ (seq_to_seqheap s) =1 seq.count^~ s.
Proof. move=> a; elim: s=> //= ??->; ssrnatlia. Qed.

(* Now we want to define fromseq function that will translate  *)
(* sequense of elements into heap in O(n) time                 *)
(* Our implementation is based on divide and conqure principle *)
(* adapted to total languages                                  *)
Fixpoint fromseqheap_push h1 hh :=
  match hh with
  | None :: hh' | [::] as hh' => (some h1) :: hh'
  | (some h2) :: hh' => None :: fromseqheap_push (merge h2 h1) hh'
  end.

Fixpoint fromseqheap_pop h1 hh :=
  if hh is sh2 :: hh' then
    let h2 := if sh2 is some h then h else [||] in
   fromseqheap_pop (merge h2 h1) hh' else h1.

Fixpoint fromseqheap_rec hh sh  :=
  match sh with
  | [:: x1, x2 & h'] => let h1 := merge x1 x2 in
    fromseqheap_rec (fromseqheap_push h1 hh) h'
  | [:: h] => fromseqheap_pop h hh
  | [::] => fromseqheap_pop [||] hh
  end.

Definition fromseqheap := (fromseqheap_rec [::]).

Fixpoint fromseqheap_rec1 hh sh :=
  if sh is x :: h then fromseqheap_rec1 (fromseqheap_push x hh) h else fromseqheap_pop (  [||]) hh.

Lemma fromseqheapE sh : fromseqheap sh = fromseqheap_rec1 [::] sh.
Proof.
transitivity (fromseqheap_rec1 [:: None] sh); last by case: sh.
rewrite /fromseqheap; move: [::] {2}_.+1 (ltnSn (seq.size sh)./2) => hh n.
elim: n => // n IHn in hh sh *. case: sh => [|x [|y s]] //=; by rewrite ?merge_h_E=> //= /IHn->.
Qed.

Definition fromseq := fromseqheap \o seq_to_seqheap.

Lemma fromseqheap_pop_spec a h hh : 
  count a (fromseqheap_pop h hh) = count_sseq a hh + count a h.
Proof.
elim: hh => [|[?|]? IHhh] //= in h *; by rewrite IHhh merge_spec; ssrnatlia.
Qed.

Lemma fromseqheap_push_spec h hh a: 
  count_sseq a (fromseqheap_push h hh )= count a h + count_sseq a hh.
Proof.
elim: hh=> [|[?|]? IHhh] //= in h *. by rewrite IHhh merge_spec; ssrnatlia.
Qed.

Lemma fromseqheap_rec1_spec sh hh a: 
  count a (fromseqheap_rec1 hh sh) = count_sseq a hh + count_seq a sh.
Proof.
elim: sh => [|?? IHsh] /= in hh *;
by rewrite ?fromseqheap_pop_spec // IHsh fromseqheap_push_spec; ssrnatlia.
Qed.

Lemma fromseqheap_spec sh : 
 count^~ (fromseqheap sh) =1 count_seq^~ sh.
Proof. move=> a; by rewrite fromseqheapE fromseqheap_rec1_spec. Qed.

Theorem fromseq_cspec (s : seq T): 
  seq.count^~ s =1 count^~ (fromseq s).
Proof.
move=> a; by rewrite /fromseq /= fromseqheap_spec seq_to_seqheap_spec.
Qed.

(* In this section we prove that fromseq s statisfy any invariant *)
(* with spesial properties                                        *)
Section Invariant.
Definition invariant := heap T -> bool.

Variables inv : invariant.

Hypothesis merge_invariat : forall h1 h2, inv h1 -> inv h2 -> inv (merge h1 h2).
Hypothesis inv_E : inv [||].
Hypothesis inv_NodexEE : forall x, inv [[||]| measure1, x |  [||]].
Hint Resolve inv_E : core.

Definition some_inv sh := if sh is some h then inv h else true.

Lemma inv_fromseqheap_pop h sh: 
  (seq.all some_inv sh) -> inv h -> inv (fromseqheap_pop h sh).
Proof.
elim: sh=> [|[?|]? IHhh] //= in h *=> /andP[*]; by rewrite IHhh ?merge_invariat. 
Qed.

Lemma all_inv_fromseqheap_push h hh: inv h -> (seq.all some_inv hh) ->
seq.all some_inv (fromseqheap_push h hh) = (inv h) && (seq.all some_inv hh).
Proof.
by elim: hh=> [|[?|]? IHhh] //= in h *=> HH /andP[SH ?]; 
rewrite IHhh ?merge_invariat // HH SH.
Qed.

Lemma inv_fromseqheap_rec1 hh sh : 
(seq.all some_inv  hh) -> (seq.all inv sh) -> (inv (fromseqheap_rec1 hh sh)).
Proof.
elim: sh => [|h sh IHsh] /= in hh *=> ?; rewrite ?inv_fromseqheap_pop //.
move => /andP[HH ?]. by rewrite IHsh ?all_inv_fromseqheap_push // HH.
Qed.

Lemma inv_fromseqheap sh : seq.all inv sh -> inv (fromseqheap sh).
Proof. move=> ASH; by rewrite fromseqheapE inv_fromseqheap_rec1. Qed.

Lemma all_inv_seq_toseqheap s : seq.all inv (seq_to_seqheap s).
Proof. elim: s=> //= a h->; by rewrite inv_NodexEE. Qed.

Lemma inv_fromseq s : inv (fromseq s).
Proof. by rewrite /fromseq /= inv_fromseqheap // all_inv_seq_toseqheap. Qed.
End Invariant.

Lemma measure_inv_E : measure_inv [||].
Proof. by []. Qed.

Definition rank_rk_fromseq : forall s, measure_inv (fromseq s) := 
  inv_fromseq measure_inv merge_measure_inv measure_inv_E measure_inv_NodexEE.

Definition heap_ordered_fromseq : forall s, heap_ordered (fromseq s) := 
  inv_fromseq heap_ordered merge_HO_inv heap_ordered_E (heap_ordered_NodexEE measure1).

Definition leftist_inv_fromseq : forall s, leftist_inv (fromseq s) := 
  inv_fromseq leftist_inv merge_LI_inv leftist_inv_E (leftist_inv_NodexEE measure1).

Definition leftistheap_fromseq : forall s, leftistheap (fromseq s) := 
  inv_fromseq leftistheap merge_LH leftistheap_E leftistheap_NodexEE.


Equations fromheap h : seq T by wf (size h) lt:=
fromheap [||] := [::];
fromheap [tl| n, x |tr] := x :: (fromheap (deletemin [tl| n, x |tr])).

Next Obligation. rewrite merge_size; ssrnatlia. Qed.

Lemma fromheap_spec1 h: count^~ h =1 seq.count^~ (fromheap h).
Proof.
move=> p. apply_funelim (fromheap h)=> // ???? /= <-. by rewrite merge_spec; ssrnatlia.
Qed.

Lemma fromheap_srec1_in x h: (x \in h) = (x \in (fromheap h)).
Proof. by rewrite !in_count -has_pred1 has_count -fromheap_spec1. Qed.

Lemma fromheap_spec2 h: (heap_ordered h) -> sorted <=%O (fromheap h).
Proof.
apply_funelim (fromheap h)=> //= _ x h1 h2 IHh /and4P[L1 L2 H1 H2];
rewrite path_sortedE ?IHh ?all_count -?count_predT -?fromheap_spec1 ?merge_spec ?merge_HO_inv //.
- by rewrite (allE _ _ (LE_spec _ _ H1 L1)) (allE _ _ (LE_spec _ _ H2 L2)) !size_count // eq_refl.
by exact le_trans.
Qed.

Definition heapsort s := fromheap (fromseq s).

Theorem sorted_heapsort s : (sorted <=%O (heapsort s)).
Proof. by rewrite fromheap_spec2 // heap_ordered_fromseq. Qed.

Lemma count_heapsort s : seq.count^~ (heapsort s) =1 seq.count^~ s.
Proof. move=> p. by rewrite /heapsort -fromheap_spec1 fromseq_cspec. Qed.

Theorem perm_heapsort s : perm_eql (heapsort s) s.
Proof. apply/permPl/permP; by apply: count_heapsort. Qed.
End Heapsort.
End Measure.

Definition rank_measureMixin : Measure.mixin_of rank := Measure.Mixin T rank 1%N f1 rankNode rank__NodexEE rank_Node_E.
Canonical rank_measureType : measureType T := Measure.Pack T rank rank_measureMixin.

Definition size_measureMixin : Measure.mixin_of size := Measure.Mixin T size 1%N f2 sizeNode size__NodexEE size_Node_E.
Canonical size_measureType : measureType T := Measure.Pack T size size_measureMixin.

Definition leftist_rank_inv := (leftist_measure_inv rank_measureType).
Definition case_leftist_rank_inv := (case_leftist_measure_inv rank_measureType).
Definition case_leftist_rank_inv_r := (case_leftist_measure_inv_r rank_measureType).
Definition case_leftist_rank_inv_rl := (case_leftist_measure_inv_rl rank_measureType).

Section Grank.

(** The (general) rank of a tree is the length of the shortest path from the root to leaves *)
Fixpoint grank h : nat :=
  if h is Node _ _ tl tr then
    (minn (grank tl) (grank tr)).+1
  else 0.

Theorem grank_rk h : leftist_rank_inv  h -> grank h = rank h.
Proof.
elim: h=> // ??? IHh1 ? IHh2 /case_leftist_rank_inv/andP[].
rewrite /f/=/f1=>_ /and3P[??].
by rewrite IHh1 // IHh2 // minnC ?Order.NatOrder.minnE=> ->.
Qed.

End Grank.

(* We can obtain that right spine is the shoterst for heaps with *)
(* rank measure                                                  *)
Section Spine.

Lemma length_right_spine h s:
leftist_rank_inv h -> right s -> spine_in s h -> length s = rank h.
Proof.
move=> /andP[_ RC]. elim: h s RC=>[[|[]]|????? IHtr [_ _|[?/=/and3P[_ *]|]]] //.
apply/eqnP=> /=; apply/eqP. by apply: IHtr.
Qed.

Theorem rigth_spine_shortest H s1 s2:
 right s1 -> leftist_rank_inv H -> spine_in s1 H -> spine_in s2 H ->
(length s1 <= length s2)%nat.
Proof. 
elim: H s1 s2=> [????/spine_in_E->|?? tl IHtl tr IHtr [//|a s1 [??? 
|[] s2 /rigth_correct [] ->]]] //= => [? /case_leftist_rank_inv_r ?|
? /case_leftist_rank_inv_rl /and3P[??/=?]]=>*.
- rewrite -addn1 -[(length s2).+1]addn1 leq_add2r IHtr //.
rewrite (length_right_spine tr s1) //. case: (right_spine_ex tl)=> s /andP[*].
suffices: (rank tl <= length s2)%N; first by ssrnatlia.
by rewrite -(length_right_spine tl s) // IHtl.
Qed.
End Spine.
End Specifications.
End leftistheap.