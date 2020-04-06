From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype.
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).

Open Scope order_scope.

Lemma fst_true a b : true || a || b.
Proof.
by apply/orP; left.
Qed.
Hint Resolve fst_true : core.

Lemma snd_true a b : a || true || b.
Proof.
by apply/orP; left; apply/orP; right.
Qed.
Hint Resolve snd_true : core.

Lemma trd_true a b : b || a || true.
Proof.
by apply/orP; right.
Qed.
Hint Resolve trd_true : core.

Lemma lt_le n : (0 < n)%N -> (n <= 0)%N = false.
Proof.
case H : (n <= 0)%N=> //.
by move/leq_trans/(_ H).
Qed.

Lemma leq_1 : forall (a b : nat), (a <= b)%N -> (a.+1 <= b.+1)%N.
Proof. by move=> a b H; ssrnatlia. Qed.


Lemma nlt_gt : forall a b, (a <= b)%N = false -> (b < a)%N.
Proof.
move=> a b /neq0_lt0n. ssrnatlia.
Qed.    

Module leftistheap.
(*Leftist heaps are heap-ordered binary trees that satisfy the
leftist property: the rank of any left child is at least as large as the rank of its
right sibling. The rank of a node is defined to be the length of its right spine
(i.e., the rightmost path from the node in question to an empty node). A simple
consequence of the leftist property is that the right spine of any node is always
the shortest path to an empty node.*)

Section LeftistDef.
Variables (T: ordType).

Hint Resolve lexx : core.

Inductive heap :=
| Emp : heap
| Node : nat -> T-> heap -> heap -> heap.


Definition empty h :=
if h is Emp then true else false.

Theorem emptyP h : reflect (h = Emp) (empty h).
Proof. case h; by constructor. Qed.

Implicit Type h : heap.

Definition LE x h : bool := 
if h is Node n y a b then (x <= y) else true.

Fixpoint heap_ordered h : bool :=
if h is Node n x tl tr then (LE x tl) && (LE x tr) && (heap_ordered tl) && (heap_ordered tr) else true.


Fixpoint rk h : nat := if h is Node _ _ _ b then (rk b).+1 else O.

Fixpoint rank_rk h : bool :=
match h with
| Node n x tl tr => (n == (rk tr).+1) && (rank_rk tl) && (rank_rk tr)
| Emp           => true
end.
  

Fixpoint rank h : nat := if h is Node r _ _ _ then r else O.

Fixpoint leftist_inv h : bool :=
if h is Node n x tl tr then
  (rank tr <= rank tl)%N && (leftist_inv tl) && (leftist_inv tr)
else true.

Lemma rank_correct : forall h, rank_rk h -> rk h = rank h.
Proof. by move=> [] //= n _ tl tr /andP[/andP[/eqP]]. Qed.

Inductive side := r | l.

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

Definition leftist_rank_inv h := leftist_inv h && rank_rk h.


Lemma case_leftist_rank_inv_r n x tl tr :
leftist_rank_inv (Node n x tl tr) -> leftist_rank_inv tr.
Proof.
by rewrite /leftist_rank_inv /= => /andP[/andP[/andP[_ _ -> /andP[_]]]].
Qed.

Lemma case_leftist_rank_inv_rl n x tl tr:
leftist_rank_inv (Node n x tl tr) -> 
leftist_rank_inv tr && leftist_rank_inv tl && (rank tr <= rank tl)%N.
Proof.
rewrite /leftist_rank_inv=> /andP[] /=;
by move=> /andP[/andP[->->->/andP[/andP[_ ->->]]]].
Qed.

Lemma case_rank_rk n y h1 h2 : 
rank_rk (Node n y h1 h2) -> (n == (rk h2).+1) && (rank_rk h1) && (rank_rk h2).
Proof. by []. Qed.

Lemma case_heap_ordered n y h1 h2 : 
heap_ordered (Node n y h1 h2) ->
LE y h1 && LE y h2 && (heap_ordered h1) && (heap_ordered h2).
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
leftist_inv (Node n y h1 h2) -> ((rank h2 <= rank h1)%N && leftist_inv h1 && leftist_inv h2).
Proof. by []. Qed.

Lemma right_spine_ex : forall h, exists s, Right s && spine_in s h.
Proof.
elim=> [|n s hl _ hr [] s'].
- by exists nil.
by exists (r :: s').
Qed.

Lemma length_right_spine : forall h s, 
leftist_rank_inv h -> Right s -> spine_in s h ->
length s = rank h.
Proof.
move=> h s /andP [] _ RC; move: (RC)=> /rank_correct <-.
elim: h s RC=> 
[[|[]]|n x tl IHhl tr IHtr [_ _|[s /= /andP[/andP[_ RRl RRr]] |]]] //= R S.
apply/eqnP=> /=. apply/eqP. by apply: IHtr.
Qed.

Lemma spine_in_E s : spine_in s Emp -> s = [::].
Proof. by case: s=> [|[]] //=. Qed.

Theorem rigth_spine_shortest : 
forall H s1 s2, Right s1 -> leftist_rank_inv H -> spine_in s1 H -> spine_in s2 H ->
(length s1 <= length s2)%nat.
Proof. 
elim=>
[s1 s2 _ _ /spine_in_E->|
n x tl IHtl tr IHtr [//|
a s1 [/rigth_correct [] -> _ _ _ |[]
s2 /rigth_correct [] ->]]] //= => [Rs1 /case_leftist_rank_inv_r LI|
Rs1 /case_leftist_rank_inv_rl /andP[/andP[LI1 LI2 LE]]] => SI1 SI2.
- apply: leq_1; apply IHtr=> //.
rewrite (length_right_spine tr s1) //.
case: (right_spine_ex tl)=> s /andP [] Rs SIstl.
suffices: (rank tl <= length s2)%N. ssrnatlia.
rewrite -(length_right_spine tl s) //.
by apply: IHtl.
Qed.

Definition makeT (x : T) (a b : heap) : heap :=
if (rank b <= rank a)%N then Node (rank b).+1 x a b else Node (rank a).+1 x b a.

Lemma makeT_preserves_LI_inv : forall x tl tr,
leftist_inv tl -> leftist_inv tr ->
leftist_inv (makeT x tl tr).
Proof.
  rewrite /makeT=> x tl tr; case H : (rank tr <= rank tl)%N=> /=->->.
  - by rewrite H.
  move: H=> /nlt_gt H. apply/andP; split=> //; apply/andP; split=>//. by ssrnatlia.
Qed.

Lemma makeT_preserves_rk_inv x tl tr :
rank_rk tl -> rank_rk tr ->
rank_rk (makeT x tl tr).
Proof.
move=> Rl Rr; rewrite /makeT -!(rank_correct _ Rl) -!(rank_correct _ Rr).
by case H : (rk tr <= rk tl)%N=> /=; rewrite Rl Rr eq_refl.
Qed.

Lemma makeT_peserves_HO_inv x tl tr :
heap_ordered tl -> heap_ordered tr ->
LE x tl -> LE x tr ->
heap_ordered (makeT x tl tr).
Proof.
by rewrite /makeT; case H : (rank tr <= rank tl)%N=> /=->->->->.
Qed.

Fixpoint member x h :=
if h is Node _ y a b then (x == y) || (member x a) || (member x b) else false.

Notation "x ? h" := (member x h) (at level 0).

Definition leftistheap h :=
leftist_inv h && rank_rk h && heap_ordered h.

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
Hint Rewrite merge_E_h.

Lemma merge_h_E: forall h, merge h Emp = h.
Proof. by case. Qed.
Hint Rewrite merge_h_E.

Lemma rank_rk_r n x tl tr:
rank_rk (Node n x tl tr) -> rank_rk tr.
Proof. by move=> /andP[/andP[]]. Qed.

Lemma rank_rk_l n x tl tr :
rank_rk (Node n x tl tr) -> rank_rk tl.
Proof. by move=> /andP[/andP[]]. Qed.

Lemma merge_a nl nr x y tll tlr trr trl :
(x <= y) = false -> 
merge (Node nl x tll tlr) (Node nr y trl trr) = 
makeT y trl (merge  (Node nl x tll tlr) trr).
Proof.
move=> /= ->.
by elim: trr.
Qed.

Hint Rewrite merge_a.
Lemma merge_preserve_rk_inv : forall h1 h2,
rank_rk h1 -> rank_rk h2 -> rank_rk (merge h1 h2) .
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr] //.
case H : (x <= y)=> H1 H2; merge_cases;
move: (H1) (H2) => /case_rank_rk /andP[/andP[_ HH1 HH2]] /case_rank_rk /andP[/andP[_ HH3 HH4]];
apply: makeT_preserves_rk_inv=> //.
- by apply: IHhr.
by apply: IH'hr.
Qed.

Lemma case_heap_ordered_l n x tl tr :
heap_ordered (Node n x tl tr) -> (heap_ordered tl && LE x tl).
Proof. by move=> /= /andP[/andP[/andP[-> _ ->]]]. Qed.

Lemma case_heap_ordered_r n x tl tr :
heap_ordered (Node n x tl tr) -> (heap_ordered tr && LE x tr).
Proof. by move=> /= /andP[/andP[/andP[_ -> _ ->]]]. Qed.

Lemma case_LE x y n tr tl :
LE x (Node n y tl tr) -> x <= y.
Proof. by []. Qed.

Ltac makeT_cases := match goal with
| H : (?a <= ?b)%N = _ |- _ => rewrite /makeT; move : H => /= ->
end.

Ltac makeT_casesxy x y := case fresh : (x <= y)%N; makeT_cases.

Lemma merge_preserve_LE : forall h1 h2 x,
LE x h1 -> LE x h2 -> LE x (merge h1 h2).
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr x' /case_LE HH1 /case_LE HH2] //.
by merge_casesxy x y; 
[makeT_casesxy (rank (merge tlr (Node nr y trl trr))) (rank tll)|
  makeT_casesxy (rank (merge (Node nl x tll tlr) trr)) (rank trl)].
Qed.

Lemma merge_preserve_HO_inv : forall h1 h2,
heap_ordered h1 -> heap_ordered h2 -> heap_ordered (merge h1 h2).
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr H1 H2] //.
move : (H1) (H2)=>
        /case_heap_ordered /andP[/andP[/andP[L1 L2 HH1 HH2]]]
        /case_heap_ordered /andP[/andP[/andP[L'1 L'2 HH'1 HH'2]]] //;
merge_casesxy x y; apply makeT_peserves_HO_inv=> //.
1 : apply: IHhr=> //.
2 : apply: IH'hr=> //.
all : apply: merge_preserve_LE=> //=.
move: (negbT H).
by rewrite -ltNge lt_def=> /andP[_ ->].
Qed.

Lemma case_leftist_inv_l n x tl tr : leftist_inv (Node n x tl tr) -> leftist_inv tl.
Proof. by move=> /andP[/andP[]].  Qed.

Lemma case_leftist_inv_r n x tl tr : leftist_inv (Node n x tl tr) -> leftist_inv tr.
Proof. by move=> /andP[/andP[]].  Qed.

Lemma merge_preserve_LI_inv : forall h1 h2,
leftist_inv h1 -> leftist_inv h2 -> leftist_inv (merge h1 h2).
Proof.
elim=> [//| nl x tll IHhl tlr IHhr].
elim=> [|nr y trl IH'hl trr IH'hr H1 H2] //.
move : (H1) (H2) =>  /andP[/andP[_ HH1 HH2]] /andP[/andP[_ HH'1 HH'2]].
merge_casesxy x y; apply: makeT_preserves_LI_inv=> //.
- by apply: IHhr.
by apply: IH'hr.
Qed.    

Theorem merge_preserve_LH h1 h2 :
leftistheap h1 -> leftistheap h2 -> leftistheap (merge h1 h2).
Proof.
move=> /andP[/andP[LI1 RR1 HO1]] /andP[/andP[LI2 RR2 HO2]]; apply/andP; split.
- apply/andP; split.
- by apply: merge_preserve_LI_inv.
- by apply: merge_preserve_rk_inv.
by apply: merge_preserve_HO_inv. 
Qed.

Lemma case_member : forall x y n tl tr,
x ? (Node n y tl tr) <-> (x == y) || (x ? tl) || (x ? tr).
Proof. by []. Qed.

Lemma makeT_spec h1 h2 x y :
x ? (makeT y h1 h2) = ((x == y) || (x ? h1) || (x ? h2)).
Proof.
makeT_casesxy (rank h2) (rank h1).
apply/idP/idP => /case_member // [|[]].
by apply/idP/idP => /= /orP[/orP[]|]->.
Qed.

Theorem merge_spec  h1 h2 x :
x ? (merge h1 h2) = ((x ? h1) || (x ? h2)).
Proof.
apply/idP/idP.
- elim: h1 h2=> [h2|n y h1 IHh1 h2 IHh2].
- by rewrite merge_E_h=>->.
- elim=> [|m z h21 IHh21 h22 IHh22]; first by rewrite merge_h_E=>->.
- merge_casesxy y z; rewrite makeT_spec=> /orP[->|] //.
- by move=> /IHh2 /= /orP[] ->.
- move=> /IHh22 /= /orP[] -> //. apply/orP; by right.

- elim: h1 h2 => [h |n y h11 IHh1 h22 IHh2]; rewrite ?merge_E_h //.
- elim=> [/orP [] //|m z h12 IHh12 h21 IHh21]; rewrite ?merge_h_E.
merge_casesxy y z; move=> /orP[/orP[/orP[]|]|/orP[/orP[]|]]; rewrite makeT_spec.
1,2: by move=>->.
1-4: move=> HH; apply/orP; right=> /=; apply/ IHh2; rewrite /= HH //.
1-3: apply/orP; by right.
1-3,6: move=> HH; apply/orP; right=> /=; apply/ IHh21; rewrite /= HH //.
- apply/orP; by left.
1-2: by move=>->.
Qed.

Definition insert (x : T) (h : heap) := 
merge (Node 1 x Emp Emp) h.

Lemma rk_E : ((rk Emp).+1 = 1)%N.
Proof. by []. Qed.    

Lemma insert_preserve_rk_inv : forall h x,
rank_rk h -> rank_rk (insert x h).
Proof.
by move=> h x Rh; apply merge_preserve_rk_inv.
Qed.

Lemma insert_preserve_HO_inv : forall h x,
heap_ordered h -> heap_ordered (insert x h).
Proof.
by move=> h x Rh; apply merge_preserve_HO_inv.
Qed.

Lemma insert_preserve_LI_inv : forall h x,
leftist_inv h -> leftist_inv (insert x h).
Proof.
by move=> h x Rh; apply merge_preserve_LI_inv.
Qed.

Theorem insert_preserve_LH : forall h x,
leftistheap h -> leftistheap (insert x h).
Proof.
by move=> h x Rh; apply merge_preserve_LH.
Qed.


Theorem insert_correct h x y :
x ? (insert y h) = ((x == y) || (x ? h)).
Proof.
rewrite merge_spec /=; case (x == y); by case (x ? h).
Qed.

Definition findmin h := 
if h is Node _ x _ _ then Some x else None.

Theorem findmin_correct1 : forall h,
None = findmin h <-> h = Emp.
Proof. split=> [|-> //]. by case : h. Qed.

Lemma LE_correct : forall h x y,
heap_ordered h -> x ? h -> LE y h -> y <= x.
Proof.
elim=> [x y _ H| n x h1 IHh1 h2 IHh2 x' y' /= /andP[/andP[/andP[L1 L2 H1 H2]]]] //
 /orP[/orP[/eqP ->|/(IHh1 _ _ H1)/(_ L1)]|/(IHh2 _ _ H2)/(_ L2)] //; swapg; exact: le_trans.
Qed.

Theorem findmin_correct2 : forall h, heap_ordered h ->
forall z, Some z = findmin h -> forall x, x ? h -> z <= x.
Proof.
case=> [//| n x h1 h2 HO z /= [->] y /orP[/orP[/eqP ->|]|]] // H. 
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
(x ? h && LE x h) <-> (Some x = findmin h).
Proof.
split=> [/andP[]|]; move: h H=> [] //.
- move=> n y h1 h2 /= /andP[/andP[/andP[L1 L2 H1 H2]]]
  /orP[/orP[/eqP-> //|/(LE_correct _ _ _ H1)/(_ L1)]|/(LE_correct _ _ _ H2)/(_ L2)] XY YX;
  suffices: x = y=> [-> //|]; apply: le_anti; rewrite XY YX //.
move=> n s h1 h2 HO [] ->; apply/andP; split=> /=. 
- by rewrite eq_refl.
by apply lexx.
Qed.

Definition deletemin h :=
if h is Node _ _ a b then merge a b else Emp.

Lemma rank_rk_eq n x h1 h2 :
rank_rk (Node n x h1 h2) -> n = (rk h2).+1.
Proof. by move=> /andP[/andP[/eqP]]. Qed.

Lemma case_LE' x y h1 h2 n :
LE x (Node n y h1 h2) -> ((x <= y) = true).
Proof. by move=> /= ->. Qed.

Lemma rk1 : forall m y h1 h2,
(1 <= rk (Node m y h1 h2))%N.
Proof. move=> m y h1 h2 /=. ssrnatlia. Qed.

Lemma rank1 : forall m y h1 h2,
rank_rk (Node m y h1 h2) -> (1 <= rank (Node m y h1 h2))%N.
Proof. move=> m y h1 h2 /rank_correct <-. by apply rk1. Qed.

Lemma rk0: rk Emp = 0.
Proof. by []. Qed.

Lemma rank0: rank Emp = 0.
Proof. by []. Qed.

Lemma case_leftistheap_l n x h1 h2 :
leftistheap (Node n x h1 h2) -> leftistheap h1.
Proof.
by rewrite /leftistheap => /andP[/andP[/case_leftist_inv_l-> /rank_rk_l-> /case_heap_ordered_l /andP[-> _]]].
Qed.

Lemma case_leftistheap_r n x h1 h2 :
leftistheap (Node n x h1 h2) -> leftistheap h2.
Proof. 
by rewrite /leftistheap => /andP[/andP[/case_leftist_inv_r-> /rank_rk_r-> /case_heap_ordered_r /andP[-> _]]].
Qed.

Lemma deletemin_preserve_rk_inv : forall h, 
rank_rk h -> rank_rk (deletemin h).
Proof.
by case=> //=n x h1 h2 H; apply merge_preserve_rk_inv; move: H=> /andP[/andP[]].
Qed.

Lemma deletemin_preserve_HO_inv : forall h, 
heap_ordered h -> heap_ordered (deletemin h).
Proof.
by case=> //=n x h1 h2 H; apply merge_preserve_HO_inv; move: H=> /andP[/andP[]].
Qed.

Lemma deletemin_preserve_LI_inv : forall h, 
leftist_inv h -> leftist_inv (deletemin h).
Proof.
by case=> //=n x h1 h2 H; apply merge_preserve_LI_inv; move: H=> /andP[/andP[]].
Qed.

Lemma deletemin_correct : forall h, 
leftistheap h -> leftistheap (deletemin h).
Proof.
case=> //=n x h1 h2 H; apply merge_preserve_LH; move: H.
- by move/case_leftistheap_l.
by move/case_leftistheap_r.
Qed.

Theorem deletemin_spec : forall h x y,
Some x = findmin h -> (y ? (insert x (deletemin h))) = y ? h.
Proof.
case=> [//=|n x h1 h2 y z [->]].
by rewrite insert_correct /deletemin merge_spec //= orbA.
Qed.

Fixpoint insert' (x : T) (h : heap) :=
if h is Node n y a b then
let h' := Node n y a b in 
  if x <= y then
    Node 1 x h' Emp
  else makeT y a (insert' x b)
else Node 1 x Emp Emp.

Theorem insertE x h : rank_rk h -> leftist_inv h -> insert' x h = insert x h.
Proof.
rewrite /insert.
elim h=> [//|n y h1 IHh1 h2 IHh2 RR]; move : RR (RR)=> /rank1.
case H : (x <= y); merge_cases. rewrite /makeT => /lt_le -> //.
move=> _ /andP[/andP[nr RR1 RR2]] /andP[/andP[LI1 LI2 rr]].
by rewrite IHh2.
Qed.

End LeftistDef.
End leftistheap.
Module WBleftistheap.
(*Weight-biased leftist heaps are an al-
ternative to leftist heaps that replace the leftist property with the weight-biased
leftist property: the size of any left child is at least as large as the size of its
right sibling.*)
Section WBLeftistDef.
Variables (T: ordType).

Inductive heap :=
| Emp : heap
| Node : nat -> T-> heap -> heap -> heap.
Print negbT.
Fixpoint rank (H : heap) : nat :=
if H is Node r _ _ _ then r else O.

Definition makeT (x : T) (a b : heap) : heap :=
if rank a >= rank b then 
Node ((rank b) + (rank a) + 1) x a b
else Node ((rank b) + (rank a) + 1) x b a.

Fixpoint size (h : heap) : nat :=
if h is Node _ _ a b then (size b) + (size a) + 1 else O.

Definition isEmpty (h : heap) :=
if h is Emp then true else false.


Program Fixpoint merge (a b : heap) {measure (size a + size b)} : heap :=
match a, b with
| h, Emp => h
| Emp, h => h
| Node n x a1 b1, Node m y a2 b2 =>
let h1 := Node n x a1 b1 in
let h2 := Node m y a2 b2 in
if leq x y then
  makeT x a1 (merge b1 h2)
else
  makeT y a2 (merge h1 b2)
end.
Solve All Obligations with (move=> /=; rewrite -!plusE; lia).
Next Obligation.
move=> /=;
rewrite -!plusE; lia.
Qed.
Next Obligation.
move=> /=;
rewrite -!plusE; lia.
Qed.

Definition insert (x : T) (h : heap) := 
        merge (Node 1 x Emp Emp) h.

Definition findmin (h : heap) := 
if h is Node _ x _ _ then Some x else None.

Definition deletemin (h : heap) :=
if h is Node _ _ a b then merge a b else Emp.

Program Fixpoint merge' (a b : heap) {measure (size a + size b)} : heap :=
match a, b with
| h, Emp => h
| Emp, h => h
| Node w1 x a1 b1, Node w2 y a2 b2 =>
let h1 := Node w1 x a1 b1 in
let h2 := Node w2 y a2 b2 in
if leq x y then
  if size a1 >= (size b1) + w2 then 
    Node (w1 + w2) x a1 (merge' b1 h2)
  else Node (w1 + w2) x (merge' b1 h2) a1
else
  if size a2 >= w1 + size b2 then
    Node (w1 + w2) y a2 (merge' h1 b2)
  else Node (w1 + w2) y (merge' h1 b2) a2
end.
Next Obligation.
move=> /=;
rewrite -!plusE; lia.
Qed.
Next Obligation.
move=> /=;
rewrite -!plusE; lia.
Qed.
Next Obligation.
move=> /=;
rewrite -!plusE; lia.
Qed.
Next Obligation.
move=> /=;
rewrite -!plusE; lia.
Qed.

End WBLeftistDef.
End WBleftistheap.
