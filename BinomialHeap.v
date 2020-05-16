From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype. 
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).
Import Order.NatOrder.
From Equations Require Import Equations.

Open Scope order_scope.

Lemma add_lt_le a b c d: (a < c)%N -> (b <= d)%N -> ((a + b == c + d) = false).
Proof. 
move=> *; have /ltn_eqF// : ((a + b) < (c + d))%N.
by rewrite [a + b]addnC -ltn_subRL -addnBA // ltn_addr.
Qed.

Lemma add_le_lt a b c d: (a <= c)%N -> (b < d)%N -> ((a + b == c + d) = false).
Proof. move=> *. rewrite [a + b]addnC [c + d]addnC. by apply: add_lt_le. Qed.

Module tree.
Section BinomialTree.
Context {T : ordType}.

(* Binomial heaps are composed of more primitive objects known as binomial trees.
   Binomial trees are inductively defined as follows:
   • A binomial tree of rank 0 is a singleton node.
   • A binomial tree of rank r + 1 is formed by linking two binomial trees of
     rank r, making one tree the leftmost child of the other.

   There is a second, equivalent definition of binomial trees that is sometimes
   more convenient: a binomial tree of rank r is a node with r children t_1 ... t_r,
   where each t_i is a binomial tree of rank r — i *)
Inductive tree :=
| Node : T -> list tree -> tree.

Lemma st : seq tree. Proof. exact [::]. Qed.
Hint Resolve st: core.

Implicit Type tr : tree.
Notation "[ x | c ]" := (Node x c).

Fixpoint size tr : nat :=
match tr with [x| l] =>
  let fix binom_list l :=
    if l is trh :: trt then size trh + binom_list trt
    else 0 in (binom_list l).+1
  end.

Lemma sizeE x : (forall h l, size [x | h :: l] = size h + size [x| l]) * (size [x| [::]] = 1)%N.
Proof. by split=> *; rewrite /= ?addnS. Qed.

Lemma binomtree_ind (P : tree -> Prop):
  (forall x, P [x| [::]]) ->
  (forall h l x, P h -> P [x| l] -> P [x| h :: l]) ->
  forall h, P h.
Proof.
move=> Base IH_Hyp h. have [n le_size] := ubnP (size h).
elim: n h le_size => // n IHn [x [] // h t S]; apply: IH_Hyp; apply IHn; move: S=> /=;
case: h=> ??/=; by ssrnatlia.
Qed.

Arguments size : simpl never.

(* here we define decidable equality on trees *)

Fixpoint eqtree tr1 tr2 :=
match tr1, tr2 with [x| l], [y| t] =>
let fix binom_list l t :=
  match l, t with
  | h1 :: t1, h2 :: t2 => (eqtree h1 h2) && (binom_list t1 t2)
  | [::], [::]         => true
  | _, _               => false
  end in (x == y) && (binom_list l t)
end.

Lemma eqtreeE' x l h y t h': 
  (eqtree [x| h :: l] [y| h' :: t] = ((eqtree [x| l] [y| t]) && (eqtree h h'))).
Proof.  move=> /=. case: (x == y)=> //=. by rewrite andbC. Qed.

Lemma eqtree_refl h: eqtree h h.
Proof.
elim/binomtree_ind: h=> [/=*|???]; by rewrite ?eq_refl // eqtreeE'=>->->.
Qed.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
move=> tr1 tr2. apply/Bool.iff_reflect.
elim/binomtree_ind: tr1 tr2=> [?[?[]/=]|??? IH1 IH2[?[]]]; rewrite ?andbT ?andbF //.
- split=> [[->]|/eqP->] //; by rewrite eq_refl.
- split=> //=; by rewrite andbF.
move=>*; rewrite eqtreeE'; split=> [[->->->]|/andP[/IH2[->->/IH1->]]]; 
by rewrite // ?eqtree_refl.
Qed.

Canonical tree_eqMixin := EqMixin eqtreeP.
Canonical tree_eqType := Eval hnf in EqType tree tree_eqMixin.

Lemma eqtreeE : eqtree = eq_op. Proof. by []. Qed.


(* Here we defins some invariants for binomial trees:
   - binimtree_of_rk tr rk == tr is binomial tree of rank rk
   - heap_ordered tr  == tr is heap ordered *)
Fixpoint binom_of_rk (rk : nat) (tr : tree) := 
match tr, rk with
| [x| trh :: trt], rk'.+1 => binom_of_rk rk' trh && binom_of_rk rk' [x| trt]
| [x| [::]],       0      => true
| _,               _      => false
end.

Lemma rk_singl x rk : binom_of_rk rk [x | [::]] -> rk = 0.
Proof. by case: rk. Qed.

Theorem binomtree_size rk tr : binom_of_rk rk tr -> size tr = 2 ^ rk.
Proof.
elim/binomtree_ind: tr rk=> [x rk /rk_singl ->|]//=??? IHtr1 IHtr2 []//= rk /andP[*].
rewrite sizeE /= (IHtr1 rk) // (IHtr2 rk) // expnS. by ssrnatlia.
Qed.

Lemma binomtree_of_rk_0 x l: binom_of_rk 0 [x | l] -> l = [::].
Proof. by case: l. Qed.


Fixpoint heap_ordered tr : bool :=
  match tr with [x| l] =>
    let fix binom_list l :=
      if l is ([y| trtt] as trh) :: trt then
        (x <= y) && heap_ordered trh && binom_list trt
      else true in binom_list l
    end.

Lemma heap_orderedE x y t l: 
  ((heap_ordered [x| [y| t] :: l] = [&& (x <= y), (heap_ordered [y| t]) & (heap_ordered [x| l])]) *
  (heap_ordered [x| [::]])).
Proof. move=> /=; by case: (x <= y). Qed.


Lemma heap_ordered_nodes x ts: heap_ordered [x| ts] -> 
  all heap_ordered ts.
Proof.
elim: ts=> // [[??? IHts]]. by rewrite heap_orderedE=> /and3P[/= _ -> /IHts].
Qed.

Arguments heap_ordered : simpl never.



Fixpoint count (a : pred T) tr : nat := 
  match tr with [x| l] =>
  let fix binom_list l :=
    if l is trh :: trt then
        count a trh + binom_list trt
    else 0 in (a x) + binom_list l
  end.

Lemma countE a x: 
  (forall tr l, count a [x| tr :: l] = count a [x| l] + count a tr) *
  (count a [x| [::]] = a x).
Proof. split=> /= *; first by ssrnatlia. by rewrite addn0. Qed.

Arguments count : simpl never.

Definition mem_tree tr := fun x => (0 < count (pred1 x) tr)%N.

Definition tree_eqclass := tree.
Identity Coercion tree_of_eqclass : tree_eqclass >-> tree.
Coercion pred_of_tree (h : tree_eqclass) : {pred T} := mem_tree h.

Canonical tree_predType := PredType pred_of_tree.
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_tree_predType := PredType mem_tree.

Lemma inE x y: 
  (forall tr l, (x \in [y| tr :: l] = (x \in [y| l]) || (x \in tr)) *
  (x \in [y| [::]] = (x == y)) * (forall l, x \in [x| l]))%type.
Proof.
split=> *.
- split=> *; rewrite /in_mem /= /mem_tree !countE ?addn_gt0 //= 1?eq_sym. by case (x==y).
by rewrite /in_mem /= /mem_tree /count /= eq_refl.
Qed.

Definition all a tr := (count a tr == size tr).

Lemma count_le_size a tr: (count a tr <= size tr)%N.
Proof.
elim/binomtree_ind: tr=> x *; rewrite ?countE sizeE; first by case: (a x).
by rewrite addnC leq_add.
Qed.

Lemma allE a x tr l: ((all a [x| [::]] = a x) *
(all a [x| tr :: l] = all a [x| l] && all a tr))%type.
Proof.
rewrite /all !countE // !sizeE //; split; first by case: a.
have := (count_le_size a tr); have := (count_le_size a [x| l]).
rewrite leq_eqVlt addnC=> /orP[/eqP->|C /add_le_lt/(_ C)->];
last by move: C=> /ltn_eqF->. rewrite leq_eqVlt=> /orP[/eqP->|/ltn_eqF];
by rewrite ?eq_refl // eqn_add2r=>->.
Qed.

Lemma in_all tr a x: x \in tr -> all a tr -> a x.
Proof.
elim/binomtree_ind: tr=> [?|??? IHtr1 IHtr2]; rewrite inE ?allE //;
first by move/eqP->. by move=> /orP[H /andP[/(IHtr2 H)]|H /andP[_ /(IHtr1 H)]].
Qed.

Lemma all_le z x tr : (x <= z) -> all (>= z) tr -> all (>= x) tr.
Proof.
move=> xz. elim/binomtree_ind: tr => [?| ??? IH1 IH2]; rewrite ?allE //; 
first by move => /(le_trans xz). move=> /andP[*]; by rewrite IH1 // IH2.
Qed.

Lemma ho_t_min y l: heap_ordered [y| l] -> all (>= y) [y| l].
Proof.
move: {-2}[y| l] (@erefl _ [y| l])=> t; move: t y l.
elim/binomtree_ind=> [???[->]|[z t l x IHh1 IHh2 ?? [<- ? ]]]; 
rewrite allE // heap_orderedE=> /and3P[xz *];
rewrite (IHh2 x l) //=. have: (all (>= z) [z| t]); first by rewrite (IHh1 z t).
by apply: all_le.
Qed.

Lemma size_tree_pos tr: (0 < count predT tr)%coq_nat.
Proof.
elim/binomtree_ind: tr=>*; rewrite countE //.
by apply: Plus.lt_plus_trans.
Qed.


(* Here we define link function. It can construct one binomial tree of rank
   r + 1 taking two trees with rank r
   Each list of children is maintained in decreasing order of rank,
   and elements are stored in heap order. We maintain heap order by always
   linking trees with larger roots under trees with smaller roots. *)
Definition link (t1 t2 : tree) : tree :=
  match t1, t2 with 
  | [x1| c1], [x2| c2] =>
  if x1 <= x2 then 
    [x1| (t2 :: c1)]
  else [x2| (t1 :: c2)]
end.

Lemma link_ho_inv tr1 tr2 : heap_ordered tr1 -> heap_ordered tr2 ->
  heap_ordered (link tr1 tr2).
Proof.
  case: tr1 tr2=>??[??/=]. case: ifP; rewrite heap_orderedE; by case: ltgtP=> ?? ->->.
Qed.

Lemma link_binom_inv rk tr1 tr2: 
  binom_of_rk rk tr1 -> binom_of_rk rk tr2 -> binom_of_rk rk.+1 (link tr1 tr2).
Proof. case: tr1 tr2=>??[??/=]. by case: ifP=> _->->. Qed.

Lemma link_spec a tr1 tr2: count a (link tr1 tr2) = count a tr1 + count a tr2.
Proof. case: tr1 tr2=> ??[??/=]; case: ifP; by rewrite countE // addnC. Qed.

End BinomialTree.
End tree.

Notation tree := tree.tree.
Notation link := tree.link.
Notation binom_of_rk := tree.binom_of_rk.
Notation "[ x | c ]" := (tree.Node x c).
Notation link_binom_inv := tree.link_binom_inv.
Notation link_ho_inv := tree.link_ho_inv.

Arguments tree.heap_ordered : simpl never.
Arguments tree.count : simpl never.

Canonical tree_eqMixin T := EqMixin (@tree.eqtreeP T).
Canonical tree_eqType T := Eval hnf in EqType tree (@tree_eqMixin T).

Identity Coercion tree_of_eqclass : tree.tree_eqclass >-> tree.
Coercion pred_of_tree (T : ordType) (h : tree.tree_eqclass) : {pred T} := (@tree.mem_tree T) h.

Canonical tree_predType T := PredType (pred_of_tree T).
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_tree_predType T := PredType (@tree.mem_tree T).

Section BinomialHeap.
Variables (T : ordType).
Implicit Type tr : @tree T.

(* Binomial heap is a collection of heap-ordered binomial trees in which
   no two trees have the same rank. This collection is represented as a
   list of trees and their rank in increasing order of rank. *)
Definition heap := seq (nat * (@tree T)).

Definition rank_ord (le : rel nat) (ntr1 ntr2 : nat * (@tree T)) : bool :=
  le ntr1.1 ntr2.1.

Implicit Type h : heap.

Definition rank_sorted h    := sorted (rank_ord (fun n m => (n < m)%N)) h.
Definition heap_ordered h   := all (tree.heap_ordered \o snd) h.
Definition binomial_pair ph := @binom_of_rk T ph.1 ph.2.
Definition all_trees_binomial h  := all binomial_pair h.
Definition binomial_heap h := 
  [&& (rank_sorted h), (all_trees_binomial h) & (heap_ordered h)].

Lemma rank_sorted_E: rank_sorted [::].
Proof. by []. Qed.

Lemma rank_sorted1 x : rank_sorted [:: (0%N, [x| [::]])].
Proof. by []. Qed.

Lemma heap_ordered_E: heap_ordered [::].
Proof. by []. Qed.

Lemma heap_ordered1 x : heap_ordered [:: (0%N, [x| [::]])].
Proof. by []. Qed.

Lemma all_trees_binomial_E: all_trees_binomial [::].
Proof. by []. Qed.

Lemma all_trees_binomial1 x : all_trees_binomial [:: (0%N, [x| [::]])].
Proof. by []. Qed.

Lemma binomial_heap_E: binomial_heap [::].
Proof. by []. Qed.

Lemma binomial_heap1 x: binomial_heap [:: (0%N, [x| [::]])].
Proof. by []. Qed.

Definition all_trees_binomial_rk h := ((rank_sorted h) && (all_trees_binomial h)).

Lemma all_trees_binomial_rk1 x : all_trees_binomial_rk [:: (0%N, [x| [::]])].
Proof. by []. Qed.

Lemma all_trees_binomial_rk_E : all_trees_binomial_rk [::].
Proof. by []. Qed.

Fixpoint count (a : pred T) h : nat :=
  if h is (_, th) :: t then tree.count a th + count a t
  else 0.

Lemma count_cat hs1 hs2 a: count a (hs1 ++ hs2) = count a hs1 + count a hs2 .
Proof. elim: hs1=> // [[/=???->]]; by ssrnatlia. Qed.


(* Here we define some casual fuctions like \in, count etc. *)
Fixpoint eqheap h1 h2 := 
match h1, h2 with
| (rk, tr) :: t, (rk', tr') :: t' => [&& (rk == rk'), (tr == tr') & (eqheap t t')]
| [::], [::]                      => true
| _, _                            => false
end.

Lemma eqheapP : Equality.axiom eqheap.
Proof.
elim=> [[]/=|[??? IH []]]; try by constructor.
move=> [?? l]. apply/Bool.iff_reflect=>/=. 
split=> [[->->->]|/and3P[/eqP->/eqP->/IH->]]; rewrite // ?eq_refl/=.
elim: l=> //= [[???->]]; by rewrite ?eq_refl.
Qed.

Canonical heap_eqMixin := EqMixin eqheapP.
Canonical heap_eqType := Eval hnf in EqType heap heap_eqMixin.

Lemma eqheapE : eqheap = eq_op. Proof. by []. Qed.


Fixpoint mem_heap h := 
if h is (_, tr) :: ttt then xpredU (fun x => x \in tr) (mem_heap ttt) else xpred0.

Definition heap_eqclass := heap.
Identity Coercion heap_of_eqclass : heap_eqclass >-> heap.
Coercion pred_of_heap (h : heap_eqclass) : {pred T} := mem_heap h.

Canonical heap_predType := PredType pred_of_heap.
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_heap_predType := PredType mem_heap.

Definition consh : nat * tree -> heap -> heap := cons.

Lemma inE (x : T): 
  ((forall rk tr h, x \in (consh (rk, tr) h) = (x \in h) || (x \in tr)) *
  ((x \in [::]) = false))%type.
Proof. split=> *; rewrite /in_mem //= /in_mem /= orbC //. Qed.

Lemma int_conut x h: x \in h = (0 < count (pred1 x) h)%N.
Proof.
elim: h=> //= [[???]]; rewrite inE=>->. 
by rewrite /in_mem/=/tree.mem_tree -addn_gt0 addnC.
Qed.

Fixpoint all a h := if h is (_, th) :: t then tree.all a th && all a t else true.

Lemma in_all h a x: x \in h -> all a h -> a x.
Proof.
elim: h=> //= [[??? IHh]]; by
rewrite inE=> /orP[/IHh H /andP[_ /H]|/tree.in_all H /andP[/H]].
Qed.

Lemma all_le z x h : (x <= z) -> all (>= z) h -> all (>= x) h.
Proof.
elim: h x z=> // [[/= _ ?? IHh ? z xz /andP[??]]].
by rewrite (tree.all_le z) // (IHh _ z).
Qed.

Definition size h : nat := count (predT) h.

Definition empty h :=
if h is [::] then true else false.

Theorem emptyP h : reflect (h = [::]) (empty h).
Proof. case h; by constructor. Qed.

(* We are now ready to describe the functions on binomial heaps.
   We begin with insert and merge, which are defined in loose analogy
   to incrementing or adding binary numbers. *)
Fixpoint instree tr (rk : nat) h :=
  if h is (rk', tr') :: ts then
    if (rk < rk')%N then (rk, tr) :: h
    else instree (link tr tr') rk.+1 ts
  else [:: (rk, tr)].

Definition insertable rk h :=
  if h is trp :: th then (rk <= trp.1)%N else true.

Lemma instree_rk_sort_inv tr rk h: 
  binom_of_rk rk tr -> insertable rk h -> all_trees_binomial h ->
  rank_sorted h -> rank_sorted (instree tr rk h).
Proof.
elim: h rk tr=> // [[rk tr ts IHh rk' tr' /= BT]];
rewrite /rank_ord/= leq_eqVlt => /orP[/eqP EQ|]; case: ifP=> //; first by rewrite EQ ltnn.
- move=> _ /andP[]; move:BT. rewrite EQ /binomial_pair/= => ?? BH P.
  rewrite {}IHh // ?link_binom_inv //= ?/rank_ord;
  by move: ts P BH=> [] //=?? /andP[].
by rewrite /rank_sorted/=/rank_ord=> -> {IHh} _ _=>->. 
Qed.

Lemma instree_ho_inv tr rk h: 
  tree.heap_ordered tr ->
  heap_ordered h -> heap_ordered (instree tr rk h).
Proof.
elim: h rk tr=> /= [??-> //|[??? IHh ??]].
case: ifP => /= [_ -> /andP[->->] //|_ ?/andP[*]]; 
by rewrite IHh ?link_ho_inv.
Qed.

Lemma instree_binomial_inv tr rk h: 
  binom_of_rk rk tr -> insertable rk h -> all_trees_binomial h ->
  rank_sorted h -> all_trees_binomial (instree tr rk h).
Proof.
elim: h rk tr => /= [??|[?? l IHh ?? BT]];
rewrite -/binomial_pair ?andbT //= leq_eqVlt =>/orP[/eqP<-|->/andP[/=->->]];
rewrite ?/binomial_pair (ltnn, BT) // /= => /andP[? Bl Sl].
rewrite IHh // ?link_binom_inv //; 
by move: l {Bl IHh} Sl=> []//= ?? /andP[].
Qed.

Theorem instree_correct tr rk h : 
  binom_of_rk rk tr -> insertable rk h -> tree.heap_ordered tr ->
  binomial_heap h -> binomial_heap (instree tr rk h).
Proof.
move=> ??? /and3P[*]. 
by rewrite /binomial_heap instree_binomial_inv ?instree_ho_inv ?instree_rk_sort_inv.
Qed.

Lemma instree_spec a tr rk h: count a (instree tr rk h) = tree.count a tr + count a h.
Proof.
elim: h tr rk=>//= [[??? IHl *]]. case: ifP;
by rewrite // IHl tree.link_spec addnA.
Qed.

Lemma rank_sort_insertable rk tr l: 
  rank_sorted ((rk, tr) :: l) = insertable rk.+1 l && rank_sorted l.
Proof. by case: l. Qed.

Lemma insertable_instree (rk rk' : nat) tr h: (rk <= rk')%N ->
  insertable rk (instree tr rk' h).
Proof.
elim: h tr rk'=> // [[rk'' ? l IHh ?? /= ?]]. case: ifP=> //. 
rewrite IHh //. by ssrnatlia.
Qed.

(* To insert a new element into a heap, we first create a new singleton
   tree (i.e., a binomial tree of rank 0). We then step through the
   existing trees in increasing order of rank until we find a missing rank,
   linking trees of equal rank as we go.*)
Definition insert x h := instree [x| [::]] 0 h.

Lemma insert_rk_sort_inv x h: 
 rank_sorted h -> all_trees_binomial h -> rank_sorted (insert x h).
Proof. move=> H H'; apply: instree_rk_sort_inv=> //. by case: h {H H'}. Qed.

Lemma insert_ho_inv x h: 
  heap_ordered h -> heap_ordered (insert x h).
Proof.
move=> H; apply: instree_ho_inv; by rewrite // ?heap_orderedE.
Qed.

Lemma insert_binom_inv x h: 
  all_trees_binomial h -> rank_sorted h -> all_trees_binomial (insert x h).
Proof. move=> H H'; apply instree_binomial_inv=> //; by case: h {H H'}. Qed.

Theorem insert_spec a x h : count a (insert x h) = a x + count a h.
Proof. rewrite instree_spec tree.countE //. Qed.

Theorem insert_correct x h: 
 binomial_heap h -> binomial_heap (insert x h).
Proof.
move/and3P=>[*].
by rewrite /binomial_heap insert_rk_sort_inv ?insert_ho_inv ?insert_binom_inv.
Qed.


(* To merge two heaps, we step through both lists of trees in
  increasing order of rank, linking trees of equal rank as we go.*)
Fixpoint merge h1 :=
if h1 is (rk1, trh1) :: trt1 then
let fix merge_h1 h2 :=
  if h2 is (rk2, trh2) :: trt2 then
    if rk1 < rk2 then 
      (rk1, trh1) :: merge trt1 h2
    else if rk2 < rk1 then
      (rk2, trh2) :: merge_h1 trt2
    else instree (link trh1 trh2) rk1.+1 (merge trt1 trt2)
  else h1 in merge_h1
else id.

Lemma merge_h_E h: merge h [::] = h.
Proof. by case: h=> // [[]]. Qed.


Lemma merge_h1 (rk1 rk2 : nat) trh1 trh2 tr1 tr2 trt1 trt2: 
  rk2 < rk1 -> merge ((rk1, trh1) :: trt1) ((rk2, trh2) :: trt2) = 
      (rk2, trh2) :: merge ((rk1, trh1) :: trt1) trt2.
Proof.
move=> RR; have /= ->: rk1 < rk2 = false; move: RR; first by case: ltgtP. by move=>->.
Qed.

Lemma merge_h1'' (rk1 rk2 : nat) trh1 trh2 tr1 tr2 trt1 trt2: 
  rk1 < rk2 -> merge ((rk1, trh1) :: trt1) ((rk2, trh2) :: trt2) = 
      (rk1, trh1) :: merge trt1 ((rk2, trh2) :: trt2).
Proof. by move=> /=->. Qed.

Lemma merge_h1' (rk1 rk2 : nat) trh1 trh2 tr1 tr2 trt1 trt2: 
  rk1 = rk2 -> merge ((rk1, trh1) :: trt1) ((rk2, trh2) :: trt2) = 
  instree (link trh1 trh2) rk1.+1 (merge trt1 trt2).
Proof. move=> /=->. by rewrite ltxx. Qed.

Ltac merge_cases rk1 rk2 := 
have /or3P[||/eqP]: [|| rk1 < rk2, rk1 > rk2 | rk1 == rk2] => [|RR|RR|RR];
first (by case: ltgtP); [rewrite merge_h1'' // |rewrite merge_h1 //|rewrite merge_h1' //].

Arguments merge: simpl never.

Lemma merge_ho_inv h1 h2: heap_ordered h1 -> heap_ordered h2 ->
  heap_ordered (merge h1 h2).
Proof.
elim: h1 h2=> // [[rk1 ? l IHh1]]. elim=> // [[rk2 ? l1 IHh2 H1 H2]].
merge_cases rk1 rk2; move: (H1) (H2)=> /= /andP[Hb Hl /andP[Hb1 Hl1]];
by rewrite ?Hb ?Hb1 ?IHh2 ?instree_ho_inv ?link_ho_inv ?IHh1.
Qed.

Lemma merge_spec h1 h2 a: count a (merge h1 h2) = count a h1 + count a h2.
Proof.
elim: h1 h2=> // [[rk1 ? l IHh1]]. elim=> /= [|[rk2 ? l1 IH2]]; first by rewrite addn0.
merge_cases rk1 rk2; rewrite /= ?IH2 /= ?instree_spec ?IHh1 ?tree.link_spec /=; by ssrnatlia.
Qed.

Lemma insertale_merge h1 h2 rk: insertable rk h1 -> insertable rk h2 ->
   insertable rk (merge h1 h2).
Proof.
case: h1; case: h2=> [*|]; rewrite ?merge_h_E // => [[rk1 ?? [rk2 /= *]]].
merge_cases rk2 rk1; rewrite insertable_instree //. by ssrnatlia.
Qed.

Arguments rank_sorted: simpl never.

Lemma merge_binom_inv h1 h2 :  rank_sorted h1 -> rank_sorted h2 ->
all_trees_binomial h1 -> all_trees_binomial h2 -> all_trees_binomial (merge h1 h2) * rank_sorted (merge h1 h2).
Proof.
elim: h1 h2=> // [[rk1 ? l IHh1]]. elim=> // [[rk2 ? l1 IHh2 RS1 RS2 B B']].
merge_cases rk1 rk2; move: (B) (B'); rewrite /= /binomial_pair /= => /andP[B1 Bl /andP[B2 Bl1]];
move: (RS1) (RS2); rewrite !rank_sort_insertable=> /andP[?? /andP[??]];
by rewrite ?B1 ?B2 ?IHh2 ?instree_binomial_inv ?instree_rk_sort_inv
 ?link_binom_inv ?insertale_merge ?IHh1 ?RR // -?RR.
Qed.

Theorem merge_correct h1 h2: binomial_heap h1 -> binomial_heap h2 ->
 binomial_heap (merge h1 h2).
Proof.
move/and3P=>[???/and3P[*]].
by rewrite /binomial_heap merge_ho_inv ?merge_binom_inv.
Qed.

Lemma merge_binom_inv' h1 h2 : (rank_sorted h1) && (all_trees_binomial h1) ->
(rank_sorted h2) && (all_trees_binomial h2) -> rank_sorted (merge h1 h2) && all_trees_binomial (merge h1 h2).
Proof. move=> /andP[??/andP[??]]. by rewrite ?merge_binom_inv. Qed.

(* Both findMin and deleteMin call an auxiliary function removeMinTree
   that finds the tree with the minimum root and removes it from the list, 
   returning both the tree and the remaining list. *)
Fixpoint removemintree (ts : heap) : option (tree * heap * nat) :=
match ts with
| [::]      => None
| [:: (rk, tr)]     => some (tr, [::], rk)
| (rk, [x| l]) :: ts =>  
              if removemintree ts is some ([x'| l'], ts', rk') then
                if x <= x' then some ([x| l], ts, rk) 
                else some ([x'| l'], (rk, [x| l]) :: ts', rk')
              else None
end.

Lemma removemintree_None (ts : heap): 
  removemintree ts = None <-> ts = [::].
Proof.
elim: ts=> //= [[? [?? []// a l]]].
case: (removemintree (a :: l))=> // [[[[]]]*|[] /(_ erefl) //].
by case: ifP.
Qed.

Lemma removeintree_some {h l h' x rank}: heap_ordered h ->
removemintree h = some ([x| l], h', rank) -> (x \in h) * (all (>= x) h).
Proof.
elim: h x l h' rank=> // [[rk [y ? /= [?????/= /andP[/tree.ho_t_min Ay _ [EQ]]|[r tr t IHh  x ??? /andP[HY HH]]]]]].
- by (move: EQ Ay=> ->->; rewrite inE tree.inE).
move: {-2}(removemintree ((r, tr) :: t)) (@erefl _ (removemintree ((r, tr) :: t)))=> rt.
case: rt=> [[[[???? /esym/(IHh _ _ _ _ HH) [Is As]]]]| /esym/removemintree_None] //.
case: ifP=> ys [Eq Eq1]; move: Eq Eq1 ys Is As HY=> -> _ LE.
- move=> ? /(all_le _ _ _ LE)-> /tree.ho_t_min->. by rewrite inE tree.inE ?orbT.
have xy: (x <= y)=> [|Ix]; first by move: LE; case: ltgtP. 
by rewrite inE Ix=>-> /tree.ho_t_min/(tree.all_le _ _ _ xy)->.
Qed.

Notation sw := (ltac:(move=> A B; move: B A)).

Lemma removemintree_count {h l h' x rank} a: 
  some ([x| l], h', rank) = removemintree h -> 
  count a h' + tree.count a [x| l] = count a h.
Proof.
elim: h x l h' rank=> // [[? [?? /=[?????[->->->_]|[r tr t IHh????]]]]];
first by ssrnatlia.
move: {-2}(removemintree ((r, tr) :: t)) (@erefl _ (removemintree ((r, tr) :: t))) =>
 [[[[???? /IHh/sw]]]|/esym/removemintree_None//].
case: ifP=> [_ [->->->_ /=]| _[->->->_/=<-]]; by ssrnatlia.
Qed.

Arguments subseq !_ !_.

Lemma removemintree_subseq {h l h' x rank}: rank_sorted h ->
  removemintree h = some ([x| l], h', rank) -> subseq h' h.
Proof.
elim: h x l h' rank=> // [[rk [y l /= [??????[??<-//]|[r tr t IHh???? R]]]]].
move: {-2}(removemintree ((r, tr) :: t)) (@erefl _ (removemintree ((r, tr) :: t)))=>
[[[[?? b ? /esym EQ]]]|/esym/removemintree_None//]. move: R.
rewrite /rank_sorted/==> /andP[?/IHh/(_ EQ) /sw]. case: ifP=>? [_ _ <- _];
rewrite ?subseq_cons // -{1}cat1s -[((_, _) :: b)]cat1s.
move=> /(cat_subseq (subseq_refl [:: (rk, [y | l])])). by rewrite ?cat1s.
Qed.

Lemma removemintree_rs_inv {h l h' x rank}: rank_sorted h ->
removemintree h = some ([x| l], h', rank) -> rank_sorted h'.
Proof.
move=> R /(removemintree_subseq R)/subseq_sorted/(_ R). apply=> [[??[??[??]]]].
rewrite /rank_ord/=. by ssrnatlia.
Qed.


Lemma removemintree_binom_inv {h l h' x rank}: all_trees_binomial h ->
  removemintree h = some ([x| l], h', rank) -> (binomial_pair (rank, [x| l])) * (all_trees_binomial h').
Proof.
elim: h x l h' rank=> // [[rk [y ? /= [?????/andP[??[<-<-<-<-//]]|[r tr t IHh???? /andP[? B]]]]]].
move: {-2}(removemintree ((r, tr) :: t)) (@erefl _ (removemintree ((r, tr) :: t)))=>
[[[[???? /esym/(IHh _ _ _ _ B)]]]|/esym/removemintree_None//].
case: ifP => _ [??] [<-<-<-<-] //=. split=> //; by apply/andP; split.
Qed.

Lemma removemintree_ho_inv {h l h' x rank}: heap_ordered h ->
removemintree h = some ([x| l], h', rank) -> (heap_ordered h') * (tree.heap_ordered [x| l]).
Proof.
elim: h x l h' rank=> // [[rk [y ? /= [?????/andP[??[<-<-<-_//]]|[r tr t IHh???? /andP[? H]]]]]].
move: {-2}(removemintree ((r, tr) :: t)) (@erefl _ (removemintree ((r, tr) :: t)))=>
[[[[???? /esym/(IHh _ _ _ _ H)]]]|/esym/removemintree_None//].
case: ifP => _ [??] [<-<-<-_] //=. split=> //; by apply/andP; split.
Qed.

Definition findmin (ts : heap) : option T :=
if (removemintree ts) is some ([x| _], _, _) then some x else None.

Theorem findmin_None h: None = findmin h <-> h = [::].
Proof. 
split=> [|-> //]. rewrite /findmin.
case a : (removemintree h)=> [[[[]]]|] //*. move: a. 
by rewrite removemintree_None.
Qed.

Theorem findmin_spec x h: heap_ordered h -> 
reflect  (Some x = findmin h) ((x \in h) && all (>= x) h).
Proof.
move=> HH; apply: Bool.iff_reflect. split=> [|/andP[]]. 
- elim: h HH=> // [[ rk [y l t IHh HH]]]. rewrite /findmin.
  case H: (removemintree ((rk, [y | l]) :: t))=> [[[[]]]|] // [EQ].
  by move: EQ H=><- /(removeintree_some HH)[-> /=].
rewrite /findmin. case H': (removemintree h)=> [[[[]]]|].
- move: H'=> /(removeintree_some HH) => [[/in_all Is As /in_all/(_ As) sx /Is xs]].
  apply/congr1/le_anti; by rewrite sx xs.
by move: h H' {HH}=> [] // ?? /removemintree_None.
Qed.
  
Fixpoint revh_rank (ts : seq tree) (rk : nat) : heap :=
match ts with
| [::] => [::]
| t :: ts' => (revh_rank ts' rk.-1) ++ [:: (rk.-1, t)]
end.

Lemma revh_rank_rs_binom_inv x l rk: binom_of_rk rk [x| l] ->
  (rank_sorted (revh_rank l rk)) * (all_trees_binomial (revh_rank l rk)).
Proof.
elim: l rk=> // [[?? l IHl []// /= rk /andP[]]].
rewrite /all_trees_binomial all_cat /= {2}/binomial_pair /fst/snd=>->.
case: rk=> [/tree.binomtree_of_rk_0->//|rk {}/IHl[/=]]. 
move=> R. rewrite /all_trees_binomial=>->. move: R.
rewrite /rank_sorted cats1 -[revh_rank _ _]revK -rev_cons rev_sorted
 [sorted _ (rev ((_, _) :: _))]rev_sorted/=. case: l=> //= ??.
by rewrite cats1 rev_rcons /=/rank_ord/= ltnSn.
Qed.

Lemma revh_rank_ho_inv x l rk: tree.heap_ordered [x| l] ->
  heap_ordered (revh_rank l rk).
Proof.
elim: l rk=> //= [[???]]; rewrite tree.heap_orderedE /heap_ordered
  => IHl rk /and3P[?? /(IHl rk.-1)]. rewrite all_cat => ->/=; by rewrite andbT.
Qed.


Definition deletemin h : heap :=
if (removemintree h) is some ([x| ts1], ts2, rk) then
  merge (revh_rank ts1 rk) ts2
else [::].

Lemma deletemin_binomial h : rank_sorted h -> all_trees_binomial h -> 
  (rank_sorted (deletemin h) * all_trees_binomial (deletemin h)).
Proof.
rewrite /deletemin. case H: (removemintree h)=> [[[[x]]]|//]
  /removemintree_rs_inv/(_ H) ? /removemintree_binom_inv/(_ H)[??].
by rewrite ?merge_binom_inv // (revh_rank_rs_binom_inv x).
Qed.

Lemma deletemin_ho_inv h: heap_ordered h -> heap_ordered (deletemin h).
Proof.
rewrite /deletemin. case H: (removemintree h)=> [[[[??? rk]]]|//]
  /removemintree_ho_inv/(_ H)[? /(revh_rank_ho_inv _ _ rk) ?].
by rewrite merge_ho_inv.
Qed.

Theorem deletemin_spec {h x}: 
  Some x = findmin h <-> (count^~ (insert x (deletemin h)) =1 count^~ h).
Proof.
split=> [S a|]; first move: S.
- rewrite insert_spec /deletemin.
  move: {-2}(removemintree h) (@erefl _ (removemintree h))=>
  [[[[? l ? rk R]]]|/esym/removemintree_None->//]. move: (R).
  rewrite /findmin=> <- [->]. move: R=>  /removemintree_count-/(_ a)<-.
  apply/eqP. rewrite merge_spec addnA addnC eqn_add2l; apply/eqP.
  elim: l rk=> //= ?? IHl rh. by rewrite count_cat addnA IHl /= addn0 tree.countE.
move=> H; move: (H (pred1 x)). rewrite insert_spec /= eq_refl.
elim: h x {H}=> //= [[rk [x t /= l IHh]]]. rewrite /deletemin/findmin.
move: {-2}(removemintree ((rk, [x | t]) :: l)) (@erefl _ (removemintree ((rk, [x | t]) :: l)))=>
  [[[[???? /removemintree_count H y]]]|/esym/removemintree_None//].
rewrite merge_spec.
Qed.

Theorem deletemin_correct h: 
  binomial_heap h -> binomial_heap (deletemin h).
Proof.
move/and3P=>[*]; by rewrite /binomial_heap deletemin_ho_inv ?deletemin_binomial.
Qed.


Lemma deletemin_size h : size (deletemin h) = (size h).-1.
Proof.
case H: (findmin h); last by move: H=> /esym/(findmin_None)->.
move: (deletemin_spec predT (esym H)). rewrite /size insert_spec/==><-.
by ssrnatlia.
Qed.

(* In this section we define heapsort and prove it's properties *)
(* heapsort fist translates sequense of elements into heap and  *)
(* than takes the minimal element of the heap while it is not   *)
(* empty                                                        *)
Section Heapsort.
Implicit Type hh : seq (option heap).

Fixpoint seq_to_seqheap (st : seq T) : seq heap :=
if st is h :: t then [:: (0, [h| [::]])] :: (seq_to_seqheap t)
else [::].

Fixpoint count_sseq a hh := 
  if hh is sh :: hh' then 
    if sh is some h then count a h + count_sseq a hh' 
    else count_sseq a hh'
  else 0.

Fixpoint count_seq a (sh : seq heap) := 
  if sh is h :: sh' then count a h + count_seq a sh' else 0.

Theorem seq_to_seqheap_spec s: count_seq^~ (seq_to_seqheap s) =1 seq.count^~ s.
Proof. move=> a; elim: s=> //= ??->; rewrite tree.countE. ssrnatlia. Qed.

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
    let h2 := if sh2 is some h then h else [::] in
   fromseqheap_pop (merge h2 h1) hh' else h1.

Fixpoint fromseqheap_rec hh sh  :=
  match sh with
  | [:: x1, x2 & h'] => let h1 := merge x1 x2 in
    fromseqheap_rec (fromseqheap_push h1 hh) h'
  | [:: h] => fromseqheap_pop h hh
  | [::] => fromseqheap_pop [::] hh
  end.

Definition fromseqheap := (fromseqheap_rec [::]).

Fixpoint fromseqheap_rec1 hh sh :=
  if sh is x :: h then fromseqheap_rec1 (fromseqheap_push x hh) h else fromseqheap_pop [::] hh.

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
Definition invariant := heap -> bool.

Variables inv : invariant.

Hypothesis merge_invariat : forall h1 h2, inv h1 -> inv h2 -> inv (merge h1 h2).
Hypothesis inv_E : inv [::].
Hypothesis inv_NodexEE : forall x, inv [:: (0, [x| [::]])].
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


Definition all_trees_binomial_rk_fromseq : forall s, all_trees_binomial_rk (fromseq s) := 
  inv_fromseq all_trees_binomial_rk merge_binom_inv' all_trees_binomial_rk_E all_trees_binomial_rk1.

Definition heap_ordered_fromseq : forall s, heap_ordered (fromseq s) := 
  inv_fromseq heap_ordered merge_ho_inv heap_ordered_E heap_ordered1.

Definition binomial_heap_fromseq: forall s, binomial_heap (fromseq s) :=
  inv_fromseq binomial_heap merge_correct binomial_heap_E binomial_heap1.


Equations fromheap h : seq T by wf (size h) lt:=
fromheap [::] := [::];
fromheap  (a :: b) := 
  if findmin (a :: b) is some y then y :: (fromheap (deletemin (a :: b)))
  else [::].

Next Obligation.
rewrite deletemin_size. apply: Lt.lt_pred_n_n.
rewrite /size/=. apply: Plus.lt_plus_trans. by apply: tree.size_tree_pos.
Qed.

Lemma fromheap_spec1 h: count^~ h =1 seq.count^~ (fromheap h).
Proof.
move=> p. apply_funelim (fromheap h)=> // [[a c b IH]].
(* case H: findmin (a :: b)=> //. anomaly*)
move: {-2}(findmin ((a, c) :: b)) (@erefl _ (findmin ((a, c) :: b)))=>
[d H|/findmin_None//]. by rewrite -(@deletemin_spec _ _ d) // insert_spec /= -IH.
Qed.

Lemma fromheap_spec2 h: (heap_ordered h) -> sorted <=%O (fromheap h).
Proof.
apply_funelim (fromheap h)=> // [[a c b IH]].
move: {-2}(findmin ((a, c) :: b)) (@erefl _ (findmin ((a, c) :: b)))=>
[d|/findmin_None//] H HH. move: (HH)=> /(findmin_spec d)[_ /(_ H) /andP[*/=]].
rewrite path_sortedE ?IH ?deletemin_ho_inv // ?andbT; last by apply: le_trans.
apply/allP=> x. rewrite -has_pred1 has_count -fromheap_spec1.
move=> /(@leq_trans _ _ (count (pred1 x) (insert d (deletemin ((a, c) :: b))))) Le.
have: (0 < count (pred1 x) (insert d (deletemin ((a, c) :: b))))%N.
- apply: Le. rewrite insert_spec; by ssrnatlia.
rewrite deletemin_spec // -int_conut=> /in_all. by apply.
Qed.

Definition heapsort s := fromheap (fromseq s).

Theorem sorted_heapsort s : (sorted <=%O (heapsort s)).
Proof. by rewrite fromheap_spec2 // heap_ordered_fromseq. Qed.

Lemma count_heapsort s : seq.count^~ (heapsort s) =1 seq.count^~ s.
Proof. move=> p. by rewrite /heapsort -fromheap_spec1 fromseq_cspec. Qed.

Theorem perm_heapsort s : perm_eql (heapsort s) s.
Proof. apply/permPl/permP; by apply: count_heapsort. Qed.
End Heapsort.
End BinomialHeap.
