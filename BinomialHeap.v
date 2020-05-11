From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype. 
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).
Import Order.NatOrder.

Open Scope order_scope.

(*Lemma nat_ltgteq (n m : nat) : (n < m) || (n > m) || (n == m).
Proof. by case: ltgtP. Qed.*)

Lemma add_lt_le a b c d: (a < c)%N -> (b <= d)%N -> ((a + b == c + d) = false).
Proof. 
move=> *; have /ltn_eqF// : ((a + b) < (c + d))%N.
by rewrite [a + b]addnC -ltn_subRL -addnBA // ltn_addr.
Qed.

Lemma add_le_lt a b c d: (a <= c)%N -> (b < d)%N -> ((a + b == c + d) = false).
Proof. move=> *. rewrite [a + b]addnC [c + d]addnC. by apply: add_lt_le. Qed.

Section BinomialHeap.

Variables (T : ordType).

Inductive tree :=
| Node : T -> list tree -> tree.

Implicit Type tr : tree.

Definition heap := seq (nat * tree).

Notation "[ x | c ]" := (Node x c).

Fixpoint binomtree_of_rk (rk : nat) (tr : tree) := 
  match tr, rk with
  | [x| trh :: trt], rk'.+1 => binomtree_of_rk rk' trh && binomtree_of_rk rk' [x| trt]
  | [x| [::]],       0      => true
  | _,               _      => false
  end.

(*Lemma size_nodes r x y h l : 
  binomtree_of_rk r [x | [y | h] :: l] -> size h = size l.
Proof.
elim: l h r=> [[]//??[]//[]//?/andP[]|?? IHl[[|[]]|]]//=? l []//[]// r /=/andP[/andP[??/andP[*]]].
rewrite (IHl l r.+1) //=; by apply/andP; split.
Qed.*)

Fixpoint eqtree tr1 tr2 := true.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
Admitted.

Canonical tree_eqMixin := EqMixin eqtreeP.
Canonical tree_eqType := Eval hnf in EqType tree tree_eqMixin.

Lemma eqtreeE : eqtree = eq_op. Proof. by []. Qed.


Fixpoint size (tr : tree) : nat :=
  match tr with [x| l] =>
    let fix binom_list l :=
      if l is trh :: trt then size trh + binom_list trt
      else 0 in (binom_list l).+1
    end.

Lemma binomtree_ind (P : tree -> Prop):
  (forall x, P [x| [::]]) ->
  (forall h l x, P h -> P [x| l] -> P [x| h :: l]) ->
  forall h, P h.
Proof.
move=> Base IH_Hyp h. have [n le_size] := ubnP (size h).
elim: n h le_size => // n IHn [x [] // h t S]; apply: IH_Hyp; apply IHn; move: S=> /=;
case: h=> ??/=; by ssrnatlia.
Qed.

Lemma sizeE x : (forall h l,size [x | h :: l] = size h + size [x| l]) * (size [x| [::]] = 1)%N.
Proof. by split=> *; rewrite /= ?addnS. Qed.

Lemma rk_singl x rk : binomtree_of_rk rk [x | [::]] -> rk = 0.
Proof. by case: rk. Qed.

Arguments size : simpl never.

Theorem binomtree_size rk tr : binomtree_of_rk rk tr -> size tr = 2 ^ rk.
Proof.
elim/binomtree_ind: tr rk=> [x rk /rk_singl ->|]//=??? IHtr1 IHtr2 []//= rk /andP[*].
rewrite sizeE /= (IHtr1 rk) // (IHtr2 rk) // expnS. by ssrnatlia.
Qed.

Fixpoint heap_ordered_tree tr : bool :=
  match tr with [x| l] =>
    let fix binom_list l :=
      if l is ([y| trtt] as trh) :: trt then
        (x <= y) && heap_ordered_tree trh && binom_list trt
      else true in binom_list l
    end.

Lemma heap_ordered_treeE x y t l: 
  (heap_ordered_tree [x| [y| t] :: l] = (x <= y) && (heap_ordered_tree [y| t]) && (heap_ordered_tree [x| l])) *
  (heap_ordered_tree [x| [::]]).
Proof. by []. Qed.

Arguments heap_ordered_tree : simpl never.

Definition link (t1 t2 : tree) : tree :=
  match t1, t2 with 
  | [x1| c1], [x2| c2] =>
  if x1 <= x2 then 
    [x1| (t2 :: c1)]
  else [x2| (t1 :: c2)]
end.

Lemma link_preserves_heaporder tr1 tr2 : heap_ordered_tree tr1 -> heap_ordered_tree tr2 ->
  heap_ordered_tree (link tr1 tr2).
Proof.
  case: tr1 tr2=>??[??/=]. case: ifP; rewrite heap_ordered_treeE; by case: ltgtP=> ??->->.
Qed.

Lemma link_preserves_binomial rk tr1 tr2: 
  binomtree_of_rk rk tr1 -> binomtree_of_rk rk tr2 -> binomtree_of_rk rk.+1 (link tr1 tr2).
Proof. case: tr1 tr2=>??[??/=]. by case: ifP=> _->->. Qed.

Fixpoint count_tree (a : pred T) tr : nat := 
  match tr with [x| l] =>
  let fix binom_list l :=
    if l is trh :: trt then
        count_tree a trh + binom_list trt
    else 0 in (a x) + binom_list l
  end.

Lemma count_treeE a x: 
  (forall tr l, count_tree a [x| tr :: l] = count_tree a [x| l] + count_tree a tr) *
  (count_tree a [x| [::]] = a x).
Proof. split=> /= *; first by ssrnatlia. by rewrite addn0. Qed.

Arguments count_tree : simpl never.

Definition mem_tree tr := fun x => (0 < count_tree (fun y => x == y) tr)%N.

Definition tree_eqclass := tree.
Identity Coercion tree_of_eqclass : tree_eqclass >-> tree.
Coercion pred_of_tree (h : tree_eqclass) : {pred T} := mem_tree h.

Canonical tree_predType := PredType pred_of_tree.
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_tree_predType := PredType mem_tree.

Lemma inEt x y: 
  (forall tr l, (x \in [y| tr :: l] = (x \in [y| l]) || (x \in tr)) *
  (x \in [y| [::]] = (x == y)))%type.
Proof.
split=> *; rewrite /in_mem /= /mem_tree !count_treeE ?addn_gt0 //. by case (x==y). 
Qed.

Lemma link_spec a tr1 tr2: count_tree a (link tr1 tr2) = count_tree a tr1 + count_tree a tr2.
Proof. case: tr1 tr2=> ??[??/=]; case: ifP; by rewrite count_treeE // addnC. Qed.

Print sorted.

Definition rank_ord (le : rel nat) (tr1 tr2 : nat * tree) : bool := le tr1.1 tr2.1.

Implicit Type h : heap.

Definition rank_sorted h    := sorted (rank_ord (fun n m => (n < m)%N)) h.
Definition heap_ordered h   := all (heap_ordered_tree \o snd) h.
Definition binomial_pair ph := binomtree_of_rk ph.1 ph.2.
Definition binomial_heap h  := all binomial_pair h.

Fixpoint instree tr (rk : nat) h :=
  if h is (rk', tr') :: ts then
    if (rk < rk')%N then (rk, tr) :: h
    else instree (link tr tr') rk.+1 ts
  else [:: (rk, tr)].

Definition insertable rk h :=
  if h is trp :: th then (rk <= trp.1)%N else true.

Lemma instree_peserves_rk_sort tr rk h: 
  binomtree_of_rk rk tr -> insertable rk h -> binomial_heap h ->
  rank_sorted h -> rank_sorted (instree tr rk h).
Proof.
elim: h rk tr=> // [[rk tr ts IHh rk' tr' /= BT]];
rewrite /rank_ord/= leq_eqVlt => /orP[/eqP EQ|]; case: ifP=> //; first by rewrite EQ ltnn.
- move=> _ /andP[]; move:BT. rewrite EQ /binomial_pair/= => ?? BH P.
  rewrite {}IHh // ?link_preserves_binomial //= ?/rank_ord;
  by move: ts P BH=> [] //=?? /andP[].
by rewrite /rank_sorted/=/rank_ord=> -> {IHh} _ _=>->. 
Qed.

Lemma instree_peserves_heap_order tr rk h: 
  heap_ordered_tree tr ->
  heap_ordered h -> heap_ordered (instree tr rk h).
Proof.
elim: h rk tr=> /= [??-> //|[??? IHh ??]].
case: ifP => /= [_ -> /andP[->->] //|_ ?/andP[*]]; 
by rewrite IHh ?link_preserves_heaporder.
Qed.

Lemma instree_peserves_binomial tr rk h: 
  binomtree_of_rk rk tr -> insertable rk h -> binomial_heap h ->
  rank_sorted h -> binomial_heap (instree tr rk h).
Proof.
elim: h rk tr => /= [??|[?? l IHh ?? BT]];
rewrite -/binomial_pair ?andbT //= leq_eqVlt =>/orP[/eqP<-|->/andP[/=->->]];
rewrite ?/binomial_pair (ltnn, BT) // /= => /andP[? Bl Sl].
rewrite IHh // ?link_preserves_binomial //; 
by move: l {Bl IHh} Sl=> []//= ?? /andP[].
Qed.

Fixpoint count (a : pred T) h : nat :=
  if h is (_, th) :: t then count_tree a th + count a t
  else 0.

(* heap := seq (nat * tree)*)

Fixpoint mem_heap h := 
if h is (_, tr) :: ttt then xpredU (fun x => x \in tr) (mem_heap ttt) else xpred0.

Definition heap_eqclass := heap.
Identity Coercion heap_of_eqclass : heap_eqclass >-> heap.
Coercion pred_of_heap (h : heap_eqclass) : {pred T} := mem_heap h.

Canonical heap_predType := PredType pred_of_heap.
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_heap_predType := PredType mem_heap.

Definition consh trn h : heap := trn :: h.

(*Lemma inE (x : T): 
  (forall rk tr h, ((x \in (rk, tr) :: h) = (x \in h) || (x \in tr)) *
  ((x \in [::]) = false))%type.
Proof. split=> *; rewrite /consh /in_mem //= /in_mem /= orbC //. Qed.*)

Lemma instree_spec a tr rk h: count a (instree tr rk h) = count_tree a tr + count a h.
Proof.
elim: h tr rk=>//= [[??? IHl *]]. case: ifP;
by rewrite // IHl link_spec addnA.
Qed.

Definition insert x h := instree [x| [::]] 0 h.

Lemma insert_peserves_rk_sort x h: 
 rank_sorted h -> binomial_heap h -> rank_sorted (insert x h).
Proof. move=> H H'; apply: instree_peserves_rk_sort=> //. by case: h {H H'}. Qed.

Lemma insert_peserves_heap_order x h: 
  heap_ordered h -> heap_ordered (insert x h).
Proof.
move=> H; apply: instree_peserves_heap_order; by rewrite // ?heap_ordered_treeE.
Qed.

Lemma insert_peserves_binomial x h: 
  binomial_heap h -> rank_sorted h -> binomial_heap (insert x h).
Proof. move=> H H'; apply instree_peserves_binomial=> //; by case: h {H H'}. Qed.

Lemma insert_spec a x h : count a (insert x h) = a x + count a h.
Proof. rewrite instree_spec count_treeE //. Qed.

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

Lemma merge_preserves_heap_order h1 h2: heap_ordered h1 -> heap_ordered h2 ->
  heap_ordered (merge h1 h2).
Proof.
elim: h1 h2=> // [[rk1 ? l IHh1]]. elim=> // [[rk2 ? l1 IHh2 H1 H2]].
merge_cases rk1 rk2; move: (H1) (H2)=> /= /andP[Hb Hl /andP[Hb1 Hl1]];
by rewrite ?Hb ?Hb1 ?IHh2 ?instree_peserves_heap_order ?link_preserves_heaporder ?IHh1.
Qed.

Lemma merge_spec h1 h2 a: count a (merge h1 h2) = count a h1 + count a h2.
Proof.
elim: h1 h2=> // [[rk1 ? l IHh1]]. elim=> /= [|[rk2 ? l1 IH2]]; first by rewrite addn0.
merge_cases rk1 rk2; rewrite /= ?IH2 /= ?instree_spec ?IHh1 ?link_spec /=; by ssrnatlia.
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


Lemma insertale_merge h1 h2 rk: insertable rk h1 -> insertable rk h2 ->
   insertable rk (merge h1 h2).
Proof.
case: h1; case: h2=> [*|]; rewrite ?merge_h_E // => [[rk1 ?? [rk2 /= *]]].
merge_cases rk2 rk1; rewrite insertable_instree //. by ssrnatlia.
Qed.

Arguments rank_sorted: simpl never.

Lemma merge_preserves_binomial h1 h2 :  rank_sorted h1 -> rank_sorted h2 ->
binomial_heap h1 -> binomial_heap h2 -> binomial_heap (merge h1 h2) * rank_sorted (merge h1 h2).
Proof.
elim: h1 h2=> // [[rk1 ? l IHh1]]. elim=> // [[rk2 ? l1 IHh2 RS1 RS2 B B']].
merge_cases rk1 rk2; move: (B) (B'); rewrite /= /binomial_pair /= => /andP[B1 Bl /andP[B2 Bl1]];
move: (RS1) (RS2); rewrite !rank_sort_insertable=> /andP[?? /andP[??]];
by rewrite ?B1 ?B2 ?IHh2 ?instree_peserves_binomial ?instree_peserves_rk_sort
 ?link_preserves_binomial ?insertale_merge ?IHh1 ?RR // -?RR.
Qed.

Definition allt a tr := (count_tree a tr == size tr).

Lemma count_le_size a tr: (count_tree a tr <= size tr)%N.
Proof.
elim/binomtree_ind: tr=> x *; rewrite ?count_treeE sizeE; first by case: (a x).
by rewrite addnC leq_add.
Qed.


Lemma alltE a x y t l: ((allt a [x| [::]] = a x) *
(allt a [x| [y| t] :: l] = allt a [x| l] && allt a [y|t]))%type.
Proof.
rewrite /allt !count_treeE // !sizeE //; split; first by case: a.
have := (count_le_size a [y| t]); have := (count_le_size a [x| l]).
rewrite leq_eqVlt addnC=> /orP[/eqP->|C /add_le_lt/(_ C)->];
last by move: C=> /ltn_eqF->. rewrite leq_eqVlt=> /orP[/eqP->|/ltn_eqF];
by rewrite ?eq_refl // eqn_add2r=>->.
Qed.

Fixpoint all a h := if h is (_, th) :: t then allt a th && all a t else true.

Fixpoint removemintree (ts : heap) : option (tree * heap) :=
match ts with
| [::]      => None
| [:: (_, tr)]     => some (tr, [::])
| (rk, [x| l]) :: ts =>  
              if removemintree ts is some ([x'| l'], ts') then
                if x <= x' then some ([x| l], ts) 
                else some ([x'| l'], (rk, [x| l]) :: ts)
              else None
end.

Lemma removemintree_None (ts : heap): 
  removemintree ts = None <-> ts = [::].
Proof.
elim: ts=> //= [[? [?? []// a l]]].
case: (removemintree (a :: l))=> // [[[]]*|[] /(_ erefl) //].
by case: ifP.
Qed.

(*Lemma removeintree_some h x l h': 
removemintree h = some ([x| l], h') <->.
Proof.
  
Qed.*)



Definition findmin (ts : heap) : option T :=
if (removemintree ts) is some ([x| _], _) then some x else None.

Theorem findmin_None h: None = findmin h <-> h = [::].
Proof. 
split=> [|-> //]. rewrite /findmin.
case a : (removemintree h)=> [[[]]|] //*. move: a. 
by rewrite removemintree_None.
Qed.

(*Theorem findmin_spec x h: heap_ordered h -> 
((x \in h) && all (>= x) h) <-> (Some x = findmin h).
Proof.
move=> HH; split=> [/andP[]|]; move: h HH=> [|[]] //.
- move=> rk tr l H /=. rewrite /in_mem /=.
split=> [/andP[]|]; move: h H=> [] //.
- move=> n y h1 h2 /= /and4P[L1 L2 H1 H2]
  /or3P[/eqP-> //|/(LE_correct _ _ _ H1)/(_ L1)|/(LE_correct _ _ _ H2)/(_ L2)] XY YX;
suffices: x = y=> [-> //|]; apply: le_anti; rewrite XY YX //.
move=> ????? [->]. by rewrite in_node eq_refl /=.
Qed.*)
  
Fixpoint revh_rank (ts : seq tree) (rk : nat) : heap :=
match ts with
| [::] => [::]
| t :: ts' => (revh_rank ts' rk.-1) ++ [:: (rk, t)]
end.

(*Definition deleteMin (ts : heap) : heap :=
if (removemintree ts) is some ([x| ts1], ts2) then
  if ts1 is (rk, _) :: _ then merge (revh_rank ts1 rk) ts2
  else ts2
else [::].

  Definition isEmpty (ts : Heap) :=
    if ts is [] then true else false.*)
End BinomialHeap.
