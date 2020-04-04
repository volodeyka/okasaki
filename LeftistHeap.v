From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype.
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).

Open Scope order_scope.

Module LeftistHeap.
(*Leftist heaps are heap-ordered binary trees that satisfy the
leftist property: the rank of any left child is at least as large as the rank of its
right sibling. The rank of a node is defined to be the length of its right spine
(i.e., the rightmost path from the node in question to an empty node). A simple
consequence of the leftist property is that the right spine of any node is always
the shortest path to an empty node.*)

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

  
  
  Section LeftistDef.
    Variables (Elem : ordType).

    Hint Resolve lexx : core.

    Inductive Heap :=
    | E : Heap
    | T : nat -> Elem -> Heap -> Heap -> Heap.

    Definition LE x h : bool := 
      if h is T n y a b then (x <= y) else true.

    Fixpoint HeapOrder h : bool :=
      if h is T n x tl tr then
        (LE x tl) && (LE x tr) && (HeapOrder tl) && (HeapOrder tr)
      else true.


    Fixpoint rk (h : Heap) : nat :=
      if h is T _ _ _ b then (rk b).+1 else O.

    Fixpoint Rank_Rk h : bool :=
      match h with
      | T n x tl tr => (n == (rk tr).+1) && (Rank_Rk tr) && (Rank_Rk tl)
      | E           => true
      end.
        
    
    Fixpoint rank (H : Heap) : nat :=
    if H is T r _ _ _ then r else O.

    Fixpoint Leftist_Inv h : bool :=
    if h is T n x tl tr then
      (Leftist_Inv tl) && (Leftist_Inv tr) && (rank tr <= rank tl)%N
    else true.

    Lemma rank_correct : forall H, Rank_Rk H -> rk H = rank H.
    Proof. by move=> [] //= n _ tl tr /andP[/andP[/eqP]]. Qed.

    Inductive side := r | l.
  
    Definition spine := seq side.

    Fixpoint spine_in p h : bool :=
      match p, h with
      | r :: p, T _ _ _ tr => spine_in p tr
      | l :: p, T _ _ tl _ => spine_in p tl
      | [::],   E          => true
      | _,      _          => false
      end.

    Fixpoint Right p : bool :=
      match p with
      | r :: p' => Right p'
      | l :: _  => false
      | [::]    => true
      end.
    
    Lemma Rigth_correct : forall x s, Right (x :: s) -> (x = r /\ Right s).
    Proof. move=> [] //=. Qed.

    Lemma case_spine_in : forall side s n x tl tr, 
      spine_in (side :: s) (T n x tl tr) -> 
      if side is r then spine_in s tr else spine_in s tl.
    Proof. move=> [] //=. Qed. 

    Definition Leftist_Rank_Inv (H : Heap) := Leftist_Inv H /\ Rank_Rk H.


    Lemma case_Leftist_Rank_Inv_r: forall n x tl tr,
      Leftist_Rank_Inv (T n x tl tr) -> Leftist_Rank_Inv tr.
    Proof.
      by move=> n x tl tr [] /= /andP[/andP[_ Ltr _ /andP[/andP[]]]].
    Qed.
    
    Lemma case_Leftist_Rank_Inv_rl: forall n x tl tr,
      Leftist_Rank_Inv (T n x tl tr) -> 
      Leftist_Rank_Inv tr /\ Leftist_Rank_Inv tl /\ (rank tr <= rank tl)%N.
    Proof. by move=> n x tl tr [/= /andP[/andP[LIl LIr R /andP[/andP[]]]]]. Qed.

    Lemma case_Rank_Rk n y h1 h2 : 
      Rank_Rk (T n y h1 h2) -> (n = (rk h2).+1) /\ (Rank_Rk h1) /\ (Rank_Rk h2).
      Proof. by move=> /= /andP[/andP[/eqP]]. Qed.
  
  Lemma case_HeapOrder n y h1 h2 : 
    HeapOrder (T n y h1 h2) ->
    LE y h1 /\ LE y h2 /\ (HeapOrder h1) /\ (HeapOrder h2).
  Proof. by move=> /= /andP[/andP[/andP[]]]. Qed.      
    
  
  Lemma lt_le n : (0 < n)%N -> (n <= 0)%N = false.
  Proof.
    case H : (n <= 0)%N=> //.
    by move/leq_trans/(_ H).
  Qed.
  
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
  
  Lemma case_Leftist_inv n y h1 h2 : 
    Leftist_Inv (T n y h1 h2) -> ((rank h2 <= rank h1)%N /\ Leftist_Inv h1 /\ Leftist_Inv h2).
  Proof. by move=> /= /andP[/andP[]]. Qed.

  Lemma leq_1 : forall (a b : nat), (a <= b)%N -> (a.+1 <= b.+1)%N.
    Proof. by move=> a b H; ssrnatlia. Qed.

    Lemma Right_spine_ex : forall H, exists s, Right s /\ spine_in s H.
    Proof.
      elim=> [|n s hl _ hr [] s' [] IHHR IHHS].
      - by exists nil.
      by exists (r :: s').
    Qed.

    Lemma length_right_spine : forall H s, 
    Leftist_Rank_Inv H -> Right s -> spine_in s H ->
    length s = rank H.
    Proof.
      move=> h s [] _ RC; move: (RC)=> /rank_correct <-.
      elim: h s RC=> 
      [[|[]]|n x tl IHhl tr IHtr [_ _|[s /= /andP[/andP[_ RRl RRr]] |]]] //= R S.
      apply/eqnP=> /=. apply/eqP. by apply: IHtr.
    Qed.
    
    Lemma spine_in_E s : spine_in s E -> s = [::].
    Proof. by case: s=> [|[]] //=. Qed.
    


    Theorem rigth_spine_shortest : 
      forall H s1 s2, Right s1 -> Leftist_Rank_Inv H -> spine_in s1 H -> spine_in s2 H ->
      (length s1 <= length s2)%nat.
    Proof. 
      elim=>
      [s1 s2 _ _ /spine_in_E->|
      n x tl IHtl tr IHtr [//|
      a s1 [/Rigth_correct [] -> _ _ _ |[]
      s2 /Rigth_correct [] ->]]] //= => [Rs1 /case_Leftist_Rank_Inv_r LI|
      Rs1 /case_Leftist_Rank_Inv_rl [] LI1 [] LI2 LE]=> SI1 SI2.
      - apply: leq_1; apply IHtr=> //.
      rewrite (length_right_spine tr s1) //.
      case: (Right_spine_ex tl)=> s [] Rs SIstl.
      suffices: (rank tl <= length s2)%N. ssrnatlia.
      rewrite -(length_right_spine tl s) //.
      by apply: IHtl.
    Qed.

    Definition makeT (x : Elem) (a b : Heap) : Heap :=
      if (rank b <= rank a)%N then T (rank b).+1 x a b else T (rank a).+1 x b a.

    Lemma nlt_gt : forall a b, (a <= b)%N = false -> (b < a)%N.
    Proof.
      move=> a b /neq0_lt0n. ssrnatlia.
    Qed.    

    Lemma makeT_preserves_LI_inv : forall x tl tr,
      Leftist_Inv tl -> Leftist_Inv tr ->
      Leftist_Inv (makeT x tl tr).
    Proof.
        rewrite /makeT=> x tl tr; case H : (rank tr <= rank tl)%N=> /=->->//=.
        move: H=> /nlt_gt; by ssrnatlia.
    Qed.

    Lemma makeT_preserves_rk_inv x tl tr :
      Rank_Rk tl -> Rank_Rk tr ->
      Rank_Rk (makeT x tl tr).
    Proof.
      move=> Rl Rr; rewrite /makeT -!(rank_correct _ Rl) -!(rank_correct _ Rr).
      by case H : (rk tr <= rk tl)%N=> /=; rewrite Rl Rr eq_refl.
    Qed.
    
    Lemma makeT_peserves_HO_inv x tl tr :
      HeapOrder tl -> HeapOrder tr ->
      LE x tl -> LE x tr ->
      HeapOrder (makeT x tl tr).
    Proof.
      by rewrite /makeT; case H : (rank tr <= rank tl)%N=> /=->->->->.
    Qed.
    
    Fixpoint member x (h : Heap) :=
      if h is T _ y a b then (x == y) || (member x a) || (member x b) else false.

    Notation "x ? h" := (member x h) (at level 0).

    Definition LeftistHeap (h : Heap) :=
      Leftist_Inv h /\ Rank_Rk h /\ HeapOrder h.

    Fixpoint merge a :=
    if a is T n x a1 b1 then
      let fix merge_a b :=
        if b is T m y a2 b2 then
          if x <= y then 
            makeT x a1 (merge b1 b)
          else
            makeT y a2 (merge_a b2)
        else a in
      merge_a
    else id.

    Arguments merge !tl !tr : rename.

    Lemma merge_E_h: forall h, merge E h = h.
    Proof.  by case. Qed.
    Hint Rewrite merge_E_h.

    Lemma merge_h_E: forall h, merge h E = h.
    Proof. by case. Qed.
    Hint Rewrite merge_h_E.

    Lemma Rank_Rk_r n x tl tr:
      Rank_Rk (T n x tl tr) -> Rank_Rk tr.
    Proof. by move=> /andP[/andP[]]. Qed.

    Lemma Rank_Rk_l n x tl tr :
      Rank_Rk (T n x tl tr) -> Rank_Rk tl.
    Proof. by move=> /andP[/andP[]]. Qed.

    Lemma merge_a nl nr x y tll tlr trr trl :
      (x <= y) = false -> 
      merge (T nl x tll tlr) (T nr y trl trr) = 
      makeT y trl (merge  (T nl x tll tlr) trr).
    Proof.
      move=> /= ->.
      by elim: trr.
    Qed.
    
    Hint Rewrite merge_a.
    Lemma merge_preserve_rk_inv : forall h1 h2,
      Rank_Rk h1 -> Rank_Rk h2 -> Rank_Rk (merge h1 h2) .
    Proof.
      elim=> [//| nl x tll IHhl tlr IHhr].
      elim=> [|nr y trl IH'hl trr IH'hr] //.
      case H : (x <= y)=> H1 H2; merge_cases;
      move: (H1) (H2) => /case_Rank_Rk [_ [HH1 HH2]] /case_Rank_Rk [_ [HH3 HH4]];
      apply makeT_preserves_rk_inv=> //.
      - by apply IHhr.
      by apply IH'hr.
    Qed.
    
    Lemma case_HeapOrder_l n x tl tr :
      HeapOrder (T n x tl tr) -> (HeapOrder tl /\ LE x tl).
    Proof. by move=> /andP[/andP[/andP[]]]. Qed.
    
    Lemma case_HeapOrder_r n x tl tr :
      HeapOrder (T n x tl tr) -> (HeapOrder tr /\ LE x tr).
    Proof. by move=> /andP[/andP[/andP[]]]. Qed.

    Lemma case_LE x y n tr tl :
      LE x (T n y tl tr) -> x <= y.
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
      [makeT_casesxy (rank (merge tlr (T nr y trl trr))) (rank tll)|
       makeT_casesxy (rank (merge (T nl x tll tlr) trr)) (rank trl)].
    Qed.

    Lemma merge_preserve_HO_inv : forall h1 h2,
      HeapOrder h1 -> HeapOrder h2 -> HeapOrder (merge h1 h2).
    Proof.
      elim=> [//| nl x tll IHhl tlr IHhr].
      elim=> [|nr y trl IH'hl trr IH'hr H1 H2] //.
      move : (H1) (H2)=>
              /case_HeapOrder [L1 [L2[HH1 HH2]]]
              /case_HeapOrder [L'1 [L'2[HH'1 HH'2]]] //;
      merge_casesxy x y; apply makeT_peserves_HO_inv=> //.
      1 : apply: IHhr=> //.
      2 : apply: IH'hr=> //.
      all : apply: merge_preserve_LE=> //=.
      move: (negbT H).
      by rewrite -ltNge lt_def=> /andP[_ ->].
    Qed.

    Lemma case_Leftist_Inv_l n x tl tr :
    Leftist_Inv (T n x tl tr) -> Leftist_Inv tl.
    Proof. by move=> /andP[/andP[]].  Qed.

    Lemma case_Leftist_Inv_r n x tl tr :
    Leftist_Inv (T n x tl tr) -> Leftist_Inv tr.
    Proof. by move=> /andP[/andP[]].  Qed.
    
    Lemma merge_preserve_LI_inv : forall h1 h2,
      Leftist_Inv h1 -> Leftist_Inv h2 -> Leftist_Inv (merge h1 h2).
    Proof.
      elim=> [//| nl x tll IHhl tlr IHhr].
      elim=> [|nr y trl IH'hl trr IH'hr H1 H2] //.
      move : (H1) (H2) => /case_Leftist_inv [_ [HH1 HH2]] /case_Leftist_inv [_ [HH'1 HH'2]].
      merge_casesxy x y; apply: makeT_preserves_LI_inv=> //.
      - by apply: IHhr.
      by apply: IH'hr.
    Qed.    

    Theorem merge_preserve_LH h1 h2 :
      LeftistHeap h1 -> LeftistHeap h2 -> LeftistHeap (merge h1 h2).
    Proof.
      move=> [LI1 [RR1 HO1]] [LI2 [RR2 HO2]]; split.
      - by apply: merge_preserve_LI_inv.
      - split.
      - by apply: merge_preserve_rk_inv.
      by apply: merge_preserve_HO_inv. 
    Qed.
    
    Lemma case_member : forall x y n tl tr,
    x ? (T n y tl tr) <-> (x = y) \/ (x ? tl) \/ (x ? tr).
    Proof.
      split.
      - move=> /orP[/orP[/eqP|]|]; by [left|right; left|right; right].
      case=> [->|[]H] /=; apply/orP.
      - by left; apply/orP; left.
      - by left; apply/orP; right.
      by right.
    Qed.

    Lemma makeT_spec h1 h2 x y :
      x ? (makeT y h1 h2) <-> (x = y) \/ (x ? h1) \/ (x ? h2).
    Proof.
    makeT_casesxy (rank h2) (rank h1).
      split => /case_member // [|[]].
      split=> [/case_member // [->|[]->]|[->/=|[]/=->]] //.
      - by left.
      - by right; right.
      - by right; left.
      by rewrite eq_refl.
    Qed.
    
    Theorem merge_spec : forall h1 h2 x,
      x ? (merge h1 h2) <-> (x ? h1) \/ (x ? h2).
    Proof.
      split.
      - elim: h1 h2=> [h2|n y h1 IHh1 h2 IHh2].
      - rewrite merge_E_h=> H; by right.
      - elim=> [|m z h21 IHh21 h22 IHh22]; first by rewrite merge_h_E=> H; left.
      - merge_casesxy y z=> /makeT_spec [-> |[->|]].
      - by left; rewrite eq_refl.
      - by left.
      - move=> /IHh2 [->|]; [left|]=> //=; by right.
      1,2: by rewrite ?eq_refl; right.
      - move=> /IHh22 [/case_member [->|[]->]|->]; rewrite ?eq_refl.
      1-3: by left.
      - by right.

      - elim: h1 h2=> [h [F|H]|n y h11 IHh1 h22 IHh2]; rewrite ?merge_E_h //.
      - elim=> [[] // F|m z h12 IHh12 h21 IHh21]; rewrite ?merge_h_E.
      merge_casesxy y z; case=> /orP[/orP[/eqP|]|]; rewrite makeT_spec.
      - by left.
      - by right; left.
      1-4: right; right; apply IHh2.
      - by left.
      1- 3: by right=> /=; rewrite H0 ?eq_refl.
      1-3, 6: right; right; apply IHh21=> /=; rewrite H0 ?eq_refl.
      1-3: by left.
      - by right.
      - by left.
      by right; left.
    Qed.

    Definition insert (x : Elem) (h : Heap) := 
      merge (T 1 x E E) h.
    
    Lemma rk_E : ((rk E).+1 = 1)%N.
    Proof. by []. Qed.    

    Lemma insert_preserve_rk_inv : forall h x,
      Rank_Rk h -> Rank_Rk (insert x h).
    Proof.
      by move=> h x Rh; apply merge_preserve_rk_inv.
    Qed.

    Lemma insert_preserve_HO_inv : forall h x,
      HeapOrder h -> HeapOrder (insert x h).
    Proof.
      by move=> h x Rh; apply merge_preserve_HO_inv.
    Qed.

    Lemma insert_preserve_LI_inv : forall h x,
      Leftist_Inv h -> Leftist_Inv (insert x h).
    Proof.
      by move=> h x Rh; apply merge_preserve_LI_inv.
    Qed.

    Theorem insert_preserve_LH : forall h x,
      LeftistHeap h -> LeftistHeap (insert x h).
    Proof.
      by move=> h x Rh; apply merge_preserve_LH.
    Qed.
    
    Lemma x_Ty x y : (x) ? (T 1 y E E) <-> (x = y).
    Proof.
      by split=> /= [/orP[/orP[/eqP|]|]|->]; rewrite ?eq_refl.
    Qed.

    Theorem insert_correct h x y :
    x ? (insert y h) <-> (x = y) \/ (x ? h).
    Proof.
      by rewrite merge_spec x_Ty.
    Qed.
    
    Definition findMin (h : Heap) := 
      if h is T _ x _ _ then Some x else None.

    Theorem findMin_correct1 : forall h,
      None = findMin h <-> h = E.
    Proof. split=> [|-> //]. by case : h. Qed.
    
    Lemma LE_correct : forall h x y,
      HeapOrder h -> x ? h -> LE y h -> y <= x.
    Proof.
      elim=> [x y _ H| n x h1 IHh1 h2 IHh2 x' y' HO /case_member 
      [-> /case_LE //|[H|H] /case_LE]]//.
      move: HO=> /case_HeapOrder_l [] /IHh1 H1 /(H1 x' x H) H2 H3.
      2: move: HO=> /case_HeapOrder_r [] /IHh2 H1 /(H1 x' x H) H2 H3.
      all: move: H3 H2; apply: le_trans.
    Qed.

    Theorem findMin_correct2 : forall h, HeapOrder h ->
      forall z, Some z = findMin h -> forall x, x ? h -> z <= x.
    Proof.
      case=> [//| n x h1 h2 HO z /= [->] y /(case_member _ _ n)[-> //|[H|H]]].
      - by move: HO=> /case_HeapOrder_l [] /LE_correct - /(_ _ x H).
      - by move: HO=> /case_HeapOrder_r [] /LE_correct - /(_ _ x H).
    Qed.

    Lemma findMin_cases : forall h, (exists x, Some x = findMin h) \/ (h = E).
    Proof.
      case=> [|n z h1 h2 /=]; first by right.
      by left; exists z.
    Qed.
    
    Theorem findMin_LE_correct : forall x h,
      HeapOrder h ->
      (x ? h /\ LE x h) <-> (Some x = findMin h).
    Proof.
      split=> [[]|]; move: h H=> [] //.
      - move=> n y h1 h2 H /case_member [-> //|[HH|HH] /case_LE XY];
        suffices: x = y=> [-> //|]; move: H.
      - move=> /case_HeapOrder_l [] /LE_correct L /(L _ _ HH) YX.
      apply: le_anti. by apply/andP.
      - move=> /case_HeapOrder_r [] /LE_correct L /(L _ _ HH) YX.
      apply: le_anti. by apply/andP.
      move=> n s h1 h2 HO [] ->; split=> /=. 
      - by rewrite eq_refl.
      by apply lexx.
    Qed.

    Definition deleteMin (h : Heap) :=
      if h is T _ _ a b then merge a b else E.

    Lemma Rank_Rk_eq n x h1 h2 :
      Rank_Rk (T n x h1 h2) -> n = (rk h2).+1.
    Proof. by move=> /andP[/andP[/eqP]]. Qed.
    
    Lemma case_LE' x y h1 h2 n :
      LE x (T n y h1 h2) -> ((x <= y) = true).
    Proof. by move=> /= ->. Qed.

    Lemma rk1 : forall m y h1 h2,
      (1 <= rk (T m y h1 h2))%N.
    Proof. move=> m y h1 h2 /=. ssrnatlia. Qed.

    Lemma rank1 : forall m y h1 h2,
    Rank_Rk (T m y h1 h2) -> (1 <= rank (T m y h1 h2))%N.
    Proof. move=> m y h1 h2 /rank_correct <-. by apply rk1. Qed.
    
    Lemma rk0: rk E = 0.
    Proof. by []. Qed.
    
    Lemma rank0: rank E = 0.
    Proof. by []. Qed.

    Lemma LI_exfalso n x m y h1 h2 :
      LeftistHeap (T n x E (T m y h1 h2)) -> False.
    Proof.
      move=> [/= /andP[/andP[/andP[]]]] LI1 LI2 rr M0 [/andP[/andP[]]] _
        /andP[/andP[/eqP M RR1 RR2 _]] _.
      by move : M M0=>-> //.
    Qed.

    Lemma case_LeftistHeap_l n x h1 h2 :
    LeftistHeap (T n x h1 h2) -> LeftistHeap h1.
    Proof.
      move=> [/case_Leftist_Inv_l LI [/Rank_Rk_l RR /case_HeapOrder_l [HO _]]].
      split=> [//|]; by split.
    Qed.
    
    Lemma case_LeftistHeap_r n x h1 h2 :
    LeftistHeap (T n x h1 h2) -> LeftistHeap h2.
    Proof. 
      move=> [/case_Leftist_Inv_r LI2 [/Rank_Rk_r RR /case_HeapOrder_r [HO _]]].
      split=> [//|]; by split.
    Qed.
    
    Lemma deleMin_preserve_rk_inv : forall h, 
      Rank_Rk h -> Rank_Rk (deleteMin h).
    Proof.
      by case=> //=n x h1 h2 H; apply merge_preserve_rk_inv; move: H=> /andP[/andP[]].
    Qed.
    
    Lemma deleMin_preserve_HO_inv : forall h, 
      HeapOrder h -> HeapOrder (deleteMin h).
    Proof.
      by case=> //=n x h1 h2 H; apply merge_preserve_HO_inv; move: H=> /andP[/andP[]].
    Qed.

    Lemma deleMin_preserve_LI_inv : forall h, 
      Leftist_Inv h -> Leftist_Inv (deleteMin h).
    Proof.
      by case=> //=n x h1 h2 H; apply merge_preserve_LI_inv; move: H=> /andP[/andP[]].
    Qed.

    Lemma deleMin_correct : forall h, 
      LeftistHeap h -> LeftistHeap (deleteMin h).
    Proof.
      case=> //=n x h1 h2 H; apply merge_preserve_LH; move: H.
      - by move/case_LeftistHeap_l.
      by move/case_LeftistHeap_r.
    Qed.

    Theorem deleteMin_spec : forall h x y,
      Some x = findMin h -> (y ? (insert x (deleteMin h))) <-> y ? h.
    Proof.
      case=> [//=|n x h1 h2 y z [->]];
      by rewrite insert_correct /= merge_spec case_member.
    Qed.
    
    Definition isEmpty (h : Heap) :=
      if h is E then true else false.

    Theorem emptyP h : reflect (h = E) (isEmpty h).
    Proof. by case h; constructor. Qed.

    Fixpoint insert' (x : Elem) (h : Heap) :=
      if h is T n y a b then
      let h' := T n y a b in 
        if x <= y then
          T 1 x h' E
        else makeT y a (insert' x b)
      else T 1 x E E.
    
    Theorem insertE x h : Rank_Rk h -> Leftist_Inv h -> insert' x h = insert x h.
    Proof.
      rewrite /insert.
      elim h=> [//|n y h1 IHh1 h2 IHh2 RR]; move : RR (RR)=> /rank1.
      case H : (x <= y); merge_cases. rewrite /makeT => /lt_le -> //.
      move=> _ /andP[/andP[nr RR1 RR2]] /andP[/andP[LI1 LI2 rr]].
      by rewrite IHh2.
    Qed.
    
  End LeftistDef.
End LeftistHeap.
Module WBLeftistHeap.
(*Weight-biased leftist heaps are an al-
ternative to leftist heaps that replace the leftist property with the weight-biased
leftist property: the size of any left child is at least as large as the size of its
right sibling.*)
  Section WBLeftistDef.
  Variables (Elem : ordType).

  Inductive Heap :=
  | E : Heap
  | T : nat -> Elem -> Heap -> Heap -> Heap.
Print negbT.
  Fixpoint rank (H : Heap) : nat :=
  if H is T r _ _ _ then r else O.

  Definition makeT (x : Elem) (a b : Heap) : Heap :=
    if rank a >= rank b then 
      T ((rank b) + (rank a) + 1) x a b
    else T ((rank b) + (rank a) + 1) x b a.
  
  Fixpoint size (h : Heap) : nat :=
  if h is T _ _ a b then (size b) + (size a) + 1 else O.

  Definition isEmpty (h : Heap) :=
  if h is E then true else false.
  

  Program Fixpoint merge (a b : Heap) {measure (size a + size b)} : Heap :=
    match a, b with
    | h, E => h
    | E, h => h
    | T n x a1 b1, T m y a2 b2 =>
    let h1 := T n x a1 b1 in
    let h2 := T m y a2 b2 in
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
  
  Definition insert (x : Elem) (h : Heap) := 
              merge (T 1 x E E) h.

  Definition findMin (h : Heap) := 
    if h is T _ x _ _ then Some x else None.
  
  Definition deleteMin (h : Heap) :=
    if h is T _ _ a b then merge a b else E.
  
    Program Fixpoint merge' (a b : Heap) {measure (size a + size b)} : Heap :=
    match a, b with
    | h, E => h
    | E, h => h
    | T w1 x a1 b1, T w2 y a2 b2 =>
    let h1 := T w1 x a1 b1 in
    let h2 := T w2 y a2 b2 in
      if leq x y then
        if size a1 >= (size b1) + w2 then 
          T (w1 + w2) x a1 (merge' b1 h2)
        else T (w1 + w2) x (merge' b1 h2) a1
      else
        if size a2 >= w1 + size b2 then
          T (w1 + w2) y a2 (merge' h1 b2)
        else T (w1 + w2) y (merge' h1 b2) a2
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
End WBLeftistHeap.
