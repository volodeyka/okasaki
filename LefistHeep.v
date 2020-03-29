From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype.
Require Import ssrlia.
Require Import Psatz. Require Import Arith.
Import Order.TTheory.
Notation ordType := (orderType tt).
Require Import Coq.Program.Wf.

Open Scope order_scope.

Module LIFTISTHEAP.
(*Leftist heaps are heap-ordered binary trees that satisfy the
leftist property: the rank of any left child is at least as large as the rank of its
right sibling. The rank of a node is defined to be the length of its right spine
(i.e., the rightmost path from the node in question to an empty node). A simple
consequence of the leftist property is that the right spine of any node is always
the shortest path to an empty node.*)
  Section LeftistDef.
    Variables (Elem : ordType).

    Lemma boolean_lem : forall a b, a && b -> b.
    Proof.
      by case=> [].
    Qed.
    
    Lemma boolean_lem1 : forall a, a = false -> ~~ a.
    Proof.
      by case.
    Qed.

    Hint Resolve lexx : core.    

    Lemma leF_le : forall (x y : Elem), ((x <= y) = false) -> (y <= x).
    Proof.
      move=> x y H.
      suffices: y < x. rewrite lt_neqAle. apply boolean_lem.
      suffices: ~~(x <= y).
      rewrite leNgt. by case: (y < x).
      by apply boolean_lem1.
    Qed.

    Inductive Heap :=
    | E : Heap
    | T : nat -> Elem -> Heap -> Heap -> Heap.

    Inductive LE : Elem -> Heap -> Prop :=
    | LE_x_E : forall x, LE x E
    | LE_x_T : forall (x y : Elem) a b n, ((x <= y) = true) -> LE x (T n y a b).

    Hint Resolve LE_x_E : core.

    Inductive HeapOrder : Heap -> Prop :=
    | HO_E : HeapOrder E
    | HO_T : forall x tl tr n (L1 : LE x tl) (L2 : LE x tr) 
              (HO1: HeapOrder tl) (HO2 : HeapOrder tr),
              HeapOrder (T n x tl tr).
    
    Hint Resolve HO_E : core.

    Fixpoint rk (h : Heap) : nat :=
      if h is T _ _ _ b then (rk b).+1 else O.

    Inductive Rank_Rk : Heap -> Prop :=
    | RR_E : Rank_Rk E
    | RR_T : forall x tl tr (RR_Tl : Rank_Rk tl) (RR_Tr : Rank_Rk tr),
             Rank_Rk (T (rk tr).+1 x tl tr).
    
    Hint Resolve RR_E : core.
    
    Fixpoint rank (H : Heap) : nat :=
    if H is T r _ _ _ then r else O.

    Inductive Leftist_Inv : Heap -> Prop :=
    | LI_E : Leftist_Inv E
    | LI_T : forall x tl tr n (LI_Tl : Leftist_Inv tl) (LI_Tr : Leftist_Inv tr)
             (RK : (rank tr <= rank tl)%N), Leftist_Inv (T n x tl tr).
    
    Hint Resolve LI_E : core.

    Lemma rank_correct : forall H, Rank_Rk H -> rk H = rank H.
    Proof. move=> H [] //. Qed.

    Inductive side := r | l.
  
    Definition spine := seq side.

    Inductive spine_in : spine -> Heap -> Prop :=
    | SI_E : spine_in nil E
    | SI_Tr : forall n x tr tl p
                       (Spine : spine_in p tr),
                       spine_in (r :: p) (T n x tl tr)
    | ST_Tl : forall n x tr tl p
                       (Spine : spine_in p tl),
                       spine_in (l :: p) (T n x tl tr).
    
    Hint Resolve SI_E : core.

    Inductive Right : spine -> Prop :=
    | R_nil : Right nil
    | R_cons : forall s, Right s -> Right (r :: s).
    
    Hint Resolve R_nil : core.
    
    Lemma Rigth_correct : forall x s, Right (x :: s) -> (x = r /\ Right s).
    Proof. by move=> x s H; inversion H. Qed.

    Lemma spine_in_rl : forall side s n x tl tr, 
      spine_in (side :: s) (T n x tl tr) -> 
      if side is r then spine_in s tr else spine_in s tl.
    Proof. by move=> [] s n x tl tr H; inversion H. Qed. 

    Definition Leftist_Rank_Inv (H : Heap) := Leftist_Inv H /\ Rank_Rk H.


    Lemma Leftist_inv_r: forall n x tl tr,
      Leftist_Rank_Inv (T n x tl tr) -> Leftist_Rank_Inv tr.
    Proof. by move=> n x tl tr [] H H'; inversion H; inversion H'. Qed.
    
    Lemma Leftist_inv_rl: forall n x tl tr,
      Leftist_Rank_Inv (T n x tl tr) -> 
      Leftist_Rank_Inv tr /\ Leftist_Rank_Inv tl /\ (rank tr <= rank tl)%N.
    Proof. by move=> n x tl tr [] H H'; inversion H; inversion H'. Qed.

    Lemma case_Rank_Rk n y h1 h2 : 
    Rank_Rk (T n y h1 h2) -> (n = (rk h2).+1) /\ (Rank_Rk h1) /\ (Rank_Rk h2).
  Proof. by move=> H; inversion H. Qed.
  
  Lemma case_HeapOrder n y h1 h2 : 
    HeapOrder (T n y h1 h2) ->
    LE y h1 /\ LE y h2 /\ (HeapOrder h1) /\ (HeapOrder h2).
  Proof. by move=> H; inversion H. Qed.      
    
  
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
  Proof.
    by move=> H; inversion H.
  Qed.

  Lemma leq_1 : forall (a b : nat), (a <= b)%N -> (a.+1 <= b.+1)%N.
    Proof. by move=> a b H; ssrnatlia. Qed.

    Lemma Right_spine_ex : forall H, exists s, Right s /\ spine_in s H.
    Proof.
      elim=> [|n s hl _ hr [] s' [] IHHR IHHS].
      - by exists nil.
      by exists (r :: s'); split; constructor.
    Qed.

    Lemma length_right_spine : forall H s, 
    Leftist_Rank_Inv H -> Right s -> spine_in s H ->
    length s = rank H.
    Proof.
      move=> h s [] _ RC; move: (RC)=> /rank_correct <-.
      elim: h s RC=> 
      [s _ _ H|n x tl IHhl tr IHtr [_ _ H|
      [s H /Rigth_correct [] _ RS /spine_in_rl SIr|s _ F]]] /=;
      try by inversion H.
      - inversion H; rewrite PeanoNat.Nat.succ_inj_wd.
        by apply: (IHtr s RR_Tr RS SIr).
      by inversion F.
    Qed.
    
    Theorem rigth_spine_shortest : 
      forall H s1 s2, Right s1 -> Leftist_Rank_Inv H -> spine_in s1 H -> spine_in s2 H ->
      (length s1 <= length s2)%nat.
    Proof. 
      elim=> 
      [s1 s2 _ H1 H2 _|
      n x tl IHtl tr IHtr [//|
      a s1 [/Rigth_correct [] -> _ _ _ H|
      a' s2 /Rigth_correct [] ->]]] /=.
      - inversion H1; inversion H2=> //.
      - inversion H.
      move: a'=> [Rs1 /Leftist_inv_r LI|
                  Rs1 /Leftist_inv_rl [] LI1 [] LI2 LE]
                  /spine_in_rl SI1 /spine_in_rl SI2.
      - apply: leq_1; apply IHtr=> //.
      rewrite (length_right_spine _ _ LI1 Rs1 SI1).
      case: (Right_spine_ex tl)=> s [] Rs SIstl.
      suffices: (rank tl <= length s2)%N. ssrnatlia.
      rewrite -(length_right_spine _ _ LI2 Rs SIstl).
      by apply: IHtl.
    Qed.

    Definition makeT (x : Elem) (a b : Heap) : Heap :=
      if (rank b <= rank a)%N then T (rank b).+1 x a b else T (rank a).+1 x b a.

    Lemma nlt_gt : forall a b, (a <= b)%N = false -> (b < a)%N.
    Proof.
      Print leq.
      move=> a b /neq0_lt0n. ssrnatlia.
    Qed.    

    Lemma makeT_preserves_LI_inv : forall x tl tr,
      Leftist_Inv tl -> Leftist_Inv tr ->
      Leftist_Inv (makeT x tl tr).
    Proof.
        move=> x tl tr LIl LIr; rewrite /makeT.
        case H : (rank tr <= rank tl)%N; constructor=> //.
        move: H=> /nlt_gt. by ssrnatlia.
    Qed.

    Lemma makeT_preserves_rk_inv x tl tr :
      Rank_Rk tl -> Rank_Rk tr ->
      Rank_Rk (makeT x tl tr).
    Proof.
      move=> Rl Rr; rewrite /makeT -!(rank_correct _ Rl) -!(rank_correct _ Rr).
      by case H : (rk tr <= rk tl)%N; constructor=> //.  
    Qed.
    
    Lemma makeT_peserves_HO_inv x tl tr :
      HeapOrder tl -> HeapOrder tr ->
      LE x tl -> LE x tr ->
      HeapOrder (makeT x tl tr).
    Proof.
      move=> Hl Hr LEl LEr; rewrite /makeT.
      by case H : (rank tr <= rank tl)%N; constructor=> //.
    Qed.
    

    Reserved Notation "x ? h" (at level 0).

    Inductive member : Elem -> Heap -> Prop :=
    | M_x_Tx : forall x n tl tr, x ? (T n x tl tr)
    | M_x_Tl : forall x y n tl tr, x ? tl -> x ? (T n y tl tr)
    | M_x_Tr : forall x y n tl tr, x ? tr -> x ? (T n y tl tr)
    where "x ? h" := (member x h).

    Hint Resolve M_x_Tx : core.

    (*Program Fixpoint merge (a b : Heap) {measure (rk a + rk b)} : Heap :=
      match a, b with
      | h, E => h
      | E, h => h
      | T n x a1 b1, T m y a2 b2 =>
      let h1 := T n x a1 b1 in
      let h2 := T m y a2 b2 in
        if x <= y then
          makeT x a1 (merge b1 h2)
        else
          makeT y a2 (merge h1 b2)
      end.
    Next Obligation.
      rewrite addnC (addnC (rk b1).+1 (rk b2).+1).
      by apply: Nat.add_lt_le_mono; lia.
    Qed.*)

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

    Ltac inv := match goal with
    | |- _ -> _ => by move=> H; inversion H
    end.
    Lemma merge_E_h: forall h, merge E h = h.
    Proof. by case=> //=. Qed.
    Hint Rewrite merge_E_h.

    Lemma merge_h_E: forall h, merge h E = h.
    Proof. by case=> //=. Qed.
    Hint Rewrite merge_h_E.

    Lemma Rank_Rk_r n x tl tr:
      Rank_Rk (T n x tl tr) -> Rank_Rk tr.
    Proof. inv. Qed.

    Lemma Rank_Rk_l n x tl tr :
      Rank_Rk (T n x tl tr) -> Rank_Rk tl.
    Proof. inv. Qed.

    Lemma merge_a nl nr x y tll tlr trr trl :
      (x <= y) = false -> 
      merge (T nl x tll tlr) (T nr y trl trr) = 
      makeT y trl (merge  (T nl x tll tlr) trr).
    Proof.
      move=> /= ->.
      by elim: trr=> //=.
    Qed.
    
    Hint Rewrite merge_a.
    Lemma merge_preserve_rk_inv : forall h1 h2,
      Rank_Rk h1 -> Rank_Rk h2 -> Rank_Rk (merge h1 h2) .
    Proof.
      elim=> [//| nl x tll IHhl tlr IHhr].
      elim=> [|nr y trl IH'hl trr IH'hr] //.
      case H : (x <= y)=> H1 H2; merge_cases;
      move: (H1) (H2) => /= /case_Rank_Rk [_ [HH1 HH2]] /case_Rank_Rk [_ [HH3 HH4]];
      apply makeT_preserves_rk_inv=> //.
      - by apply IHhr.
      by apply IH'hr.
    Qed.
    
    Lemma case_HeapOrder_l n x tl tr :
      HeapOrder (T n x tl tr) -> (HeapOrder tl /\ LE x tl).
    Proof. inv. Qed.
    
    Lemma case_HeapOrder_r n x tl tr :
      HeapOrder (T n x tl tr) -> (HeapOrder tr /\ LE x tr).
    Proof. inv. Qed.

    Lemma case_LE x y n tr tl :
      LE x (T n y tl tr) -> x <= y.
    Proof. inv. Qed.
    
    Ltac makeT_cases := match goal with
    | H : (?a <= ?b)%N = _ |- _ => rewrite /makeT; move : H => /= ->
    end.

    Ltac makeT_casesxy x y := case fresh : (x <= y)%N; makeT_cases.

    Lemma merge_preserve_LE : forall h1 h2 x,
      LE x h1 -> LE x h2 -> LE x (merge h1 h2).
    Proof.
      elim=> [//| nl x tll IHhl tlr IHhr].
      elim=> [|nr y trl IH'hl trr IH'hr x' /case_LE HH1 /case_LE HH2] //.
      merge_casesxy x y; 
      [makeT_casesxy (rank (merge tlr (T nr y trl trr))) (rank tll)|
       makeT_casesxy (rank (merge (T nl x tll tlr) trr)) (rank trl)];
      try by constructor.
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
      all : apply: merge_preserve_LE=> //; constructor=> //.
      by apply: (leF_le _ _ H).
    Qed.

    Lemma Leftist_Inv_l : forall n x tl tr,
    Leftist_Inv (T n x tl tr) -> Leftist_Inv tl.
    Proof. by move=> n x tl tr H; inversion H. Qed.

    Lemma Leftist_Inv_r : forall n x tl tr,
    Leftist_Inv (T n x tl tr) -> Leftist_Inv tr.
    Proof. by move=> n x tl tr H; inversion H. Qed.
    
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
      split; first by move=> H; inversion H; [left|right; left|right; right].
      by case=> [->|[/M_x_Tl|/M_x_Tr]].
    Qed.
    Hint Resolve M_x_Tx : core.
    Lemma makeT_correct h1 h2 x y :
      x ? (makeT y h1 h2) <-> (x = y) \/ (x ? h1) \/ (x ? h2).
    Proof.
    makeT_casesxy (rank h2) (rank h1).
    (*M_x_Tl : forall x y n tl tr, x ? tl -> x ? (T n y tl tr)*) 
      split => /case_member // [|[]].
      split=> [/case_member // [|[]]| 
      [->|[/(M_x_Tr x y (rank h1).+1 h2 h1)|
           /(M_x_Tl x y (rank h1).+1 h2 h1)]]] //.
      - by left.
      - by right; right.
      - by right; left.
    Qed.    
    Ltac member_left := match goal with
    | H : ?x ? ?h1 |- ?x ? (T _ _ ?h1 ?h2) => by apply M_x_Tl
    end.
    
    Theorem merge_correct : forall h1 h2 x,
      x ? (merge h1 h2) <-> (x ? h1) \/ (x ? h2).
    Proof.
      split.
      - elim: h1 h2=> [h2|n y h1 IHh1 h2 IHh2].
      - rewrite merge_E_h=> H; by right.
      - elim=> [|m z h21 IHh21 h22 IHh22]; first by rewrite merge_h_E=> H; left.
      - merge_casesxy y z=> /makeT_correct [-> |[HH|]].
      - by left.
      - by left; apply M_x_Tl.
      - move=> /IHh2 [] xMh2; [left; apply: M_x_Tr|]=> //.
      1,2: by right.
      - by right; apply M_x_Tl.
      - by move=> /IHh22 []; [left|right; apply: M_x_Tr].

      - elim: h1 h2=> [h [F|H]|n y h11 IHh1 h22 IHh2]; rewrite ?merge_E_h //;
        first by inversion F.
      - elim=> [[] // F|m z h12 IHh12 h21 IHh21]; rewrite ?merge_h_E; 
        first by inversion F.
      merge_casesxy y z; case=> /case_member [|[HH|HH]]; rewrite makeT_correct.
      - by left.
      - by right; left.
      1-4: right; right; apply IHh2.
      - by left.
      1- 3: right.
      - by rewrite H0.
      - by apply M_x_Tl.
      - by apply M_x_Tr.
      1-3, 6: right; right; apply IHh21.
      - by rewrite H0; left.
      - by left; apply M_x_Tl.
      - by left; apply M_x_Tr.
      - by right.
      - by left.
      - by right; left.
    Qed.

    Definition insert (x : Elem) (h : Heap) := 
      merge (T 1 x E E) h.
    
    Lemma rk_E : ((rk E).+1 = 1)%N.
    Proof. by []. Qed.    

    Lemma insert_preserve_rk_inv : forall h x,
      Rank_Rk h -> Rank_Rk (insert x h).
    Proof.
      move=> h x Rh; apply merge_preserve_rk_inv=> //.
      rewrite -rk_E. by apply RR_T.
    Qed.

    Lemma insert_preserve_HO_inv : forall h x,
      HeapOrder h -> HeapOrder (insert x h).
    Proof.
      move=> h x Rh; apply merge_preserve_HO_inv=> //.
      by apply HO_T.
    Qed.

    Lemma insert_preserve_LI_inv : forall h x,
      Leftist_Inv h -> Leftist_Inv (insert x h).
    Proof.
      move=> h x Rh; apply merge_preserve_LI_inv=> //.
      by apply LI_T.
    Qed.

    Theorem insert_preserve_LH : forall h x,
      LeftistHeap h -> LeftistHeap (insert x h).
    Proof.
      move=> h x Rh; apply merge_preserve_LH=> //.
      split; first by apply LI_T.
      split; first by rewrite -rk_E; apply RR_T.
      by apply HO_T.
    Qed.
    
    Lemma x_Ty : forall x y, (x) ? (T 1 y E E) <-> (x = y).
    Proof.
      move=> x y.
      split=> [H|->].
      - inversion H=> //; inversion H2.
      by apply M_x_Tx.
    Qed.

    Theorem insert_correct : forall h x y,
    x ? (insert y h) <-> (x = y) \/ (x ? h).
    Proof.
      move=> h x y.
      by rewrite merge_correct x_Ty.
    Qed.
    
    Definition findMin (h : Heap) := 
      if h is T _ x _ _ then Some x else None.

    Theorem findMin_correct1 : forall h,
      None = findMin h <-> h = E.
    Proof. split=> [|-> //]. move: h. by case. Qed.
    
    Lemma LE_correct : forall h x y,
      HeapOrder h -> x ? h -> LE y h -> y <= x.
    Proof.
      elim=> [x y _ H| n x h1 IHh1 h2 IHh2 x' y' HO /case_member 
      [-> /case_LE //|[H|H] /case_LE] ];
      first by inversion H.
      move: HO=> /case_HeapOrder_l [] /IHh1 H1 /(H1 x' x H) H2 H3.
      2: move: HO=> /case_HeapOrder_r [] /IHh2 H1 /(H1 x' x H) H2 H3.
      all: move: H3 H2; apply le_trans.
    Qed.

    Theorem findMin_correct2 : forall h, HeapOrder h ->
      forall z, Some z = findMin h -> forall x, x ? h -> z <= x.
    Proof.
      case=> [//| n x h1 h2 HO z /= [->] y /case_member [-> //|[H|H]]].
      - by move: HO=> /case_HeapOrder_l [] /LE_correct - /(_ _ x H).
      - by move: HO=> /case_HeapOrder_r [] /LE_correct - /(_ _ x H).
    Qed.

    Lemma findMin_cases : forall h, (exists x, Some x = findMin h) \/ (h = E).
    Proof.
      case=> [|n z h1 h2 /=]; first by right.
      by left; exists z.
    Qed.
    Lemma boolean_lemm : forall (a b : bool), a -> b -> a && b.
    Proof.
      case=> [] //.
    Qed.
    
    Theorem findMin_LE_correct : forall x h,
      HeapOrder h ->
      (x ? h /\ LE x h) <-> (Some x = findMin h).
    Proof.
      split=> [[]|]; move: h H=> [] //=.
      - move=> H F; inversion F.
      - move=> n y h1 h2 H /case_member [-> //|[HH|HH] /case_LE XY];
        suffices: x = y=> [-> //|]; move: H.
      - move=> /case_HeapOrder_l [] /LE_correct L /(L _ _ HH) YX.
      apply: le_anti. by apply: boolean_lemm=> //.
      - move=> /case_HeapOrder_r [] /LE_correct L /(L _ _ HH) YX.
      apply: le_anti. by apply: boolean_lemm=> //.
      move=> n s h1 h2 HO [] ->; split=> [//|]. apply LE_x_T. by apply lexx.
    Qed.
    Definition deleteMin (h : Heap) :=
      if h is T _ _ a b then merge a b else E.

    Lemma Rank_Rk_eq : forall n x h1 h2,
      Rank_Rk (T n x h1 h2) -> n = (rk h2).+1.
    Proof. by move=> n x h1 h2 H; inversion H. Qed.
    
    Lemma case_LE' : forall x y h1 h2 n,
      LE x (T n y h1 h2) -> ((x <= y) = true).
    Proof.
      by move=> x y h1 h2 n H; inversion H.
    Qed.

    Lemma rk1 : forall m y h1 h2,
      (1 <= rk (T m y h1 h2))%N.
    Proof.
      move=> m y h1 h2 /=. ssrnatlia.
    Qed.

    Lemma rank1 : forall m y h1 h2,
    Rank_Rk (T m y h1 h2) -> (1 <= rank (T m y h1 h2))%N.
    Proof.
      move=> m y h1 h2 /rank_correct <-. by apply rk1.
    Qed.
    
    Lemma rk0: rk E = 0.
    Proof.
      by [].
    Qed.
    
    Lemma rank0: rank E = 0.
    Proof.
      by [].
    Qed.

    Lemma LI_exfalso n x m y h1 h2 :
      LeftistHeap (T n x E (T m y h1 h2)) -> False.
    Proof.
      move=> [LI [RR HO]].
      inversion LI. exfalso.
      suffices: (1 <= 0)%N.
      - ssrnatlia.
      move: RK. rewrite -!rank_correct ?rk0.
      move: (rk1 m y h1 h2). apply leq_trans.
      - by [].
      by move: RR=> /Rank_Rk_r.
    Qed.

    Lemma case_LeftistHeap_l n x h1 h2 :
    LeftistHeap (T n x h1 h2) -> LeftistHeap h1.
    Proof.
      move=> [/Leftist_Inv_l LI [/Rank_Rk_l RR /case_HeapOrder_l [HO _]]].
      split=> [//|]; by split.
    Qed.
    
    Lemma case_LeftistHeap_r n x h1 h2 :
    LeftistHeap (T n x h1 h2) -> LeftistHeap h2.
    Proof.
      move=> [/Leftist_Inv_r LI [/Rank_Rk_r RR /case_HeapOrder_r [HO _]]].
      split=> [//|]; by split.
    Qed.
    
    Lemma deleMin_preserve_rk_inv : forall h, 
      Rank_Rk h -> Rank_Rk (deleteMin h).
    Proof.
      case=> //=n x h1 h2 H. apply merge_preserve_rk_inv; move: H.
      - by move/Rank_Rk_l.
      by move/Rank_Rk_r.
    Qed.
    
    Lemma deleMin_preserve_HO_inv : forall h, 
      HeapOrder h -> HeapOrder (deleteMin h).
    Proof.
      case=> //=n x h1 h2 H. apply merge_preserve_HO_inv; move: H.
      - by move=>/case_HeapOrder_l [].
      by move=>/case_HeapOrder_r [].
    Qed.

    Lemma deleMin_preserve_LI_inv : forall h, 
      Leftist_Inv h -> Leftist_Inv (deleteMin h).
    Proof.
      case=> //=n x h1 h2 H. apply merge_preserve_LI_inv; move: H.
      - by move/Leftist_Inv_l.
      by move/Leftist_Inv_r.
    Qed.

    Lemma deleMin_correct : forall h, 
      LeftistHeap h -> LeftistHeap (deleteMin h).
    Proof.
      case=> //=n x h1 h2 H. apply merge_preserve_LH; move: H.
      - by move/case_LeftistHeap_l.
      by move/case_LeftistHeap_r.
    Qed.

    Theorem deleteMin_spec : forall h x y,
      Some x = findMin h -> (y ? (insert x (deleteMin h))) <-> y ? h.
    Proof.
      case=> [//=|n x h1 h2 y z [->]];
      by rewrite insert_correct /= merge_correct case_member.
    Qed.
    
    Definition isEmpty (h : Heap) :=
      if h is E then true else false.

    Theorem emptyP h : reflect (h = E) (isEmpty h).
    Proof.
      by case h; constructor.
    Qed.

    Fixpoint memb x (h : Heap) :=
      if h is T _ y a b then
        if (x == y) then true else (memb x a) || (memb x b) else false.    

    Theorem memberP x h : reflect (x ? h) (memb x h).
    Proof.
      elim h=> [|n y h1 IHh1 h2 IHh2 /=]; first by constructor=> F; inversion F.
      apply (@iffP (x = y \/ (x ? h1) \/ (x ? h2))); rewrite ?case_member //.
      apply: (iffP orP); case=> [/eqP H|]; try by left; try by right.
      - by move=> /orP [/IHh1| /IHh2]; [right; left| right; right].
      by case; right; apply/orP; [left; apply/IHh1|right; apply/IHh2].
    Qed.

    
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
      elim h=> [//=|n y h1 IHh1 h2 IHh2 RR]; move : RR (RR)=> /rank1.
      case H : (x <= y); merge_cases. rewrite /makeT /= => /lt_le -> //.
      move=> _; swapg=> /case_Leftist_inv [RR [LI _]] /Rank_Rk_r/IHh2 <- //.
    Qed.
    
  End LeftistDef.
End LIFTISTHEAP.
Module WBLIFTISTHEAP.
(*Weight-biased leftist heaps are an al-
ternative to leftist heaps that replace the leftist property with the weight-biased
leftist property: the size of any left child is at least as large as the size of its
right sibling.*)
  Section WBLeftistDef.
  Variables (Elem : ordType).

  Inductive Heap :=
  | E : Heap
  | T : nat -> Elem -> Heap -> Heap -> Heap.

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
End WBLIFTISTHEAP.
