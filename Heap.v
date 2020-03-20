From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import Lia.
Require Import Omega.
Require Import Arith.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import BinSrcTree.

(*Require Import Stack.*)

Set Implicit Arguments.

Module HEAP.
    Record class (Heap : Type) := Class
    {
        Element : ordType;

        Empty : Heap;
        IsEmpty : Heap -> bool;

        Insert : Element -> Heap -> Heap;
        Merge : Heap -> Heap -> Heap;

        FindMin : Heap -> option Element;
        DeleteMin : Heap -> Heap; 
    }.
    Structure type := Pack { sort : Type; class_of : class sort }.

    Section Exports.
    
    Coercion sort : type >-> Sortclass.
    Variables (H : type).
    Definition Elem      := Element (class_of H).
    Definition insert    := Insert (class_of H).
    Definition merge     := Merge (class_of H).
    Definition isEmpty   := IsEmpty (class_of H).
    Definition findMin   := FindMin (class_of H).
    Definition deleteMin := DeleteMin (class_of H).
    Definition empty     := Empty (class_of H).
    
    End Exports.
    Arguments Class {_}.

End HEAP.


Module LIFTISTHEAP.
(*Leftist heaps are heap-ordered binary trees that satisfy the
leftist property: the rank of any left child is at least as large as the rank of its
right sibling. The rank of a node is defined to be the length of its right spine
(i.e., the rightmost path from the node in question to an empty node). A simple
consequence of the leftist property is that the right spine of any node is always
the shortest path to an empty node.*)
  Section LeftistDef.
    Variables (Elem : ordType).

    Inductive Heap :=
    | E : Heap
    | T : nat -> Elem -> Heap -> Heap -> Heap.

    Fixpoint rank (H : Heap) : nat :=
    if H is T r _ _ _ then r else O.

    Definition makeT (x : Elem) (a b : Heap) : Heap :=
      if rank a >= rank b then T (rank b).+1 x a b else T (rank a).+1 x b a.
    
    Fixpoint rk (h : Heap) : nat :=
    if h is T _ _ _ b then (rk b).+1 else O.

    Program Fixpoint merge (a b : Heap) {measure (rk a + rk b)} : Heap :=
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
    Next Obligation.
    Print Nat.add_lt_le_mono.
      simpl. rewrite addnC. 
      replace ((rk b1).+1 + (rk b2).+1) with ((rk b2).+1 + (rk b1).+1).
      - apply Nat.add_lt_le_mono; lia.
      by rewrite addnC. 
    Qed.
    
    Definition insert (x : Elem) (h : Heap) := 
                merge (T 1 x E E) h.

    Definition findMin (h : Heap) := 
      if h is T _ x _ _ then Some x else None.
    
    Definition deleteMin (h : Heap) :=
      if h is T _ _ a b then merge a b else E.

    Definition isEmpty (h : Heap) :=
      if h is E then true else false.

    Fixpoint insert' (x : Elem) (h : Heap) :=
      if h is T n y a b then
      let h' := T n y a b in 
        if leq x y then
          T 1 x h' E
        else T n y (insert' x a) b
      else T 1 x E E.
  End LeftistDef.

Arguments Heap      {_}.
Arguments insert    {_}.
Arguments merge     {_}.
Arguments isEmpty   {_}.
Arguments findMin   {_}.
Arguments deleteMin {_}.
Arguments E         {_}.

Definition LeftistClass (Elem : ordType) : HEAP.class Heap :=
  HEAP.Class Elem E isEmpty insert merge findMin deleteMin.
Canonical LeftistHeap (Elem : ordType) : HEAP.type :=
  HEAP.Pack (LeftistClass Elem).

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

  Lemma arithmetics1 (n m k l : nat) : 
   (n + (m + k + 1) < n + l + 1 + (m + k + 1))%coq_nat.
  Proof.
    simpl. 
    replace (n + l + 1 + (m + k + 1))
    with ((l + 1) + (n + (m + k + 1))).
    Print Nat.add_lt_le_mono.
    - apply (Nat.add_lt_le_mono O (l + 1) (n + (m + k + 1))(n + (m + k + 1))).
      - rewrite addnC. apply (Nat.add_lt_le_mono O 1 O (l)); lia.
      - by lia.
        rewrite addnA.
        replace (l + 1 + n) with (n + l + 1).
        - by []. 
          rewrite <- addnA. by rewrite addnC.
  Qed.

  Lemma arithmetics2 (n m k l : nat): (n + m + 1 + l <
  n + m + 1 + (l + k + 1))%coq_nat.
  Proof.
    simpl.
    apply plus_lt_compat_l. rewrite <- addnA.
    replace (k + 1) with (1 + k).
    rewrite addnA.
    apply lt_plus_trans. rewrite addn1. apply Nat.lt_succ_diag_r.
    by rewrite addnC.
  Qed.
  

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
  Next Obligation.
    apply arithmetics1.
  Qed.
  Next Obligation.
    apply arithmetics2.
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
      by apply arithmetics1.
    Qed.
    Next Obligation.
      by apply arithmetics1.
    Qed.
    Next Obligation.
      by apply arithmetics2.
    Qed.
    Next Obligation.
      by apply arithmetics2.
    Qed.
  End WBLeftistDef.

Arguments Heap      {_}.
Arguments insert    {_}.
Arguments merge     {_}.
Arguments isEmpty   {_}.
Arguments findMin   {_}.
Arguments deleteMin {_}.
Arguments E         {_}.

Definition WBLeftistClass (Elem : ordType) : HEAP.class Heap :=
  HEAP.Class Elem E isEmpty insert merge findMin deleteMin.
Canonical WBLeftistHeap (Elem : ordType) : HEAP.type :=
  HEAP.Pack (WBLeftistClass Elem).
End WBLIFTISTHEAP.

Module BINOMHEAP.
  Section BinomHeap.
  Variables (Elem : ordType).

  Inductive Tree :=
  | Node : nat -> Elem -> list Tree -> Tree.

  Definition Heap := list Tree.
  Definition empty : Heap := [].
  

  Definition rank := fun '(Node r x c) => r.
  Definition root := fun '(Node r x c) => x.

  Fixpoint rk (Tr : Tree) :=
  match Tr with Node _ x c =>
  if c is h :: _ then (rk h).+1 else 1 end.

  Definition link (t1 t2 : Tree) : Tree :=
    match t1, t2 with 
    | Node r x1 c1, Node _ x2 c2 =>
    if leq x1 x2 then 
      Node r.+1 x1 (t2 :: c1)
    else Node r.+1 x2 (t1 :: c2)
    end.
  
  Fixpoint insTree (t : Tree) (ts : Heap) :=
    match t, ts with 
    | t, []        => [t]
    | t, t' :: ts' => if (rank t) < (rank  t') then
                        t :: ts
                      else  insTree (link t t') ts'
    end.

  Definition insert (x : Elem) (ts : Heap) := insTree (Node 0 x []) ts.

  Fixpoint size (ts : Heap) : nat :=
    if ts is t :: ts' then (rk t) + size ts' else O.

   (*Lemma arismeticts1 (n m l k : nat) (H : n > 0) : 
     (k + (m + l) < n + k + (m + l))%coq_nat.
   Proof.
     Search Peano.lt.
     rewrite <- addnA.
     apply Nat.lt_add_pos_l.
   Qed.*)
   Lemma pos_rk (t : Tree) : (0 < (rk t))%coq_nat.
   Proof.
     induction t.
     case l; simpl.
     - by [].
       move=> t l'.
       lia.
   Qed.


  Program Fixpoint merge (ts1 ts2 : Heap) {measure (size ts1 + size ts2)} : Heap :=
    match ts1, ts2 with
    | t, [] => t
    | [], t => t
    | t1 :: ts'1, t2 :: ts'2 => 
      if (rank t1 < rank t2) is true then
        t1 :: (merge ts'1 ts2)
      else
        if rank t2 < rank t1 is true then
          t2 :: (merge ts1 ts'2)
        else insTree (link t1 t2) (merge ts'1 ts'2)
    end.
    Next Obligation. 
      simpl.
      rewrite <- addnA.
      apply: (Nat.lt_add_pos_l _ _ (pos_rk t1)).
    Qed.
    Next Obligation.
      simpl.
      replace (rk t1 + size ts'1 + (rk t2 + size ts'2)) with
               (rk t1 + size ts'1 + size ts'2 + rk t2).
      - apply: (Nat.lt_add_pos_r _ _ (pos_rk t2)).
        replace (rk t2 + size ts'2) with (size ts'2 + rk t2).
        - rewrite addnA; by [].
          by rewrite addnC.
    Qed.
    Next Obligation.
      simpl.
      replace (rk t1 + size ts'1 + (rk t2 + size ts'2)) with
               ((size ts'1 + size ts'2) + (rk t1 + rk t2)).
      - apply Nat.lt_add_pos_r. 
        apply Nat.add_pos_pos; apply pos_rk.
        replace (rk t1 + size ts'1) with (size ts'1 + rk t1).
        rewrite <- addnA. rewrite <- addnA.
        apply Nat.add_cancel_l.
        rewrite addnC. rewrite <- addnA.
        by apply Nat.add_cancel_l.
        by rewrite addnC.
    Qed.

    Fixpoint removeMinTree (ts : Heap) : option (Tree * Heap) :=
      match ts with
      | []      => None
      | [t]     => Some (t, [])
      | t :: ts =>  if removeMinTree ts is Some (t', ts') then
                      if leq (root t) (root t') then
                        Some (t, ts) 
                      else Some (t', t :: ts)
                    else None
      end.

    Definition findMin (ts : Heap) : option Elem :=
      if (removeMinTree ts) is Some (t, _) then Some (root t) else None.
    
    Definition deleteMin (ts : Heap) : Heap :=
      if (removeMinTree ts) is Some (Node _ x ts1, ts2) then
        (merge (rev ts1) ts2)
      else [].
    
    Fixpoint findMin' (ts : Heap) : option Elem :=
      match ts with
      | [] => None
      | [Node _ y _] => Some y
      | (Node _ y _) :: ts' => 
                    if findMin ts' is Some x then
                      if lt x y then 
                        Some x
                      else Some y
                    else None
      end.

    Definition isEmpty (ts : Heap) :=
      if ts is [] then true else false.
  End BinomHeap.

Arguments Heap      {_}.
Arguments insert    {_}.
Arguments merge     {_}.
Arguments isEmpty   {_}.
Arguments findMin   {_}.
Arguments deleteMin {_}.
Arguments empty     {_}.


Definition BinomHeapClass (Elem : ordType) : HEAP.class Heap :=
  HEAP.Class Elem empty isEmpty insert merge findMin deleteMin.
Canonical BinomHeap (Elem : ordType) : HEAP.type :=
  HEAP.Pack (BinomHeapClass Elem).
End BINOMHEAP.

Module BINOMHEAP_RK.
  Section BinomHeap_rk.

  Variables (Elem : ordType).
  Inductive Tree :=
  | Node : Elem -> list Tree -> Tree.

  Definition Heap := list (nat * Tree).
  Definition empty : Heap := [].

  Definition root := fun '(Node x c) => x.

  Fixpoint rk (Tr : Tree) :=
  match Tr with Node x c =>
  if c is h :: _ then (rk h).+1 else 1 end.

  Definition link (t1 t2 : Tree) : Tree :=
    match t1, t2 with 
    | Node x1 c1, Node x2 c2 =>
    if leq x1 x2 then 
      Node x1 (t2 :: c1)
    else Node x2 (t1 :: c2)
    end.
  
  Fixpoint insTree (t : Tree) (ts : Heap) :=
    match t, ts with 
    | t, []        => [(rk t, t)]
    | t, t' :: ts' => let rkt := rk t in
                      if (rkt) < fst t' then
                        (rkt, t) :: ts
                      else  insTree (link t (snd t')) ts'
    end.

  Definition insert (x : Elem) (ts : Heap) := insTree (Node x []) ts.

  Fixpoint size (ts : Heap) : nat :=
    if ts is t :: ts' then (rk (snd t)) + size ts' else O.

   (*Lemma arismeticts1 (n m l k : nat) (H : n > 0) : 
     (k + (m + l) < n + k + (m + l))%coq_nat.
   Proof.
     Search Peano.lt.
     rewrite <- addnA.
     apply Nat.lt_add_pos_l.
   Qed.*)
   Lemma pos_rk (t : Tree) : (0 < (rk t))%coq_nat.
   Proof.
     induction t.
     case l; simpl.
     - by [].
       move=> t l'.
       lia.
   Qed.


  Program Fixpoint merge (ts1 ts2 : Heap) {measure (size ts1 + size ts2)} : Heap :=
    match ts1, ts2 with
    | t, [] => t
    | [], t => t
    | t1 :: ts'1, t2 :: ts'2 => 
      if (fst t1 < fst t2) is true then
        t1 :: (merge ts'1 ts2)
      else
        if fst t2 < fst t1 is true then
          t2 :: (merge ts1 ts'2)
        else insTree (link (snd t1) (snd t2)) (merge ts'1 ts'2)
    end.
    Next Obligation. 
      simpl.
      rewrite <- addnA.
      apply: (Nat.lt_add_pos_l _ _ (pos_rk t0)).
    Qed.
    Next Obligation.
      simpl.
      replace (rk t0 + size ts'1 + (rk t + size ts'2)) with
               (rk t0 + size ts'1 + size ts'2 + rk t).
      - apply: (Nat.lt_add_pos_r _ _ (pos_rk t)).
        replace (rk t + size ts'2) with (size ts'2 + rk t).
        - rewrite addnA; by [].
          by rewrite addnC.
    Qed.
    Next Obligation.
      simpl.
      replace (rk t0 + size ts'1 + (rk t + size ts'2)) with
               ((size ts'1 + size ts'2) + (rk t0 + rk t)).
      - apply Nat.lt_add_pos_r. 
        apply Nat.add_pos_pos; apply pos_rk.
        replace (rk t0 + size ts'1) with (size ts'1 + rk t0).
        rewrite <- addnA. rewrite <- addnA.
        apply Nat.add_cancel_l.
        rewrite addnC. rewrite <- addnA.
        by apply Nat.add_cancel_l.
        by rewrite addnC.
    Qed.

    Fixpoint removeMinTree (ts : Heap) : option (Tree * Heap) :=
      match ts with
      | []      => None
      | [t]     => Some (snd t, [])
      | t :: ts =>  if removeMinTree ts is Some (t', ts') then
                      if leq (root (snd t)) (root t') then
                        Some ((snd t), ts) 
                      else Some (t', t :: ts)
                    else None
      end.

    Definition findMin (ts : Heap) : option Elem :=
      if (removeMinTree ts) is Some (t, _) then Some (root t) else None.
    
    Fixpoint lTrevH (ts : list Tree) (r : nat) : Heap :=
      match ts with
      | [] => []
      | t :: ts' => (lTrevH ts' r.-1) ++ [(r, t)]
      end.

    Definition deleteMin (ts : Heap) : Heap :=
      if (removeMinTree ts) is Some (Node x ts1, ts2) then
        if head ts1 is Some hts1 then
          (merge (lTrevH ts1 (rk hts1)) ts2)
        else ts2
      else [].

    Definition isEmpty (ts : Heap) :=
      if ts is [] then true else false.


  End BinomHeap_rk.

  Arguments Heap      {_}.
  Arguments insert    {_}.
  Arguments merge     {_}.
  Arguments isEmpty   {_}.
  Arguments findMin   {_}.
  Arguments deleteMin {_}.
  Arguments empty     {_}.
  
  
  Definition BinomHeaprkClass (Elem : ordType) : HEAP.class Heap :=
    HEAP.Class Elem empty isEmpty insert merge findMin deleteMin.
  Canonical BinomHeaprk (Elem : ordType) : HEAP.type :=
    HEAP.Pack (BinomHeaprkClass Elem).  
End BINOMHEAP_RK.

Export HEAP.

Section ExplicitMin.
  Variables (H : type).

  Definition Elem := (Elem H).

  Inductive Heap := 
  | E
  | NE : Elem -> H -> Heap.
  Print Heap.

  Print insert.

  Definition Insert (x : Elem) (h : Heap) :=
    if h is NE y ts then
      if lt x y
        then NE x (insert H x ts)
      else NE y (insert H x ts)
    else NE x (insert H x (empty H)).

  Definition Merge (h1 h2 : Heap) : Heap :=
    match h1, h2 with
    | E, h2 => h2
    | h1, E => h1
    | NE x h'1, NE y h'2 =>
      if lt x y then
        NE x (merge H h'1 h'2)
      else NE y (merge H h'1 h'2)
    end.

  Definition DeleteMin (h1 : Heap) : Heap :=
    if h1 is NE x h then
       let h' := deleteMin H h in
       if findMin H h' is Some y then
         NE y h'
       else E
     else E.

  Definition FindMin (h : Heap) : option Elem :=
    if h is NE x h' then Some x else None.
  
End ExplicitMin.


Section fromList.
Variables (Heap : type).

Arguments insert    {_}.
Arguments merge     {_}.
Arguments isEmpty   {_}.
Arguments findMin   {_}.
Arguments deleteMin {_}.
Arguments empty     {_}.

Notation Elem := (Element (class_of Heap)).

Fixpoint StackT_to_StackHeap (st : list Elem) : list Heap :=
      if st is h :: t then
        cons (insert h empty) (StackT_to_StackHeap t)
      else [].

    Fixpoint merge_list_one_time (st : list Heap) : list Heap :=
    if st is h1 :: (h2 :: t) then
      cons (merge h1 h2) (merge_list_one_time t)
    else st.    


    Definition list_ind2 := 
    fun (A : Type) (P : list A -> Prop) (f : P []) (f' : forall x, P [x])
      (f0 : forall (a b : A) (l : list A), P l -> P (a :: b :: l)) =>
    fix F (l : list A) : P l :=
      match l as l0 return (P l0) with
      | [] => f
      | [x] => f' x
      | x :: y :: l0 => f0 x y l0 (F l0)
      end.      

    Program Fixpoint merge_list (st : list Heap) {measure (length st)} : Heap :=
    match st with
    | [h] => h
    | []  => empty
    | st'   => merge_list (merge_list_one_time st')
    end.
    Next Obligation.
      move: H0 H. 
      apply (@list_ind2
              Heap
              (fun st : list Heap => 
              (forall h : Heap, [h] <> st) ->
              [] <> st ->
              (length (merge_list_one_time st) < length st)%coq_nat)).
      - move=> _ fal; by [].
      - move=> x H. move: (H x); by [].
        move=> a b l H H1 H0.
        move: H. case l.
        - move=> h. by [].
          move=> h l0.
          case l0.
          - move=> HH. by [].
            move=> h0 l1 HH.
            simpl in *.
            assert ((length (merge_list_one_time l1)).+1 < (length l1).+2)%coq_nat.
            apply HH; by []. by lia.
    Defined.
    Next Obligation.
      by [].
    Qed.
  Definition fromList (l : list Elem) : Heap := merge_list (StackT_to_StackHeap l).
End fromList.