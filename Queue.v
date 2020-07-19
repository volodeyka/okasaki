From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path order eqtype. 
From okasaki Require Import ssrlia.
Require Import Psatz.
Import Order.TTheory.
Notation ordType := (orderType tt).
Import Order.NatOrder.

Open Scope order_scope.

Lemma dev2le a : (a./2 <= a)%N.
Proof.
by rewrite -{2}[a](half_bit_double _ false) half_leq// add0n -addnn leq_addr.
Qed.

(* The most common implementation of queues in a purely functional setting is
   as a pair of lists, f and r, where f contains the front elements of the
   queue in the correct order and r contains the rear elements of the queue 
   in reverse order. For example, a queue containing the integers 1... 6 might
   be represented by the lists f = [1,2,3] and r - [6,5,4].                    *)
Module queue.
Section specifications.
Variable T : Type.

Definition queue := ((seq T) * (seq T))%type.
Notation emp := ([::], [::]).


Implicit Type q : queue.

(* Elements are added to r and removed from f, so they must somehow migrate
   from one list to the other. This migration is accomplished by reversing r
   and installing the result as the new f whenever f would otherwise become 
   empty, simultaneously setting the new r to [::]. The goal is to maintain 
   the invariant that f is empty only if r is also empty (i.e., the entire 
   queue is empty). Note that, if f were empty when r was not, then the first 
   element of the queue would be the last element of r, which would take O(n) 
   time to access. By maintaining this invariant, we guarantee that head can 
   always find the first element in O(1) time.                               *)
Definition batched q : bool := 
match q with
    | ([::], _ :: _) => false
    | _              => true
end.

Definition head q : option T := if q is (x :: _, _) then Some x else None.

Lemma head_emp q : batched q -> (head q = None <-> q = emp).
Proof. by case: q=> [[[]|]]. Qed.

Definition checkf q := 
match q with
    | ([::], r) => (rev r, [::])
    | _         => q
end.

Definition tail q := 
match q with
    | ([::], _)   => emp
    | (x :: f, r) => checkf (f, r)
end.

Lemma batched_checkf q: batched (checkf q).
Proof. case: q=> [[]] //= l. by case (rev l). Qed.


Lemma batched_tail q : batched (tail q).
Proof. case: q=> [[]]//*. by rewrite /tail batched_checkf. Qed.

Definition snoc q x := match q with (f, r) => checkf (f, x :: r) end.

Lemma batched_snoc x q: batched (snoc q x).
Proof. case: q. rewrite /snoc =>*. by apply: batched_checkf. Qed.


End specifications.
End queue.

(* This design can easily be extended to support the double-ended queue, or
   deque, abstraction, which allows reads and writes to both ends of the queue
   (see Figure 5.3). The invariant is updated to be symmetric in its treatment
  of f and r: both are required to be non-empty whenever the deque contains two
  or more elements. When one list becomes empty, we split the other list in
  half and reverse one of the halves.                                          *)
Module double_ended_queue.
Section specification.
Variable T : eqType.

Definition dqueue := ((seq T) * (seq T))%type.
Notation emp := ([::], [::]).


Implicit Type dq : dqueue.

Definition batched dq : bool := 
match dq with
    | ([:: _, _ & _], [::]) => false
    | ([::], [:: _, _ & _]) => false
    | _                    => true
end.


Definition checkf dq := 
match dq with (f, r) =>
    match (f, r) with
    | ([:: _], _) => dq
    | (_, [:: _]) => dq
    | (_ :: _, [::]) => let l := (size f)./2 in
      (take l f, rev (drop l f))
    | ([::], _ :: _) => let l := (size r)./2 in
      (rev (drop l r), take l r)
    | _              => dq
    end
end.

Definition size dq := size (dq.1) + size (dq.2).

Definition batched' dq := 
  ((size dq) > 1)%N -> ((dq.1) != [::]) && (dq.2 != [::]).

Lemma batchedE dq: reflect (batched' dq) (batched dq).
Proof.
apply: (iffP idP); case dq=> [[[]//?[]//??|?[[]//??|??[|??]//]]]/=;
rewrite /batched'/=/size/=; apply; by ssrnatlia.
Qed.

Lemma batched_checkf dq : batched (checkf dq).
Proof.
apply/batchedE. case: dq=> [[[]//?[]//??|?[[]|??[|?[]]]]]//;
rewrite /checkf/batched'/size/fst/snd -?size_eq0 ?size_rev ?size_takel;
by rewrite ?size_drop ?subSS ?subn_eq0 -?leqNgt ?dev2le.
Qed.

Theorem checkfE dq: reflect (checkf dq = dq) (batched dq).
Proof.
apply: (iffP idP)=> [|<-]; last by apply: batched_checkf.
by case: dq=> [[[]//?[]//|?[]//??[]//?[]]].
Qed.

Definition tail dq := if dq is (x :: f, r) then checkf (f, r) else emp.

Lemma batched_tail dq : batched (tail dq).
Proof. case: dq=> [[]]//*. by rewrite batched_checkf. Qed.

Definition head x0 dq : T := 
match dq with
    | (x :: f, _)    => x
    | ([::], [:: x]) => x
    | _              => x0
end.

Definition cons x dq := match dq with (f, r) => checkf (x :: f, r) end.

Lemma batched_cons dq x: batched (cons x dq).
Proof. by case: dq=> *; rewrite /cons batched_checkf. Qed.

Definition seq_of : dqueue -> seq T := fun '(f, r) => f ++ (rev r).
Arguments seq_of : simpl never.

Lemma size_eq0 dq: batched dq -> (dq == emp) = (seq_of dq == [::]).
Proof. by case: dq=> [[[]//|]?[]]. Qed.

Lemma seq_of_checkf dq: seq_of (checkf dq) = seq_of dq.
Proof.
case: dq=> [[[]//?[]//*|?[]//??[|?[]//]]];
by rewrite /checkf/seq_of (cat0s, cats0) -?rev_cat ?revK cat_take_drop. 
Qed.

Lemma seq_of_cons x dq: batched dq -> seq_of (cons x dq) = x :: (seq_of dq).
Proof. case: dq=> [[|?[[]//?[]//|??]][]]//*; by rewrite /cons seq_of_checkf. Qed.

Lemma seq_of_tail dq: batched dq -> seq_of (tail dq) = behead (seq_of dq).
Proof.
case: dq=> [[[]|?[[]|?]]//?[]]//*; by rewrite /tail seq_of_checkf /seq_of.
Qed.

Lemma head_seq_of x0 dq: batched dq -> head x0 dq = seq.head x0 (seq_of dq).
Proof. by case: dq=> [[[]//|]?[]]. Qed.

Lemma tail_cons x dq (batch_dq : batched dq) :
  seq_of (tail (cons x dq)) = seq_of dq.
Proof. by rewrite seq_of_tail ?batched_cons ?seq_of_cons//= drop0. Qed.

Lemma cons_head_tail dq x0 (batch_dq : batched dq) (n_emp : dq != emp): 
  seq_of (cons (head x0 dq) (tail dq)) = seq_of dq.
Proof.
rewrite seq_of_cons ?batched_tail ?seq_of_tail ?head_seq_of -?nth0 -?drop1
 -?drop_nth ?drop0//.
by rewrite lt0n seq.size_eq0 -size_eq0.
Qed.

Definition rev : dqueue -> dqueue := fun '(f, r) => (r, f).

Lemma revK: involutive rev.
Proof. by case. Qed.

Lemma seq_of_rev dq: seq_of (rev dq) = seq.rev (seq_of dq).
Proof. case: dq=> *. by rewrite /rev/seq_of rev_cat seq.revK. Qed.


Lemma checkf_rev dq: checkf (rev dq) = rev (checkf dq).
Proof. case dq=> [[|?[|??]][]//?[]//]. Qed.

Lemma batched_rev dq: batched (rev dq) = batched dq.
Proof.
apply: sameP; last by apply: checkfE. apply: equivP; first by apply: checkfE.
rewrite (checkf_rev dq). split=> [/(congr1 rev)|->//]. by rewrite !revK.
Qed.

Definition init dq := if dq is (f, _ :: r) then checkf (f, r) else emp.

Lemma initE dq: init dq = rev (tail (rev dq)).
Proof. case: dq=> [?[]//*]. by rewrite {2}/rev/init/tail -checkf_rev. Qed.

Lemma batched_init dq : batched (init dq).
Proof. by rewrite initE batched_rev batched_tail. Qed.

Definition last x0 dq : T := 
match dq with
    | (_, x :: f)    => x
    | ([:: x], [::]) => x
    | _              => x0
end.

Lemma lastE dq x0: last x0 dq = head x0 (rev dq).
Proof. by case: dq=> [[]//?[]]. Qed.

Definition rcons dq x := match dq with (f, r) => checkf (f, x :: r) end.

Lemma rconsE dq x: rcons dq x = rev (cons x (rev dq)).
Proof. case: dq=>*. by rewrite {2}/rev/rcons/cons -checkf_rev. Qed.

Lemma batched_rcons dq x: batched (rcons dq x).
Proof. by rewrite rconsE batched_rev batched_cons. Qed.

Lemma seq_of_rcons x dq: 
  batched dq -> seq_of (rcons dq x) = seq.rcons (seq_of dq) x.
Proof.
case: dq=>*. 
by rewrite rconsE seq_of_rev seq_of_cons ?batched_rev// seq_of_rev rev_cons seq.revK.
Qed.

Lemma seq_of_init dq (b: batched dq): 
  seq_of (init dq) = seq.rev (behead (seq.rev (seq_of dq))).
Proof.
by rewrite initE seq_of_rev seq_of_tail ?seq_of_rev ?batched_rev.
Qed.

Lemma last_seq_of x0 dq (b : batched dq): last x0 dq = seq.last x0 (seq_of dq).
Proof. 
rewrite lastE head_seq_of ?seq_of_rev ?batched_rev// -nth0 -nth_last.
case: (seq_of dq)=> //*. by rewrite nth_rev ?subn1.
Qed.

Lemma init_cons x dq (batch_dq : batched dq) :
  seq_of (init (rcons dq x)) = seq_of dq.
Proof.
by rewrite initE rconsE revK seq_of_rev tail_cons ?batched_rev// -seq_of_rev revK.
Qed.

Lemma rcons_last_init dq x0 (batch_dq : batched dq) (n_emp : dq != emp): 
  seq_of (rcons (init dq) (last x0 dq)) = seq_of dq.
Proof.
rewrite rconsE initE revK lastE seq_of_rev cons_head_tail -?seq_of_rev ?revK//;
rewrite ?batched_rev//. by case: dq n_emp {batch_dq}=> []/=[[]|]//??[].
Qed.

End specification.
End double_ended_queue.

