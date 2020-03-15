From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import Lia.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Set Implicit Arguments.
(** TODO: split in record and structure *)
Module STACK.
  Structure Stack (T : Type) := Class
  {
    (* original from Okasaki *)
    stack :  Type;
    empty : stack;
    isEmpty : stack -> bool;

    cons : T -> stack -> stack;
    head : stack -> option T;
    tail : stack -> stack;

    (* for proofs *)
    length : stack -> nat;
    spec_isEmpty : forall st, (isEmpty st = true) <-> length st = 0;
    spec_len (st : stack): length (tail st) = (length st).-1
  }.
  (**TODO: may be it possible to make less "Arguments ..."*)
  Arguments isEmpty [T _] _.
  Arguments spec_isEmpty [T _] _.
  Arguments head [T _].
  Arguments cons [T _].
  Arguments tail [T _].
  Arguments length [T _].
  Arguments empty [T _].
  
  Variables T : Type.
  Variables e : Stack T.
  
  (** TODO: ssreflect proof *)
  Program Fixpoint append {T : Type} {e : Stack T} (st1 st2 : stack e)
  {measure (length st1)} : stack e :=
    if (isEmpty st1) is true then st2 else 
    if head st1 is Some x then cons x (append (tail st1) st2)
    else st1.
  Next Obligation.
  Proof.
    - rewrite spec_len.
      assert (length st1 <> 0).
      move=> se; apply: H. symmetry.
      by apply spec_isEmpty.
    by lia.
  Qed.

  Notation "st1 ++ st2" := (append st1 st2) (at level 60, right associativity).
  
  (* Returns empty if cannot update *)
  Fixpoint update {T : Type} {e : Stack T} (st : stack e) (i : nat) (x : T)
    {struct i} : stack e :=
    if isEmpty st is true then empty else
    if i is i'.+1 then 
    update (tail st) i' x else
    cons x (tail st).
  
End STACK.
(** TODO: instanses *)
