From Coq Require Import Arith Bool.

(* Coq is a functional strongly typed programming language *)

(*
  Basic rules:
    - All commands start with a capital letters
    - Every line must end with a '.'.
*)

(* Check returns the type of the given expression *)
Check 1.
Check 28 + 5.
Check true.
Check (false && true).
Check (5, true).

(* Coq will throw an error if the given expression has different type then the expcted one *)
Fail Check 5 && 6.

(* Note that this is of type prop(Proposition). If we think that the proposition is indeed true than we need to prove it. *)
Check 10 = 27.

Compute 20 * 2.
Compute (false || true).

(* With Definition you can declare global variables *)
Definition x := 5.
Check x.
Compute x.

(* Let allows you to create local varibles *)
Compute let y := x in y+25.
Fail Check y.
Compute 
  let num1 := 5 in
    let num2:= 10 in
      num1 + num2.
      
(* Note that if is an expression and you can compute it's value *)
Compute if true then x else 100.


(* This is how you declare inductive types *)
Inductive hour :=
    One : hour
  | Two : hour
  | Three : hour
  | Four : hour
  | Five : hour
  | Six : hour
  | Seven : hour
  | Eight : hour
  | Nine : hour
  | Ten : hour
  | Eleven : hour
  | Twelve : hour.
 
Inductive day_half :=
    AM: day_half
  | PM: day_half.


Inductive time := Time : hour -> day_half -> time.

(* This is how you define and use functions *)
(* "lambda" = fun *)
Definition next1 := fun x => x + 1.
Definition next2 x := x + 1.

Check next1.
Compute next1 5.

Definition getTwoAM (h : hour) := Time Two AM.
Compute getTwoAM Five.

Definition getTimeAM (h: hour) := Time h AM.

Definition switchHalf (t: time) := 
  match t with
    Time h AM => Time h PM
  | Time h PM => Time h AM
  end.


Compute switchHalf (getTimeAM Four).

Definition eqHour (h1 h2: hour) :bool :=
  match (h1, h2) with
    (One, One) => true
  | (Two, Two) => true
  | (Three, Three) => true
  | (Four, Four) => true
  | (Five, Five) => true
  | (Six, Six) => true
  | (Seven, Seven) => true
  | (Eight, Eight) => true
  | (Nine, Nine) => true
  | (Ten, Ten) => true
  | (Eleven, Eleven) => true
  | (Twelve, Twelve) => true
  | _ => false
  end.
    
Definition eqHalf (h1 h2: day_half) : bool :=
  match (h1, h2) with
    (AM, AM) => true
  | (PM, PM) => true
  | _ => false
  end.
  
Definition eqTime (time1 time2:time) : bool :=
  match (time1, time2) with
    (Time h1 half1, Time h2 half2) => (eqHour h1 h2) && (eqHalf half1 half2)
  end.
  
Compute eqTime (Time Three PM) (Time Three PM).


(* Propositions syntax:*)

Check 1 = 1.
(* forall *)
Check forall x: nat, x = 2.
(* exists *)
Check exists x: nat, x = 2.
(* \/ - OR *)
Check True \/ False.
(* /\ - AND*)
Check True /\ False.
(* x -> y - Provable if, when *assuming* x is provable, then so is y. *)
Check x = 2 -> x = 3.
(* ~x - provable if x is NOT provable*)
Check x = 2 -> ~(x = 3).
(* <> *)
Check 2 <> 4.

(* 
  Notice the difference between False and flase / True and true
  With capital letter - Provable/Not provable
  No capital letter - bool defenition we imported from the bool library
  
  That is also the difference between && and /\, || and \/
*)


(* 
  Proof mode:
  1. First you need to write a proposition and declare with it a Lemma or a Theorem you want to prove.
  2. Use the Proof command to enter Proof Mode.
  3. In proof mode you have Assumptions and Goals.
  4. With tactic you can manipulate your assumption and goals to get to a state where you have no goals left.
  5. When you have no goals left you can use the Qed command to announce you finished.
*)

Lemma lemma1 : 1 = 1.
Proof.
(* You can see your goals at the right *)
reflexivity.
Qed.


Lemma lemma2 : x=2 -> x=2.
Proof.
(* You can see you context (variables and hypotheses) at the top right *)
intros H.
apply H.
Qed.

(* Notice that he lemma is added to the enviorement only after you prove it *)
Lemma badLemma : 1 = 2.
Abort.

Fail Check badLema.
Check lemma1.

(* 
       |               |      in goal     |   in hypotheses    |
       |---------------+-------------------------------------- |
       | A -> B        |      intros      |      apply         |
       | A /\ B        |      split       |     destruct       |
       | A \/ B        |    left/right    |     destruct       |
       | ~A            |      intro       |      apply         |
       |  True         |     trivial      |       N/A          |
       |  False        |       N/A        |   contradiction    |
       | forall x, P x |      intros      |      apply         |
       | exists x, P x |     exists t     |     destruct       |
       | t = u         | reflexivity/ring |rewrite/discriminate|
       | t <> u        |   discriminate   |   contradiction    |
       
  Good cheat sheet for basic tactics :
  https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html
*)

Lemma lemma3 : True.
Proof.
(* Introducing trivial *)
trivial.
Qed.

Lemma lemma4 : ~False.
Proof.
intro.
(* Introducing contradiction *)
contradiction.
Qed.

Lemma lemma5 : (getTwoAM Four) = Time Two AM.
Proof.
(* Introducing compute *)
compute.
reflexivity.
Qed.

Lemma lemma6 : forall h: hour, getTwoAM h = Time Two AM.
Proof.
(* Introducing intros *)
intros.
compute.
reflexivity.
Qed.

Lemma lemma7 : exists t: time, getTwoAM Four = t.
Proof.
(* Introducing exists *)
exists (Time Two AM).
compute.
reflexivity.
Qed.

Lemma lemma8 : forall t1: time, exists t2: time, switchHalf t1 = t2.
Proof.
intros.
(* You can use your proof's context *)
exists (switchHalf t1).
reflexivity.
Qed.

Lemma lemma9 : forall t1 t2 t3: time, t1=t2 -> t1=t2 \/ t1=t3.
Proof.
intros.
(* You cant imiddietly use apply H :( *)
Fail apply H.
left.
apply H.
Qed.

Lemma lemma10 : forall t1 t2 t3 : time, t1 = t2 /\ t2 = t3 -> t1 = t2.
Proof.
intros.
(* Intoducing destruct *)
destruct H as [H1 H2].
apply H1.
Qed.

Lemma lemma11 : forall t1 t2 t3 : time, t1=t2 -> t2=t3 -> t1 = t2 /\ t2 = t3.
Proof.
intros.
(* Intoducing split and '-' syntax *)
split.
- apply H.
- apply H0.
Qed.

Lemma lemma12 : forall t1 t2 t3 : time, t1=t3 \/ t1=t2 -> t1=t2 \/ t1=t3.
Proof.
intros.
Fail apply H.
(* 
  You cant: 
  left/right...
  
  Introducing destruct on an \/ in hypothesis
*)
destruct H.
- right; apply H.
- left; apply H.
Qed.

Lemma lemma13 : forall t : time, eqTime t t = true.
Proof.
intros.
case t.
intros.
(* Introducing case and ';' syntax *)
case h; case d; compute; reflexivity.
(*
  Better than:
  case h.
  case d.
  - compute; reflexivity.
  - compute; reflexivity.
  - compute; reflexivity.
  ...
*)
Qed.

Lemma lemma14 : forall t1 t2 : time, t1=t2 -> eqTime t1 t2 = true.
Proof.
intros.
(* Introducing rewrite and apply *)
rewrite H.
apply lemma13.
Qed.


(* Understanding the multiple '->' syntax *)
Lemma lemma15 : forall t1 t2 t3: time, t1=t2 -> t2=t3 -> t1 = t3.
Proof.
intros.
rewrite H.
apply H0.
Qed.


(* A harder one *)
Lemma lemma16 : forall h1 h2 : hour, eqHour h1 h2 = true -> h1 = h2.
Proof.
(* 
  You can't do this, you get a flase assumption and its hard to see it:
  
  intros.
  case t1; case t2.
  intros.
  case h; case d; case h0; case d0.
  - reflexivity.
  - ???. 
*)

intros h1 h2.
case h1; case h2.

(* Introducing discriminate *)
(* 
  You cansolve it like this:
  - compute; intro; reflexivity.
  - compute; intro; discriminate.
  ...
  
  Or this:
  - compute; intro; (reflexivity || discriminate).
  - compute; intro; (reflexivity || discriminate).
  ...
*)

(* Introducing all and the '||' syntax *)
all: compute; intro; (reflexivity || discriminate). 
Qed.


Lemma lemma17 : (Four <> Two).
Proof.
discriminate.
Qed.

Lemma lemma18 : (Four = Two) -> False.
Proof.
intro.
discriminate.
Qed.


(* 
  Firstly lets see how the natural numbers are defiend:

  Basic natural is 0
  From there x + 1 = S x
  => 3 = S (S (S 0))
*)
Print nat.
(* Introduing Fixpoint *)
(* We must use the Fixepoin keyword instead of definition when we want to declare a recursive function *)
Fixpoint isEven (n : nat) : bool := 
  match n with
    0 => true
  | S n' => isOdd n'
  end
with isOdd (n : nat) : bool := 
  match n with
    0 => false
  | S n' => isEven n'
  end.
 
  
Compute isEven 4.
Compute isEven 17.

(* Lets look at inductive predicates *)
Inductive even : nat -> Prop :=
  | even0 : even 0
  | evenS : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    oddS : forall n, even n -> odd (S n).

Lemma lemma19 : isEven 4 = true.
Proof.
compute.
reflexivity.
Qed.


Lemma lemma20 : even 4.
Proof.
apply evenS.
apply oddS.
apply evenS.
apply oddS.
apply even0.
Qed. 


Theorem completeEven1 : forall x : nat, isEven x = true -> even x.
Proof.
intro x.
(* Introducing induction *)
induction x.
- intro.
  apply even0.
Abort.

Theorem completeEven2 : forall x : nat, even x -> isEven x = true.
Proof.
intros x.
induction x.
- compute.
  reflexivity.
Abort.


(*
During the demo I kept the automatic tactics hidden. They will try a bunch of different tactics to prove the goal for you.
Some of them are 'auto' and 'intuition'. Using this tactis could have made the proofs shorter and easier.

For more information about coq:
- List of book and tutorials - https://coq.inria.fr/documentation
- The documentation - https://coq.inria.fr/distrib/current/refman/
*)
