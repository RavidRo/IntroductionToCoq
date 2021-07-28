From Coq Require Import Arith Bool Classical_Prop.

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
Abort.


Lemma lemma2 : x=2 -> x=2.
Proof.
Abort.

(* Notice that he lemma is added to the enviorement only after you prove it *)
Lemma badLemma : 1 = 2.
Proof.
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
Abort.

Lemma lemma4 : ~False.
Proof.
Abort.

Lemma lemma5 : (getTwoAM Four) = Time Two AM.
Proof.
Abort.

Lemma lemma6 : forall h: hour, getTwoAM h = Time Two AM.
Proof.
Abort.

Lemma lemma7 : exists t: time, getTwoAM Four = t.
Proof.
Abort.

Lemma lemma8 : forall t1: time, exists t2: time, switchHalf t1 = t2.
Proof.
Abort.

Lemma lemma9 : forall t1 t2 t3: time, t1=t2 -> t1=t2 \/ t1=t3.
Proof.
Abort.

Lemma lemma10 : forall t1 t2 t3 : time, t1 = t2 /\ t2 = t3 -> t1 = t2.
Proof.
Abort.

(* Understanding the multiple '->' syntax *)
Lemma lemma11 : forall t1 t2 t3 : time, t1=t2 -> t2=t3 -> t1 = t2 /\ t2 = t3.
Proof.
Abort.

Lemma lemma12 : forall t1 t2 t3 : time, t1=t3 \/ t1=t2 -> t1=t2 \/ t1=t3.
Proof.
Abort.

Lemma lemma13 : forall t : time, eqTime t t = true.
Proof.
Abort.

Lemma lemma14 : forall t1 t2 : time, t1=t2 -> eqTime t1 t2 = true.
Proof.
Abort.


Lemma lemma15 : forall t1 t2 t3: time, t1=t2 -> t2=t3 -> t1 = t3.
Proof.
Abort.

Lemma lemma16 : (Four <> Two).
Proof.
Abort.

Lemma lemma17 : (Four = Two) -> False.
Proof.
Abort.

(* A harder one *)
Lemma lemma18 : forall h1 h2 : hour, eqHour h1 h2 = true -> h1 = h2.
Proof.
Abort.


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
Abort.


Lemma lemma20 : even 4.
Proof.
Abort.


(*
  Now let's prove a difficult theorem.
  We will prove that isEven returns true if and only if the number is of the even type.
  
  To prove that we will need to prove some additional lemmas.
*)

Lemma not_not: forall p: Prop, ~~p <-> p.
Proof.
Abort.

Lemma not_iff: forall p1 p2: Prop, (p1 <-> p2) -> (~p1 <-> ~p2).
Proof.
Abort.

(* Introducing inversion *)
Lemma inversion : forall x y: nat, S x = S y -> x = y.
Proof.
Abort.

(* The predicates only dfines on of the directions. It is up to us to prove the other one.*)
Lemma odd_iff_next_even : forall n, even (S n) <-> odd n.
Proof.
Abort.

Lemma even_iff_next_odd : forall n, odd (S n) <-> even n.
Proof.
Abort.

(* 
Now for the 2 important lemmas:
- The connection between even and odd.
- The connection between isEven and isOdd.
*)
Lemma even_iff_not_odd : forall x: nat, even x <-> ~odd x.
Proof.
Abort.

Lemma isEven_iff_not_isOdd : forall x: nat, isEven x = true <-> isOdd x = false.
Proof.
Abort.

Theorem complete_even : forall x : nat, isEven x = true <-> even x.
Proof.
Abort.

(*
During the demo I kept the automatic tactics hidden. They will try a bunch of different tactics to prove the goal for you.
Some of them are 'auto' and 'intuition'. Using this tactis could have made the proofs shorter and easier.

For more information about coq:
- List of book and tutorials - https://coq.inria.fr/documentation
- The documentation - https://coq.inria.fr/distrib/current/refman/
- The standard library - https://coq.inria.fr/distrib/current/stdlib/
*)
