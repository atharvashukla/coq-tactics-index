
(* =================
   Coq Tactics Index
   =================
   
   https://pjreddie.com/coq-tactics/
   
   Stage 1: Proving Easy Goals
   ---------------------------
   - reflexivity
   - assumption
   - discriminate
   - constructor
   
   Stage 2: Transforming Your Goal
   -------------------------------
   - apply
   - subst
   - rewrite
   - simpl
   - cut
   - unfold
   
   Stage 3: Breaking Apart Your Goal
   ---------------------------------
   - destruct
   - inversion
   - induction
   
   Stage 4: Powerful Automatic Tactics
   -----------------------------------
   - auto
   - intuition
   - omega *)


(* ----------- *)
(* reflexivity *)
(* ----------- *)

(* Use reflexivity when your goal is to prove that something equals itself. *)

(* In this example we will prove that any term x of type Set is equal to itself. 
   After we intro the variable we can prove the goal using reflexivity. *)

Lemma everything_is_itself:
  forall x: Set, x = x.
Proof.
  intro.
  reflexivity.
Qed.

(* Use it when: your goal is something like a = a. *)

(* Advanced usage: reflexivity will work even if your goal is not syntactically
   identical on the left and right side of the equality. Both sides just have to
   evaluate to the same term. *)

(* In this example we will apply reflexivity to a more complicated math 
   equation: (3 + (0 + 2)) = (1 + 4). *)

Inductive nat : Set :=
  | O
  | S : nat -> nat.

Fixpoint add (a: nat) (b: nat) : nat :=
  match a with
    | O => b
    | S x => S (add x b)
  end.

Lemma complex_math:
    (add (S (S (S O))) 
        (add O (S (S O)))) =
    add (S O) (S (S (S (S O)))).
Proof.
    reflexivity.
Qed.

(* ---------- *)
(* assumption *)
(* ---------- *)

(* If the thing you are trying to prove is already in your context, use assumption
   to finish the proof. *)

(* In this example we show that if we assume p we can prove p. We use assumption to
   tell Coq that our goal is already true in our context because we assumed it! *)


Lemma everything_implies_itself:
  forall p: Prop, p -> p.
Proof.
  intros.
  assumption.
Qed.

(* Use it when: your goal is already in your context of terms you already know. *)


(* ------------ *)
(* discriminate *)
(* ------------ *)

(* If you have an equality in your context that isn't true, you can prove anything
   using discriminate. *)


(* For discriminate to work, the terms must be structurally different. This means 
   that both terms are elements of an inductive set but they are built differently,
   using different constructors (e.g. true and false, or (S O) and (S (S O))). *)


(* In this example we show that if we assume true = false then we can prove
   anything. Note that we don't specify what a is, it really can be anything! *)
(* *)
(* *)


(* *)
(* *)
(* *)
(* *)


(* *)
(* *)
(* *)
(* *)


(* *)
(* *)
(* *)
(* *)


(* *)
(* *)
(* *)
(* *)
