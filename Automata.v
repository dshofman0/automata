(** * DFA and NFA *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Sorting.Sorted.
Require Import List ListSet. Import ListNotations.



Module FunctionImplementation.

(* ----------------------------------------------------------------- *)  
(** *** ListSet Util *)
  
(** This is a helper function used later to define evaluation
    functions for the automata. *)  

Fixpoint set_unions {A} A_dec (ss : list (set A)) :=
  match ss with
  | [] => empty_set A
  | s::ss' => set_union A_dec s (set_unions A_dec ss')
  end.



(* ################################################################# *)
(** * Formalization of DFAs *)

(** We define DFAs on arbitrary sets for states and actions. A DFA is
    defined in terms of its transition function, start state, and
    accept states. [eval_DFA] takes a start state, transition function,
    and input and computes the resulting state after processing the
    input. [accept_DFA] uses [eval_DFA] on an input and checks whether
    the output is an accept state. *)

Definition Transition {Q A : Type} : Type := Q -> A -> Q.
Definition Accept {Q : Type} : Type := Q -> bool.

Fixpoint eval_DFA {Q A} (tf : Transition) (q : Q) (str : list A) : Q :=
  match str with
  |[] => q
  |h::t => eval_DFA tf (tf q h) t
  end.

Definition accept_DFA {Q A : Type} (start : Q) (tf : Transition) (accept : Accept) (str : list A)
  : bool :=
  accept (eval_DFA tf start str).

(* ----------------------------------------------------------------- *)  
(** *** DFA Example *)

(** Here we instantiate an example DFA by definining its state and 
    action types. Then we define its transition function, accept states
    and start state. This DFA has two states

    This simple example of a DFA has two states: a start state and an
    accept state. Its alphabet is {0, 1}. The start state will only 
    move to the accept state on an input of 1. Otherwise it stays at
    the start state. Once it moves to the accept state, every input
    keeps it there.

    After defining the DFA, we compute its result on a few example
    inputs, and then we prove a theorem that characterizes the
    language it accepts. This DFA only accepts strings that contain
    a 1. *)

Inductive example_Q_DFA : Type :=
| Q_reject
| Q_accept
.

Theorem example_Q_DFA_dec : forall x y : example_Q_DFA, {x = y} + {x <> y}.
Proof. intros x y. destruct x; destruct y;
       try (left; reflexivity); try (right; intro H; discriminate).
Defined.

Inductive binary_A : Type :=
| a0
| a1
.

Definition example_TF (q : example_Q_DFA) (a : binary_A) :=
  match q with
  | Q_reject => match a with
              | a0 => Q_reject
              | a1 => Q_accept
              end
  | Q_accept => match a with
              | a0 => Q_accept
              | a1 => Q_accept
              end
  end.

Definition example_Accept (q : example_Q_DFA) :=
  match q with
  | Q_reject => false
  | Q_accept => true
  end.

Definition example_DFA := accept_DFA Q_reject example_TF example_Accept.

Example example_DFA1 : example_DFA [] = false.
Proof. reflexivity. Qed.

Example example_DFA2 : example_DFA [a0;a0;a0] = false.
Proof. reflexivity. Qed.

Example example_DFA3 : example_DFA [a0;a1] = true.
Proof. reflexivity. Qed.

Example example_DFA4 : example_DFA [a1;a1;a0;a1] = true.
Proof. reflexivity. Qed.

Theorem example_DFA_accept : forall input,
    example_DFA input = true <-> In a1 input.
Proof.
  intros. split; intro H.
  - induction input.
    + inversion H.
    + simpl. destruct a; auto.
  - induction input.
    + inversion H.
    + unfold example_DFA. unfold accept_DFA.
      destruct a; simpl.
      * destruct H. discriminate.
        apply IHinput. assumption.
      * clear H IHinput.
        induction input.
        -- reflexivity.
        -- destruct a; assumption.
Qed.

(* ################################################################# *)
(** * Formalization of NFAs *)

(** We now formalize NFAs and prove that they can be transformed into
    DFAs that accept the same language. We will formalize two versions
    of the NFA: one without epsilon transitions and one with epsilon
    transitions. *)

(* ----------------------------------------------------------------- *)  
(** *** Exists Accept Theorem *)

(** Here we prove a theorem about sets and [existsb], which will be used
    later in our transformation proofs. *)

Lemma Is_true_iff : forall x : bool,
    x = true <-> Is_true x.
Proof.
  split.
  apply Is_true_eq_left.
  apply Is_true_eq_true.
Qed.

Lemma negb_prop_iff : forall b : bool,
    Is_true (negb b) <-> ~ Is_true b.
Proof.
  split.
  apply negb_prop_elim.
  apply negb_prop_intro.
Qed.

Lemma Is_false_iff : forall x : bool,
    x = false <-> ~ x = true.
Proof.
  intros.
  rewrite <- negb_true_iff.
  rewrite Is_true_iff.
  rewrite negb_prop_iff.
  rewrite <- Is_true_iff.
  reflexivity.
Qed.

Theorem exists_accept_equal : forall (Q : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ql1 ql2 : set Q) (accept : Accept),
    (forall q, In q ql1 <-> In q ql2) -> existsb accept ql1 = existsb accept ql2.
Proof.
  intros. destruct (existsb accept ql2) eqn:Eql2.
  - rewrite existsb_exists. rewrite existsb_exists in Eql2.
    destruct Eql2. exists x.
    rewrite <- (H x) in H0. assumption.
  - rewrite Is_false_iff. rewrite Is_false_iff in Eql2.
    rewrite existsb_exists. rewrite existsb_exists in Eql2.
    intro contra. destruct contra. apply Eql2. exists x.
    rewrite (H x) in H0. assumption.
Qed.

Module NoEps.
  
(* ----------------------------------------------------------------- *)  
(** *** Formalization of NFAs with No Epsilon Transitions *)
  
(** We now formalize NFAs in a similar fashion to DFAs, using transition
    functions, start states, and accept states. Now however, the transition
    function outputs a set of states instead of a single state, and the 
    accept function checks that an accept state exists within the set of
    output states. *)

Definition NTransition {Q A : Type} : Type := Q -> A -> set Q.

Fixpoint eval_NFA {Q A} (ntf : NTransition)
         (Q_dec : forall (x y : Q), {x = y} + {x <> y})
         (q : set Q) (str : list A) : set Q :=
  match str with
  | [] => q
  | h::t =>
    set_unions Q_dec (map (fun q' => eval_NFA ntf Q_dec (ntf q' h) t)
                     q)
  end.

Definition accept_NFA {Q A : Type} (start : Q) (ntf : NTransition)
           (accept : Accept)
         (Q_dec : forall (x y : Q), {x = y} + {x <> y})           
         (str : list A)
  : bool :=
  existsb accept (eval_NFA ntf Q_dec [start] str).

(** We now formalize a transformation from NFAs to DFAs. The
    nondeterministic transition function, which maps states to sets 
    of states, is transformed into a determinsitc transition function
    that maps sets of states to sets of states. We also say that a
    set of states is accepted by the DFA if there is a state in the
    set that is accepted by the NFA. *)

Definition NTF_to_TF {Q A : Type} (ntf : @NTransition Q A)
           (Q_dec : forall (x y : Q), {x = y} + {x <> y})
  : @Transition (set Q) A :=
    fun ql a =>
       set_unions Q_dec (map (fun q' => ntf q' a) ql).

Definition NA_to_A {Q : Type} (na : @Accept Q) : @Accept (set Q) :=
  existsb na.

(* ----------------------------------------------------------------- *)  
(** *** Equivalence Proof *)

(** What follows is the proof that an NFA accepts a string [s] if and 
    only if the DFA we obtain from the transformation above accepts [s].
    This amounts to saying that the NFA and its transformation accept the
    same langauge. *)

Lemma emptyset_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (str : list A),
    eval_NFA ntf Q_dec [] str = [].
Proof.
  destruct str; reflexivity.
Qed.

Lemma cons_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (ql : set Q) (q q' : Q) (str : list A),
    In q' (eval_NFA ntf Q_dec (q :: ql) str) <-> In q' (set_union Q_dec (eval_NFA ntf Q_dec [q] str) (eval_NFA ntf Q_dec ql str)).
Proof.
  intros. destruct str.
  - rewrite set_union_iff. simpl.
    split; intros [H|H]; auto.
    destruct H; auto. contradiction.
  - reflexivity.
Qed.

Lemma set_add_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (ql : set Q) (q q' : Q) (str : list A),
    In q' (eval_NFA ntf Q_dec (set_add Q_dec q ql) str) <-> In q' (set_union Q_dec (eval_NFA ntf Q_dec [q] str) (eval_NFA ntf Q_dec ql str)).
Proof.
  intros. induction ql.
  - simpl. 
    rewrite set_union_iff. rewrite emptyset_lemma. simpl.
    split; auto. intros [H|H]. assumption. contradiction.
  - simpl. destruct (Q_dec q a).
    + subst. 
      rewrite set_union_iff.
      split; auto. intros [H|H].
      * destruct str; simpl in *.
        -- destruct H; auto. contradiction.
        -- rewrite set_union_iff. left. assumption.
      * assumption.
    + rewrite set_union_iff.
      rewrite cons_lemma. rewrite set_union_iff.
      rewrite IHql. rewrite set_union_iff.
      rewrite (cons_lemma Q A Q_dec ntf ql a).
      rewrite set_union_iff. split; intros [H|[H|H]]; auto.
Qed.

Lemma eval_union_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (ql1 ql2 : set Q) (str : list A),
    In q (eval_NFA ntf Q_dec (set_union Q_dec ql1 ql2) str) <->
    In q (set_union Q_dec (eval_NFA ntf Q_dec ql1 str) (eval_NFA ntf Q_dec ql2 str)).
Proof.
  intros. induction ql2.
  - rewrite emptyset_lemma. reflexivity.
  - simpl. rewrite set_add_lemma.
    repeat rewrite set_union_iff.
    rewrite (cons_lemma Q A Q_dec ntf ql2 a).
    rewrite IHql2.
    repeat rewrite set_union_iff.
    split; intros [H|[H|H]]; auto.
Qed.

Lemma eval_unions_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (ql : set Q) (a : A) (str : list A),
    In q (set_unions Q_dec
       (map (fun q' : Q => eval_NFA ntf Q_dec (ntf q' a) str) ql)) <->
   In q (eval_NFA ntf Q_dec
       (set_unions Q_dec (map (fun q' : Q => ntf q' a) ql)) str).
Proof.
  intros. induction ql.
  - simpl. rewrite emptyset_lemma. reflexivity.
  - simpl. rewrite eval_union_lemma.
    repeat rewrite set_union_iff. rewrite IHql. reflexivity.
Qed.

Lemma DFA_NFA_Equivalent_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (ql : set Q) (str : list A),
    In q (eval_NFA ntf Q_dec ql str) <-> In q (eval_DFA (NTF_to_TF ntf Q_dec) ql str).
Proof.
  intros. generalize dependent ql. induction str.
  - reflexivity.
  - intro ql.
    simpl. simpl in IHstr. rewrite <- IHstr.
    unfold NTF_to_TF. rewrite eval_unions_lemma. reflexivity.
Qed.

Theorem DFA_NFA_Equivalent : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (accept : Accept) (str : list A),
    accept_NFA q ntf accept Q_dec str = accept_DFA [q] (NTF_to_TF ntf Q_dec) (NA_to_A accept) str.
Proof.
  intros. destruct str; unfold accept_NFA; unfold accept_DFA.
  - reflexivity.
  - simpl.
    unfold NA_to_A. apply exists_accept_equal. assumption.
    intro q'. rewrite DFA_NFA_Equivalent_lemma.
    reflexivity.
Qed.

(* ----------------------------------------------------------------- *)  
(** *** Example NFA *)

(** We now instantiate an example of an NFA with no epsilon transitions.
    This simple example has some state-action pairs with no transition
    and some with multiple transitions. This NFA only accepts the 
    strings [0] and [01]. We compute its output on some example inputs
    and then prove a theorem characterizing the language it accepts. *)

Inductive example_Q_NFA : Type :=
| Q_start
| Q_accept0
| Q_accept1
.

Theorem example_Q_NFA_dec : forall x y : example_Q_NFA, {x = y} + {x <> y}.
Proof. intros x y. destruct x; destruct y;
       try (left; reflexivity); try (right; intro H; discriminate).
Defined.

Definition example_NTF (q : example_Q_NFA) (a : binary_A) :=
  match q with
  | Q_start => match a with
             | a0 => [Q_accept0; Q_accept1]
             | a1 => []
             end
  | Q_accept0 => match a with
               | _ => []
               end
  | Q_accept1 => match a with
               | a0 => []
               | a1 => [Q_accept0]
               end
  end.

Definition example_Accept_NFA (q : example_Q_NFA) :=
  match q with
  | Q_start => false
  | _ => true
  end.

Definition example_NFA := accept_NFA Q_start example_NTF example_Accept_NFA example_Q_NFA_dec.

Example example_NFA1 : example_NFA [] = false.
Proof. reflexivity. Qed.

Example example_NFA2 : example_NFA [a0] = true.
Proof. reflexivity. Qed.

Example example_NFA3 : example_NFA [a0;a1] = true.
Proof. reflexivity. Qed.

Example example_NFA4 : example_NFA [a1] = false.
Proof. reflexivity. Qed.

Example example_NFA5 : example_NFA [a0;a0] = false.
Proof. reflexivity. Qed.

Theorem example_NFA_accept : forall str,
  example_NFA str = true
  <-> str = [a0] \/ str = [a0;a1].
Proof.
  intros str. unfold example_NFA. unfold accept_NFA.
  split; intro H.
  - do 3 (try destruct str; try destruct b);
    try simpl in H; try rewrite emptyset_lemma in H;
    try discriminate; auto.
  - destruct H; subst; reflexivity.
Qed.

End NoEps.

Module Eps.

(* ----------------------------------------------------------------- *)  
(** *** Formalization of NFAs with Epsilon Transitions *)
  
(** We now extend the previous formalization of NFAs by adding epsilon
    transitions. We do this by using options for the action in the 
    transition function. We also write a new function which finds every
    state reachable using only epsilon transitions from a starting set
    of states that the evaluation function uses between each character
    read from teh input. For arbitrary transition functions, this is 
    actually impossible to compute directly since the set of reachable 
    states may be infinite. Hence, we add fuel to the evaluation function.
    Assuming the set of states is finite, it suffices for the fuel to be
    at least the number of states for computation to be correct. *)

Definition NTransition {Q A : Type} : Type := Q -> option A -> set Q.

Fixpoint eps_reachable {Q A} (fuel : nat) (ntf : @NTransition Q A)
         (Q_dec : forall (x y : Q), {x = y} + {x <> y})
         (q : set Q) : set Q :=
  match fuel with
  | 0 => q
  | S n =>
      set_union Q_dec q
        (eps_reachable n ntf Q_dec
           (set_unions Q_dec
             (map (fun q' => ntf q' None) q)))
  end.

Fixpoint eval_NFA {Q A} (fuel : nat) (ntf : NTransition)
         (Q_dec : forall (x y : Q), {x = y} + {x <> y})
         (q : set Q) (str : list A) : set Q :=
  match str with
  | [] => q
  | h::t =>
    set_unions Q_dec
      (map
        (fun q' =>
          eval_NFA fuel ntf Q_dec (eps_reachable fuel ntf Q_dec (ntf q' (Some h))) t) q)
  end.

Definition accept_NFA {Q A : Type} (fuel : nat) (start : Q)
         (ntf : NTransition) (accept : Accept)
         (Q_dec : forall (x y : Q), {x = y} + {x <> y})           
         (str : list A)
  : bool :=
  existsb accept (eval_NFA fuel ntf Q_dec (eps_reachable fuel ntf Q_dec [start]) str).
  
(** We now formalize the new transformation from NFAs to DFAs. It is 
    similar to the previous one, but now must use [eps_reachable] and
    also must transform the start state using [eps_reachable]. Also
    because we require fuel in the NFA, the DFA also takes fuel as input. *)

Definition NTF_to_TF {Q A : Type} (fuel : nat) (ntf : @NTransition Q A)
           (Q_dec : forall (x y : Q), {x = y} + {x <> y})
  : @Transition (set Q) A :=
    fun ql a =>
       set_unions Q_dec (map (fun q' => eps_reachable fuel ntf Q_dec (ntf q' (Some a))) ql).

Definition NA_to_A {Q : Type} (na : @Accept Q) : @Accept (set Q) :=
  existsb na.

Definition NS_to_S {Q A : Type} (fuel : nat) (start : Q) (ntf : @NTransition Q A) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) : set Q :=
  eps_reachable fuel ntf Q_dec [start].

(* ----------------------------------------------------------------- *)  
(** *** Equivalence Proof *)

(** We now do the version of the proof above for NFAs with epsilon 
    transitions. Since we now have fuel in the evaluation function, the
    statement we prove is that the NFA and its transformation accept the
    same language given the same fuel. The proof follows almost exactly 
    the same as the previous one. *)

Lemma eps_emptyset_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) fuel,
    eps_reachable fuel ntf Q_dec [] = [].
Proof.
  induction fuel.
  - reflexivity.
  - simpl. assert (H: empty_set Q = []). reflexivity.
    rewrite H. rewrite IHfuel. reflexivity.
Qed.

Lemma emptyset_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (str : list A) fuel,
    eval_NFA fuel ntf Q_dec [] str = [].
Proof.
  intros. destruct str; reflexivity.
Qed.

Lemma cons_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (ql : set Q) (q q' : Q) (str : list A) (fuel : nat),
    In q' (eval_NFA fuel ntf Q_dec (q :: ql) str) <-> In q' (set_union Q_dec (eval_NFA fuel ntf Q_dec [q] str) (eval_NFA fuel ntf Q_dec ql str)).
Proof.
  intros. destruct str.
  - rewrite set_union_iff. simpl.
    split; intros [H|H]; auto.
    destruct H; auto. contradiction.
  - reflexivity.
Qed.

Lemma set_add_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (ql : set Q) (q q' : Q) (str : list A) (fuel : nat),
    In q' (eval_NFA fuel ntf Q_dec (set_add Q_dec q ql) str) <-> In q' (set_union Q_dec (eval_NFA fuel ntf Q_dec [q] str) (eval_NFA fuel ntf Q_dec ql str)).
Proof.
  intros. induction ql.
  - simpl. 
    rewrite set_union_iff. rewrite emptyset_lemma. simpl.
    split; auto. intros [H|H]. assumption. contradiction.
  - simpl. destruct (Q_dec q a).
    + subst. 
      rewrite set_union_iff.
      split; auto. intros [H|H].
      * destruct str; simpl in *.
        -- destruct H; auto. contradiction.
        -- rewrite set_union_iff. left. assumption.
      * assumption.
    + rewrite set_union_iff.
      rewrite cons_lemma. rewrite set_union_iff.
      rewrite IHql. rewrite set_union_iff.
      rewrite (cons_lemma Q A Q_dec ntf ql a).
      rewrite set_union_iff. split; intros [H|[H|H]]; auto.
Qed.

Lemma eval_union_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (ql1 ql2 : set Q) (str : list A) (fuel : nat),
    In q (eval_NFA fuel ntf Q_dec (set_union Q_dec ql1 ql2) str) <->
    In q (set_union Q_dec (eval_NFA fuel ntf Q_dec ql1 str) (eval_NFA fuel ntf Q_dec ql2 str)).
Proof.
  intros. induction ql2.
  - rewrite emptyset_lemma. reflexivity.
  - simpl. rewrite set_add_lemma.
    repeat rewrite set_union_iff.
    rewrite (cons_lemma Q A Q_dec ntf ql2 a).
    rewrite IHql2.
    repeat rewrite set_union_iff.
    split; intros [H|[H|H]]; auto.
Qed.

Lemma eval_unions_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (ql : set Q) (a : A) (str : list A) fuel,
    In q (set_unions Q_dec
      (map (fun q' : Q => eval_NFA fuel ntf Q_dec
        (eps_reachable fuel ntf Q_dec (ntf q' (Some a))) str) ql)) <->
    In q (eval_NFA fuel ntf Q_dec
      (set_unions Q_dec (map (fun q' : Q =>
        eps_reachable fuel ntf Q_dec (ntf q' (Some a))) ql)) str).
Proof.
  intros. induction ql.
  - simpl. rewrite emptyset_lemma. reflexivity.
  - simpl. rewrite eval_union_lemma.
    repeat rewrite set_union_iff. rewrite IHql. reflexivity.
Qed.

Lemma DFA_NFA_Equivalent_lemma : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (ql : set Q) (str : list A) fuel,
      In q (eval_NFA fuel ntf Q_dec ql str) <->
      In q (eval_DFA (NTF_to_TF fuel ntf Q_dec) ql str).
Proof.
  intros. unfold NTF_to_TF. generalize dependent ql.
  induction str; intro ql.
  - reflexivity.
  - simpl. rewrite <- IHstr.
    apply eval_unions_lemma.
Qed.    

Theorem DFA_NFA_Equivalent : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (ntf : @NTransition Q A) (q : Q) (accept : Accept) (str : list A) fuel,
    accept_NFA fuel q ntf accept Q_dec str = accept_DFA (NS_to_S fuel q ntf Q_dec) (NTF_to_TF fuel ntf Q_dec) (NA_to_A accept) str.
Proof.
  intros. destruct str; unfold accept_NFA; unfold accept_DFA.
  - reflexivity.
  - unfold NA_to_A. apply exists_accept_equal. assumption.
    intro q'. rewrite DFA_NFA_Equivalent_lemma. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)  
(** *** Example NFA *)

(** We now instantiate an example of an NFA with epsilon transitions.
    This NFA has a start state with epsilon transitions to two states.
    The first state only has a transition to itself on action 0. The
    second state only has a transition to itself on action 1. Therefore,
    the NFA only accepts the empty string, strings of all 0s, and strings
    of all 1s. We compute its output on some examples and prove a theorem
    characterizing the language it accepts. *)

Inductive example_Q_NFA : Type :=
| Q_start
| Q_accept0
| Q_accept1
.

Theorem example_Q_NFA_dec : forall x y : example_Q_NFA, {x = y} + {x <> y}.
Proof. intros x y. destruct x; destruct y;
       try (left; reflexivity); try (right; intro H; discriminate).
Defined.

Definition example_NTF (q : example_Q_NFA) (oa : option binary_A) :=
  match q with
  | Q_start => match oa with
             | None => [Q_accept0; Q_accept1]
             | _ => []
             end
  | Q_accept0 => match oa with
               | Some a0 => [Q_accept0]
               | _ => []
               end
  | Q_accept1 => match oa with
               | Some a1 => [Q_accept1]
               | _ => []
               end
  end.

Definition example_Accept_NFA (q : example_Q_NFA) :=
  match q with
  | Q_start => false
  | _ => true
  end.

Definition example_NFA := accept_NFA 1 Q_start example_NTF example_Accept_NFA example_Q_NFA_dec.

Example example_NFA1 : example_NFA [] = true.
Proof. reflexivity. Qed.

Example example_NFA2 : example_NFA [a0;a0] = true.
Proof. reflexivity. Qed.

Example example_NFA3 : example_NFA [a1;a1;a1] = true.
Proof. reflexivity. Qed.

Example example_NFA4 : example_NFA [a1;a1;a0] = false.
Proof. reflexivity. Qed.

Example example_NFA5 : example_NFA [a0;a1;a0;a0] = false.
Proof. reflexivity. Qed.

Theorem example_NFA_accept : forall str,
  example_NFA str = true
  <-> (forall a, In a str -> a = a0) \/ (forall a, In a str -> a = a1).
Proof.
  intros str. unfold example_NFA.
  unfold accept_NFA. simpl.
  split.
  - intro H. destruct str.
    + left. intros. contradiction.
    + simpl in H. destruct b; simpl in H;
      repeat rewrite emptyset_lemma in H.
      * left. induction str.
        -- simpl. intros. destruct H0; try contradiction.
           symmetry. assumption.
        -- simpl. destruct a.
           ++ simpl in H.
              intros. symmetry.
              destruct H0 as [H1|H1]; destruct H1; try assumption.
              reflexivity. symmetry.
              apply IHstr. apply H.
              simpl. right. apply H0.
           ++ simpl in H. rewrite emptyset_lemma in H.
              discriminate H.
      * right. induction str.
        -- simpl. intros. destruct H0; try contradiction.
           symmetry. assumption.
        -- simpl. destruct a.
           ++ simpl in H. rewrite emptyset_lemma in H.
              discriminate H.
           ++ simpl in H.
              intros. symmetry.
              destruct H0 as [H1|H1]; destruct H1; try assumption.
              reflexivity. symmetry.
              apply IHstr. apply H.
              simpl. right. apply H0.
  - intros [H|H].
    + destruct str.
      * reflexivity.
      * destruct b.
        -- simpl.
           repeat rewrite emptyset_lemma.
           induction str.
           ++ reflexivity.
           ++ destruct a.
              ** simpl.
                 apply IHstr. intros.
                 symmetry. destruct H0; try assumption.
                 symmetry. apply H. simpl.
                 right. right. assumption.
              ** assert (contra: a1 <> a0). intro contra. discriminate.
                 exfalso. apply contra. apply H.
                 right. left. reflexivity.
        -- assert (contra: a1 <> a0). intro contra. discriminate.
           exfalso. apply contra. apply H.
           left. reflexivity.
    + destruct str.
      * reflexivity.
      * destruct b.
        -- assert (contra: a0 <> a1). intro contra. discriminate.
           exfalso. apply contra. apply H.
           left. reflexivity.
        -- simpl.
           repeat rewrite emptyset_lemma.
           induction str.
           ++ reflexivity.
           ++ destruct a.
              ** assert (contra: a0 <> a1). intro contra. discriminate.
                 exfalso. apply contra. apply H.
                 right. left. reflexivity.
              ** simpl.
                 apply IHstr. intros.
                 symmetry. destruct H0; try assumption.
                 symmetry. apply H. simpl.
                 right. right. assumption.
Qed.

End Eps.

End FunctionImplementation.


Module RelationImplementation.

Module NoEps.
  
Definition Transition {Q A : Type} : Type := Q -> A -> Q -> Prop.
Definition Accept {Q : Type} : Type := Q -> bool.

Definition finite (Q : Type) : Prop :=
  exists (U : set Q), forall (q : Q), In q U.

Definition deterministic {Q A : Type} (Q_eq : Q -> Q -> Prop) (tf : @Transition Q A) : Prop :=
  forall q a q1 q2,
      tf q a q1 -> tf q a q2 -> Q_eq q1 q2.


Reserved Notation "'A[' tf '@' q ']' str '=>' r" (at level 90, left associativity).

Inductive Automaton_eval {Q A : Type} : Transition -> Q -> list A -> Q -> Prop :=
| A_Empty : forall tf q, A[tf @ q] [] => q
| A_Step : forall (tf : Transition) q q' a str r,
    tf q a q' -> A[tf @ q'] str => r -> A[tf @ q] (a :: str) => r

where "'A[' tf '@' q ']' str '=>' r" := (Automaton_eval tf q str r) : type_scope.


Definition Automaton_accept {Q A : Type} (tf : Transition) (q : Q) (str: list A) (accept : Accept) : Prop :=
  exists r, (A[tf @ q] str => r) /\ accept r = true.

Notation "'A[' tf '@' q ']' str '<-' accept" := (Automaton_accept tf q str accept) (at level 90, left associativity).

Inductive DTransform {Q A : Type} (U : set Q) (ntf : @Transition Q A) : @Transition (set Q) A :=
| N_to_D : forall ql a ql',
    (forall q, In q ql -> In q U) -> (forall q', In q' ql' -> In q' U) ->
    (forall q', In q' U -> In q' ql' -> exists q, (In q U /\ ntf q a q' /\ In q ql)) ->
    (forall q q', In q U -> In q' U -> ntf q a q' -> In q ql -> In q' ql') ->
    DTransform U ntf ql a ql'
.

Definition set_eq {Q : Type} (ql1 ql2 : set Q) : Prop :=
  forall q, In q ql1 <-> In q ql2.

Definition setAccept {Q : Type} (accept : @Accept Q) : @Accept (set Q) :=
  existsb accept.


Lemma singletonIn : forall (Q : Type) (q q' : Q), In q [q'] <-> q = q'. 
Proof.
  split; intro H.
  destruct H. symmetry. assumption. contradiction.
  left. symmetry. assumption.
Qed.

Ltac list_auto :=
  repeat (match goal with
          | [ |- _ /\ _ ] => split
          | [ |- _ <-> _ ] => split
          | [ H: _ /\ _  |- _ ] => destruct H
          | [ |- _ -> _ ] => intro
          | [ H: In ?q [] |- _ ] => destruct H
          | [ H: In ?q [?q'] |- _ ]=> destruct H as [H|[]]
          | [ H: In ?q (?q' :: ?ql) |- _ ] => destruct H
          | [ H: _ \/ _  |- _ ] => destruct H
          | [ HIn: In ?q ?ql,
              HU: forall q : ?Q, In q ?ql -> In q ?U
              |- In ?q ?U ] => apply HU
          | _ => rewrite singletonIn
          | [ |- In ?q (?q' :: ?ql) ] =>
              try solve[left; list_auto]; try solve [right; list_auto]
          end; subst); try tauto.

Lemma DTransform_singleton_lemma : forall (Q A : Type) (U : set Q) (q : Q) (a : A) (ntf : @Transition Q A) (ntf_dec : forall q a q', {ntf q a q'} + {~ ntf q a q'}),
    exists ql, DTransform (q :: U) ntf [q] a ql.
Proof with list_auto.
  intros Q A U q a ntf ntf_dec.
  induction U as [|q_new U'].
  - destruct (ntf_dec q a q).
    + exists [q]. constructor; auto.
      intros q' HIn1 HIn2. exists q'...
    + exists [].
      constructor; list_auto.
  - destruct IHU' as [ql IHU'].
    inversion IHU'; subst; clear IHU'.
    destruct (ntf_dec q a q_new).
    + exists (q_new :: ql).
      constructor; intros; try eexists; list_auto;
        try solve[destruct H1 with q'; list_auto];
        try solve[right; eapply H2; list_auto].
      apply H0 in H3...
    + exists ql.
      constructor; intros; try eexists; list_auto;
        try solve[destruct H1 with q'; list_auto; try apply H0; list_auto];
        try solve[eapply H2; list_auto].
      apply H0 in H3...
Qed.

Lemma DTransform_universe : forall (Q A : Type) (U U' ql ql' : set Q) (a : A) (ntf : @Transition Q A),
    (forall q, In q U <-> In q U') ->
    DTransform U ntf ql a ql' -> DTransform U' ntf ql a ql'.
Proof with list_auto.
  intros Q A U U' ql ql' a ntf Heq HU.
  inversion HU; subst; clear HU.
  constructor...
  - apply Heq. apply H...
  - apply Heq. apply H0...
  - destruct H1 with q'...
    exists x...
    apply Heq...
  - apply H2 with q...
    apply Heq...
Qed.

Lemma DTransform_singleton : forall (Q A : Type) (U : set Q) (q : Q) (a : A) (ntf : @Transition Q A) (ntf_dec : forall q a q', {ntf q a q'} + {~ ntf q a q'}),
    In q U -> exists ql, DTransform U ntf [q] a ql.
Proof with list_auto.
  intros Q A U q a ntf ntf_dec HIn.
  destruct (DTransform_singleton_lemma Q A U q a ntf ntf_dec) as [ql H].
  exists ql. apply DTransform_universe with (q :: U)...
Qed.


Theorem DTransform_deterministic : forall (Q A : Type) (U : set Q) (ntf : @Transition Q A),
    deterministic set_eq (DTransform U ntf).
Proof with list_auto.
  unfold deterministic. unfold set_eq.
  intros Q A U ntf q a q1 q2 H1 H2 q'.
  inversion H1; inversion H2; subst; clear H1 H2...
  - destruct H3 with q'...
    apply H11 with x...
  - destruct H10 with q'...
    apply H4 with x...
Qed.

Theorem DTransform_progress : forall (Q A : Type) (Q_dec : forall (x y : Q), {x = y} + {x <> y}) (U ql : set Q) (a : A) (ntf : @Transition Q A) (ntf_dec : forall q a q', {ntf q a q'} + {~ ntf q a q'}),
    (forall q, In q ql -> In q U) ->
      exists ql' : set Q, DTransform U ntf ql a ql'.
Proof with list_auto.
  intros Q A Q_dec U ql a ntf ntf_dec Hsub.
  induction ql as [|q ql].
  - exists []. constructor...
  - destruct IHql as [ql' IHql]...
    apply Hsub...
    destruct (DTransform_singleton Q A U q a ntf ntf_dec) as [qlq Hqlq].
    apply Hsub...
    exists (set_union Q_dec qlq ql').
    inversion IHql; inversion Hqlq; subst.
    constructor...
    + apply Hsub...
    + rewrite set_union_iff in *...
    + rewrite set_union_iff in *...
      * destruct H8 with q'...
        exists x...
      * destruct H1 with q'...
        exists x...
    + rewrite set_union_iff. left. apply H9 with q0...
    + rewrite set_union_iff. right. apply H2 with q0...
Qed.

Lemma DTransform_evaluates : forall (Q A : Type) (Q_dec : forall x y : Q, {x = y} + {x <> y}) (U : set Q) (ntf : @Transition Q A) (ntf_dec : forall (q : Q) (a0 : A) (q' : Q), {ntf q a0 q'} + {~ ntf q a0 q'}) (ql : set Q) str,
    (forall q, In q ql -> In q U) ->
    exists rl, A[(DTransform U ntf) @ ql] str => rl.
Proof.
  intros Q A Q_dec U ntf ntf_dec ql str Hsub.
  generalize dependent ql. induction str; intros ql Hsub.
  - exists ql. constructor.
  - destruct (DTransform_progress Q A Q_dec U ql a ntf ntf_dec Hsub) as [ql' Hntf].
    destruct IHstr with ql' as [rl IH].
    + intros q HIn. inversion Hntf; subst.
      apply H0. assumption.
    + exists rl. econstructor.
      apply Hntf. assumption.
Qed.

Lemma DTransform_subset : forall (Q A : Type) (U ql ql' rl rl' : set Q) (ntf : @Transition Q A) str,
    (forall q, In q ql -> In q ql') ->
    A[DTransform U ntf @ ql] str => rl ->
    A[DTransform U ntf @ ql'] str => rl' ->
    (forall r, In r rl -> In r rl').
Proof.
  intros Q A U ql ql' rl rl' ntf str Hsub HA HA' r HIn.
  generalize dependent ql. generalize dependent ql'.
  induction str; intros ql' HA' ql Hsub HA;
  inversion HA; inversion HA'; subst; clear HA HA'.
  - apply Hsub. assumption.
  - inversion H3; inversion H10; subst; clear H3 H10.
    eapply IHstr.
    + apply H12.
    + intros q HInq. destruct H1 with q as [q'' [HUq [Hntf HInql]]].
      apply H0. apply HInq.
      assumption.
      apply H13 with q''.
      assumption.
      apply H0. assumption.
      assumption.
      apply Hsub. assumption.
    + assumption.
Qed.

Lemma DTransform_Equivalent_reverse : forall (Q A : Type) (Q_dec : forall x y : Q, {x = y} + {x <> y}) (U : set Q) (ntf : @Transition Q A) (ntf_dec : forall (q : Q) (a0 : A) (q' : Q), {ntf q a0 q'} + {~ ntf q a0 q'}) (ql rl : set Q) (r : Q) (str: list A),
    In r rl -> A[(DTransform U ntf) @ ql] str => rl ->
      exists q rl', In q ql /\ (forall r, In r rl' -> In r rl)
        /\ In r rl' /\ A[(DTransform U ntf) @ [q]] str => rl'.
Proof with list_auto.
  intros Q A Q_dec U ntf ntf_dec ql rl r str HInr Heval.
  remember (DTransform U ntf).
  induction Heval as [tf ql|tf ql ql' a str rl']; subst.
  - exists r. exists [r]...
    constructor.
  - destruct (IHHeval HInr)
      as [q' [rl [HInq' [Hsub [HInr' Heval']]]]]. reflexivity.
    inversion H; subst; clear H.
    destruct H2 with q' as [q [HUq [Hntf HInq]]]...
    destruct (DTransform_evaluates Q A Q_dec U ntf ntf_dec [q] (a :: str))
      as [rl'' Heval'']...
    exists q. exists rl''...
    + inversion Heval''; subst; clear Heval''.
      apply (DTransform_subset Q A U q'0 ql' rl'' rl' ntf str)...
      inversion H8; subst; clear H8.
      apply H3 with q...
      destruct H7 with q0...
    + inversion Heval''; subst; clear Heval''.
      assert (Hsubr: forall r, In r rl -> In r rl'').
      { apply (DTransform_subset Q A U [q'] q'0 rl rl'' ntf str)...
        inversion H7; subst; clear H7.
        apply H6 with q... }
      apply Hsubr...
Qed.

Theorem DTransform_Equivalent_forward : forall (Q A : Type) (Q_dec : forall x y : Q, {x = y} + {x <> y}) (U : set Q) (ntf : @Transition Q A) (ntf_dec : forall (q : Q) (a0 : A) (q' : Q), {ntf q a0 q'} + {~ ntf q a0 q'}) (q r : Q) (ql rl : set Q) (str: list A),
    (forall q', In q' U) -> In q ql ->
      A[ntf @ q] str => r -> A[DTransform U ntf @ ql] str => rl ->
      In r rl.
Proof with list_auto.
  intros Q A Q_dec U ntf ntf_dec q r ql rl str HU HIn Hevaln Hevald.
  generalize dependent q. generalize dependent ql.
  induction str; intros ql Hevald q Hin Hevaln;
    inversion Hevald; inversion Hevaln; subst...
  apply IHstr with (q:=q'0) (ql:=q')...
  inversion H3; subst; clear H3.
  apply H2 with q...
  apply HU.
Qed.

Theorem DTransform_Equivalent : forall (Q A : Type) (Q_dec : forall x y : Q, {x = y} + {x <> y}) (U : set Q) (ntf : @Transition Q A) (ntf_dec : forall (q : Q) (a0 : A) (q' : Q), {ntf q a0 q'} + {~ ntf q a0 q'}) (q : Q) (str: list A) (accept : Accept),
    (forall q', In q' U) ->
    A[ntf @ q] str <- accept <-> A[(DTransform U ntf) @ [q]] str <- (setAccept accept).
Proof with list_auto.
  intros Q A Q_dec U ntf ntf_dec q str accept HU. 
  unfold Automaton_accept.
  split. 
  - intros [r [Hevaln Haccept]].
    destruct (DTransform_evaluates Q A Q_dec U ntf ntf_dec [q] str)
      as [rl Hevald]... apply HU.
    exists rl...
    rewrite existsb_exists.
    exists r... 
    eapply DTransform_Equivalent_forward with (q:=q) (ql:=[q]).
    apply Q_dec. apply ntf_dec. apply HU.
    left. reflexivity.
    apply Hevaln. apply Hevald.
  - intros [rl [Heval Haccept]].
    apply existsb_exists in Haccept.
    destruct Haccept as [r [HInr Hacceptr]].
    exists r...
    generalize dependent q. generalize dependent rl.
    induction str; intros rl HInr q Heval.
    + inversion Heval; subst...
      constructor.
    + inversion Heval; subst; clear Heval.
      destruct
        (DTransform_Equivalent_reverse Q A Q_dec U ntf ntf_dec q' rl r str)
      as [q'' [rl' [HInq' [Hsubr [HInr' Heval']]]]]...
      apply A_Step with q''.
      * inversion H3; subst; clear H3.
        destruct H1 with q''...
      * apply IHstr with rl'; assumption.
Qed.

End NoEps.
  
End RelationImplementation.
