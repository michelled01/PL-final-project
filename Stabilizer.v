Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Proportional.
Require Import QuantumLib.GenMatrix.
Require Export SQIR.UnitarySem.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Measurement.
Require Import String.
Local Open Scope ucom.

Definition qubit := Vector 2.

Definition unitary := base_ucom 1.

Inductive Pauli := I | σx | σy | σz.

(* Relevant definitions
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => big_sum (fun y => A x y * B y z)%C n. *)
  
(* Check uc_eval Matrix . *)

Definition stabilizer_pair (ψ : qubit) (A: unitary) : Prop :=
    Mmult (o := 1) (uc_eval A) ψ = ψ.

Inductive stabilizer : unitary -> Prop := 
    | eigenstate: forall ψ A, stabilizer_pair ψ A -> stabilizer A.

(* Stabilizer variable s ∈ ⊗^n {I, X, Y, Z} *)
Inductive __stabilizer_integral_type  :=
    | snek (A: unitary) (s: stabilizer A)
    | minus_s (s: __stabilizer_integral_type)
    | i_s (s: __stabilizer_integral_type)
    | minus_i_s (s: __stabilizer_integral_type).

(* Notation "Integral" :=  __stabilizer_integral_type. *)
(* N.B Integral is a variable. Like x or y or z. typically, x or y or z denote numbers of some kind
Integral denotes some kind of stabilizer gate. We could've called it U or S but the paper chose Integral ...
*)

(*Should M be any unitary or only positive hermitian? and is M implicitly applied to the whole state prior to measurement*)


(* For operational semantics ∫😊🤩😶‍🌫️🙃😱👽👻🦊🐭🦧🎆🎈🎆🎇✨🎉🎊 *)


Definition stabilizer_var := string.

Inductive stabilizer_value :=
    | Plus (A: unitary) (s: stabilizer A)
    | Minus (s: stabilizer_value)
    | PlusI (s: stabilizer_value)
    | MinusI (s: stabilizer_value)
    | Var (s: stabilizer_var).

Definition stabilizer_eq : forall (v1 v2 : stabilizer_var), {v1 = v2} + {v1 <> v2} := string_dec.

Definition stabilizer_map := list (stabilizer_var * stabilizer_value).

Definition empty_stabilizer_map: stabilizer_map := nil.

Definition set_stabilizer (s: stabilizer_var) (v: stabilizer_value) (m: stabilizer_map): stabilizer_map :=
    cons (s, v) m
.

Fixpoint lookup_stabilizer (s: stabilizer_var) (m: stabilizer_map): option stabilizer_value :=
    match m with
    | nil => None
    | cons (s', v) m' =>
        if stabilizer_eq s s'
        then Some v
        else lookup_stabilizer s m'
    end.

(* Definition qubit_eq : forall (v1 v2 : qubit), {v1 = v2} + {v1 <> v2} := qubit_dec. *)

Inductive QEC_Condition :=
| condition (M: unitary) (A: stabilizer_var).

Inductive QECV_Lang := 
    | Skip
    | InitializeToZero (q: nat)
    | UnitaryTransform (U: unitary)
    | InitializeStabilizer (s: stabilizer_var) (s_e_u: stabilizer_value)
    | Seq (p1 p2: QECV_Lang)
    | If (condition: QEC_Condition) (cthen: QECV_Lang) (celse: QECV_Lang)
    | While (condition: QEC_Condition) (body: QECV_Lang)
.

Fixpoint eval_stabilizer (s: stabilizer_value) (m: stabilizer_map): stabilizer_value :=
    match s with
    | Plus A s => Plus A s
    | Minus s => Minus (eval_stabilizer s m)
    | PlusI s => PlusI (eval_stabilizer s m)
    | MinusI s => MinusI (eval_stabilizer s m)
    | Var v => match lookup_stabilizer v m with
        | Some val => val
        | None => s
        end
    end.

(* Inductive step_stabilizer : stabilizer_expr * stabilizer_map -> stabilizer_value -> Prop :=
| StabilizerExprConst : forall c s σ, 
                        step_stabilizer (StabilizerConst (Stabilizer), σ) s
| StabilizerExprVar   : forall I σ,
                        step_stabilizer (StabilizerVar I, σ) (lookup_stabilizer I σ). *)

(* C is defined as a pair of reals (a field), and Matrices are defined as a ring (superset of field). *)
(* There are two if and while cases to account for the two eigenvalues, -1 being the error*)
Definition qubit_state := Matrix 2 2.
(* TODO: FIX THIS *)
Definition partial_trace (q: nat) (s: qubit_state): qubit_state := s.

(* | Skip              : forall ρ σ, 
                      step (Skip, (ρ, σ)) (E, (ρ, σ)). *)
Inductive step : QECV_Lang * (qubit_state * stabilizer_map) -> QECV_Lang * (qubit_state * stabilizer_map) -> Prop :=
| Initialization    : forall q ρ σ,
                      step (InitializeToZero q, (ρ, σ)) (Skip, (partial_trace q ρ, σ))
| Unitary           : forall U ρ σ,
                      step (UnitaryTransform U, (ρ, σ)) (Skip, (Mmult (uc_eval U) (Mmult ρ ((uc_eval U) †)), σ))
| Sequence_E        : forall Prog ρ σ,
                      step (Seq Skip Prog, (ρ, σ)) (Prog, (ρ, σ))
| Sequence          : forall Prog1 ρ σ Prog1' ρ' σ' Prog2,
                      step (Prog1, (ρ, σ)) (Prog1', (ρ', σ')) ->
                      step (Seq Prog1 Prog2, (ρ, σ)) (Seq Prog1' Prog2, (ρ', σ'))
| Assignment        : forall s_e_u ρ σ Integral ,
                      step (InitializeStabilizer Integral  s_e_u, (ρ, σ)) (Skip, (ρ, set_stabilizer Integral (eval_stabilizer s_e_u σ) σ))
| If_minus1         : forall ρ σ Integral q Prog0 Prog1 M_0,
                      M_0 = (I - Integral)/2 ->
                        step (If 
                            (QEC_Condition U A)
                            (* (probability_of_outcome (set_qubit q Integral q) ∣1⟩) *)
                            Prog1
                            Prog0, (ρ, σ))
                            (Prog0, (M_0 ρ (M_0 †), set_stabilizer Integral (-σ Integral) σ))
.
| If_plus1          : forall ρ σ Integral q Prog0 Prog1 M_1,
                      M_1 = (I + Integral) / 2 ->
                        step ((If (probability_of_outcome (set_qubit q Integral q) ∣0⟩) Prog1 Prog0), (ρ, σ))
                              (Prog1, (M_1 ρ (M_1 †), σ))
| While_minus1      : forall ρ σ Integral q_prime Prog0 Prog1 M_0,
                      M_0 = (I - Integral) / 2 ->
                        step (While (probability_of_outcome (set_qubit q Integral q) ∣1⟩) Prog1, (ρ, σ))
                             (E, (M_0 ρ (M_0 †), set_stabilizer Integral (-σ Integral) σ))
| While_plus1       : forall ρ σ Integral q Prog0 Prog1 M_1,
                      M_1 = (I + Integral) / 2 ->
                        step (While (probability_of_outcome (set_qubit q Integral q) ∣0⟩) Prog1, (ρ, σ))
                             (Seq Prog1 (While (probability_of_outcome (set_qubit q Integral q) ∣0⟩) Prog1), (M_1 ρ (M_1 †), σ))
.

Inductive step2: QECV_Lang * (qubit_state * stabilizer_map) -> QECV_Lang -> Prop :=
| Stab_exp1         : forall ρ σ s,
                      step (set_stabilizer ρ s σ) s
.
| Stab_exp2_minus   : forall ∬ σ,
                      step (∬ ,σ) (σ ∬) ρ s s 
| Stab_exp2_plus    : forall Integral σ,
                      step (-Integral ,σ) (-σ Integral) ρ s s
.