Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Proportional.
Require Import QuantumLib.GenMatrix.
Require Export SQIR.UnitarySem.
Require Import QuantumLib.Matrix.
Require Import String.
Local Open Scope ucom.


Definition qubit0 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition qubit1 : Vector 2 := 
fun x y => match x, y with 
        | 0, 0 => C0
        | 1, 0 => C1
        | _, _ => C0
        end.
Defintion qubit := qubit0 | qubit1.

Definition unitary := base_ucom 2.

Inductive Pauli := I | σx | σy | σz.

Definition stabilizer (ψ : qubit) (A: unitary) : Prop :=
    uc_eval (A) × ψ = ψ.

(* Stabilizer variable s ∈ ⊗^n {I, X, Y, Z} *)
Inductive __stabilizer_integral_type  :=
  | snek (s: stabilizer)
  | minus_s (s: stabilizer)
  | i_s (s: stabilizer)
  | minus_i_s (s: stabilizer).

Notation "∫" :=  __stabilizer_integral_type.
(* N.B ∫ is a variable. Like x or y or z. typically, x or y or z denote numbers of some kind
∫ denotes some kind of stabilizer gate. We could've called it U or S but the paper chose ∫ ...
*)

Notation "±" := - | +.

Inductive stabilizer_value := | Plus (s: stabilizer) | Minus (s: stabilizer) | I s | MinusI s | Var (S: stabilizer_variable).

Inductive Prog :=
    | Skip
    | InitializeToZero (q: qubit)
    | UnitaryTransform (U: unitary) (q: qubit)
    | Seq (p1 p2: Prog)
    | Case (M: unitary) (q: qubit) (m: nat) (body: Prog)
    | While (B: unitary) (q: qubit) (body: Prog)
    .
(*Should M be any unitary or only positive hermitian? and is M implicitly applied to the whole state prior to measurement*)


(* For operational semantics ∫😊🤩😶‍🌫️🙃😱👽👻🦊🐭🦧🎆🎈🎆🎇✨🎉🎊 *)

Inductive QEC_Condition :=
    | condition (M: unitary) (∫ : InitializeStabilizer) (q: qubit).

Definition stabilizer_var := string.

Definition stabilizer_eq : forall (v1 v2 : stabilizer_var), {v1 = v2} + {v1 <> v2} := string_dec.

Definition stabilizer_map := list (stabilizer_var * stabilizer_value).

Definition empty_stabilizer_map: stabilizer_map := nil.

Definition set_stabilizer (s: stabilizer_var) (v: stabilizer_value) (m: stabilizer_map): stabilizer_map :=
    cons (s, v) m
.

Definition lookup_stabilizer (s: stabilizer_var) (m: stabilizer_map): option stabilizer_value :=
    match m with
    | nil => None
    | cons (s', v) m' =>
        if stabilizer_eq s s'
        then Some v
        else lookup_stabilizer s m'
    end.

Definition qubit_eq : forall (v1 v2 : qubit), {v1 = v2} + {v1 <> v2} := string_dec.


Inductive QECV_Lang := 
    | Skip
    | InitializeToZero (q: qubit)
    | UnitaryTransform (U: unitary) (q: qubit)
    | InitializeStabilizer (s: stabilizer_var) (s_e_u: stabilizer_value)
    | Seq (p1 p2: QECV_Lang)
    | If (condition: QEC_Condition) (cthen: QECV_Lang) (celse: QECV_Lang)
    | While (condition: QEC_Condition) (body: QECV_Lang)
    .

Notation E := (0, {}).
Notation c := 1 | -1 | i | -.

Inductive stabilizer_expr :=
| StabilizerConst stabilizer_value
| StabilizerVar stabilizer_var

Inductive step_stabilizer : stabilizer_expr * stabilizer_map -> stabilizer_value :=
| StabilizerExprConst : forall c s σ, 
                        step_stabilizer (StabilizerConst (dot c s), σ) (dot c s)
| StabilizerExprVar   : forall ∫ σ, 
                        step_stabilizer (± StabilizerVar ∫, σ) (± lookup_stabilizer ∫ σ).

(* C is defined as a pair of reals (a field), and Matrices are defined as a ring (superset of field). *)
(* there are two if and while cases to account for the two eigenvalues, -1 being the error*)
Inductive step : cmd * stabilizer_map -> cmd * stabilizer_map :=
| Skip              : forall ρ σ, 
                      step (skip, (ρ σ)) (E, (ρ σ))
| Initialization    : forall q ρ σ,
                      step (set_qubit q ∣0⟩ q, (ρ σ)) (E, (trace q ρ) σ)
| Unitary           : forall q ρ σ,
                      step (set_qubit q U∣0⟩ q, (ρ σ)) (E, U ρ (U †), σ)
| Sequence_E        : forall Prog ρ σ,
                      step (Seq E Prog, (ρ σ)) (Prog, ρ σ)
| Stabilizer_exp1   : forall ρ σ,
                      step (set_stabilizer ρ (dot c s) ρ) (dot c s) 
| Stabilizer_exp2   : forall ∫ σ,
                      step (± ∫ ,σ) (± σ ∫) ρ (Mmult c s) (Mmult c s) 
| Assignment        : forall s_e_u ρ σ c s,
                      step_stabilizer (s_e_u, σ) (dot c s) ->
                      step (InitializeStabilizer ∫ s_e_u, (ρ, σ)) (E, (ρ, set_stabilizer ∫ (dot c s) σ))
| Sequence          : forall Prog1 ρ σ Prog1' ρ' σ' Prog2,
                      step (Prog1, (ρ, σ)) (Prog1', (ρ' σ')) ->
                      step (Seq Prog1 Prog2, (ρ, σ)) (Seq Prog1' Prog2, (ρ' σ'))
| If_minus1         : forall ρ σ ∫ q Prog0 Prog1,
                      M_0 = (I - ∫)/2 ->
                        step (If (probability_of_outcome (set_qubit q ∫ q) ∣1⟩) Prog1 Prog0, (ρ, σ))
                             (Prog0, (M_0 ρ (M_0 †), set_stabilizer ∫ (-σ ∫) σ))
| If_plus1          : forall ρ σ ∫ q Prog0 Prog1,
                      M_1 = (I + ∫) / 2 ->
                        step ((If (probability_of_outcome (set_qubit q ∫ q) ∣0⟩) Prog1 Prog0), (ρ, σ))
                              (Prog1, (M_1 ρ (M_1 †), σ))
| While_minus1      : forall ρ σ ∫ q_prime Prog0 Prog1,
                      M_0 = (I - ∫) / 2 ->
                        step (While (probability_of_outcome (set_qubit q ∫ q) ∣1⟩) Prog1, (ρ, σ))
                             (E, (M_0 ρ (M_0 †), set_stabilizer ∫ (-σ ∫) σ))
| While_plus1       : forall ρ σ ∫ q Prog0 Prog1,
                      M_1 = (I + ∫) / 2 ->
                        step (While (probability_of_outcome (set_qubit q ∫ q) ∣0⟩) Prog1, (ρ, σ))
                             (Seq Prog1 (While (probability_of_outcome (set_qubit q ∫ q) ∣0⟩) Prog1), (M_1 ρ (M_1 †), σ))



