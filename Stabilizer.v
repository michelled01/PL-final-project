Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.GenMatrix.
Require Export SQIR.UnitarySem.

Local Open Scope ucom.


(* model from https://arxiv.org/pdf/2111.13728.pdf  *)
Inductive Pauli := I | σx | σy | σz.
(* 
Define s ∈ ⊗^n {I, X, Y, Z} to be a stabilizer of 
n-qubit state |ψ〉if s|ψ〉 = |ψ〉
*)

Definition stabilizer (n dim: nat) (ψ : Vector (2^n)) (A: Square (2^n)) : Prop :=
    A × ψ = ψ.

(* Stabilizer variable s ∈ ⊗^n {I, X, Y, Z} *)
Definition "∫" := | stabilizer | −stabilizer | i*stabilizer | −i*stabilizer.
(*Note: check how variables were defined in expr lang and imp lang from p1/p2

Notation var := string.
Definition var_eq : forall v1 v2 : var, {v1 = v2} + {v1 <> v2} := string_dec.

∫ is a variable. Like x or y or z. typically, x or y or z denote numbers of some kind
∫ denotes some kind of stabilizer gate. We could've called it U or S but the paper chose ∫ ...

*)

Inductive stabilizer_variable := (s: stabilizer) | ± s | ±i * s | (∫: stabilizer_variable)  

(*  by Lemma 4.1 and Proposition 4.2, introduce arith-
metic expressions of stabilizers  *)

(* formulate the assertion language QECV-Assn  *)

(* add Lemma 4.3  *)

Definition qubit (n : nat) := Vector (2^n).

Inductive Prog :=
    | Skip
    | InitializeToZero (q: qubit)
    | UnitaryTransform (U: ucom) (q: qubit)
    | Seq (p1 p2: Prog)
    | Case (B: ucom) (q: qubit) (m: measurement_outcome) (body: Prog)
    | While (B: ucom) (q: qubit) (body: Prog)
(*Should M be any unitary or only positive hermitian? and is M implicitly applied to the whole state prior to measurement*)


(* For operational semantics ∫😊🤩😶‍🌫️🙃😱👽👻🦊🐭🦧🎆🎈🎆🎇✨🎉🎊 *)

Inductive QECV_Lang := 
    | Skip
    | InitializeToZero (q: qubit)
    | UnitaryTransform (U: ucom) (q: qubit)
    | InitializeStabilizer (s: stabilizer) (s_e_u: ???)
    | Seq (p1 p2: Prog)
    | Case (B: ucom) (q: qubit) (∫ : InitializeStabilizer) (m: measurement_outcome) (body: Prog)
    | While (B: ucom) (q: qubit) (body: Prog)
Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| stepQubitAssign     : forall v x e,
                     step (v, Assign x e) (set_var v x (eval_expr e v), Skip)
| stepStabilizerAssign     : forall v x e,
                     step (v, Assign x e) (set_var v x (eval_expr e v), Skip)

| stepSeqLeft    : forall v c1 c2 v' c1', 
                     step (v, c1) (v', c1') ->
                     step (v, Seq c1 c2) (v', Seq c1' c2)
| stepSeqRight   : forall v c2,
                     step (v, Seq Skip c2) (v, c2)
| stepIfTrue     : forall v e then_ else_,
                     eval_expr e v <> 0 ->
                     step (v, If e then_ else_) (v, then_)
| stepIfFalse    : forall v e then_ else_,
                     eval_expr e v = 0 ->
                     step (v, If e then_ else_) (v, else_)
| stepWhileTrue  : forall v e body,
                     eval_expr e v <> 0 ->
                     step (v, While e body) (v, Seq body (While e body))
| stepWhileFalse : forall v e body,
                     eval_expr e v = 0 ->
                     step (v, While e body) (v, Skip).

Inductive stepStar : valuation * cmd -> valuation * cmd -> Prop :=
| stepStarRefl : forall v c, stepStar (v, c) (v, c)
| stepStarOnce : forall v1 c1 v2 c2 v3 c3,
                   step (v1, c1) (v2, c2) ->
                   stepStar (v2, c2) (v3, c3) ->
                   stepStar (v1, c1) (v3, c3).


*)


