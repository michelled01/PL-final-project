Require Import QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.GenMatrix.
Require Export SQIR.UnitarySem.
Require Import QuantumLib.Matrix.

Local Open Scope ucom.


Definition qubit (n : nat) :=  Vector (2^n)

Inductive Pauli := I | σx | σy | σz.

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

Inductive stabilizer_value := (s: stabilizer) | ± s | ±i * s | (∫: stabilizer_variable)  

Inductive Prog :=
    | Skip
    | InitializeToZero (q: qubit)
    | UnitaryTransform (U: ucom) (q: qubit)
    | Seq (p1 p2: Prog)
    | Case (M: observable) (q: qubit) (m: measurement_outcome) (body: Prog)
    | While (B: ucom) (q: qubit) (body: Prog)
(*Should M be any unitary or only positive hermitian? and is M implicitly applied to the whole state prior to measurement*)


(* For operational semantics ∫😊🤩😶‍🌫️🙃😱👽👻🦊🐭🦧🎆🎈🎆🎇✨🎉🎊 *)

Inductive QEC_Condition :=
    | (M: observable) (∫ : InitializeStabilizer) (q: qubit).

Inductive QECV_Lang := 
    | Skip
    | InitializeToZero (q: qubit)
    | UnitaryTransform (U: ucom) (q: qubit)
    | InitializeStabilizer (s: stabilizer_var) (s_e_u: stabilizer_value)
    | Seq (p1 p2: QECV_Lang)
    | If (condition: QEC_Condition) (cthen: QECV_Lang) (celse: QECV_Lang)
    | While (condition: QEC_Condition) (body: QECV_Lang)

//TODO: import Seq

(*
And here's the "almost correct" definition of substitution we used in lecture.
It's "almost correct" because it does not correctly perform capture-avoiding
substitution. It's therefore correct *only on closed terms*. Note, though, that
it does correctly deal with the other substitution issue we saw in lecture by
checking the binder in the [Abs x t'] case before recursing.

Fixpoint subst (t: term) (from: var) (to: term) : term :=
  match t with
  | Var x => if var_eq from x then to else t
  | Abs x t' => if var_eq from x then t else Abs x (subst t' from to)
  | App t1 t2 => App (subst t1 from to) (subst t2 from to)
  end.
===========================================================================
Definition var := string.

Definition var_eq : forall (v1 v2 : var), {v1 = v2} + {v1 <> v2} := string_dec.

Definition var_map := var -> stabilizer.

(* Update a variable map with a new mapping *)
Definition set_map (m : var_map) (var : var) (value : nat) : var_map :=
    fun v => if var_eq var v then value else m v.
=============================================================================
Definition valuation := list (var * nat).
Definition set_var (v: valuation) (x: var) (n: nat) : valuation :=
    cons (x, n) v.

To look up the value of a variable, we walk down the list until we find the first matching variable
name. Unlike in lecture, our [lookup] won't be returning an [option] type, and we will just declare
that undefined variables have value 0, as we did in HW1.

Fixpoint lookup (v: valuation) (x: var) : option (stabilizer) :=
  match v with
  | nil => None
  | cons (y, n) v' => if var_eq x y then (Some n) else lookup v' x
  end.
*)

Definition stabilizer_var := string.

Definition stabilizer_eq : forall (v1 v2 : var), {v1 = v2} + {v1 <> v2} := string_dec.

Definition stabilizer_map := list (stabilizer_var * stabilizer_value).

Definition empty_stabilizer_map: stabilizer_map := nil.

Definition set_stabilizer (s: stabilizer_var) (v: stabilizer_value) (m: stabilizer_map): stabilizer_map :=
    cons (s, v) m

Definition lookup_stabilizer (s: stabilizer_var) (m: stabilizer_map): option stabilizer_value :=
    match m with
    | nil => None
    | cons (s', v) m' =>
        if stabilizer_eq s s'
        then Some v
        else lookup_stabilizer s m'
    end.

Definition qubit_eq : forall (v1 v2 : qubit), {v1 = v2} + {v1 <> v2} := string_dec.

Notation E := (0, {})
Notation c := 1 | -1 | i | -i

Inductive stabilizer_expr :=
| StabilizerConst stabilizer_value
| StabilizerVar stabilizer_var

Inductive step_stabilizer : stabilizer_expr * stabilizer_map -> stabilizer_value :=
| StabilizerExprConst : forall c s σ, 
                        step_stabilizer (StabilizerConst (dot c s), σ) (dot c s)
| StabilizerExprVar   : forall ∫ σ, 
                        step_stabilizer (± StabilizerVar ∫, σ) (± lookup_stabilizer ∫ σ).

Inductive step : cmd * stabilizer_map -> cmd * stabilizer_map :=
| Skip              : forall ρ σ, 
                      step (skip, (ρ σ)) (E, (ρ σ))
| Initialization    : forall q ρ σ,
                      step (set_qubit q ∣0⟩ q, (ρ σ)) (E, (trace q ρ) σ)
| Unitary           : forall q ρ σ,
                      step (set_qubit q U∣0⟩ q, (ρ σ)) (E, U ρ(transpose U), σ)
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
                      M_0 = (I - ∫)/2
                      -> step((if (probability_of_outcome (set_qubit q ∫ q) ∣1⟩) then Prog1 else Prog0), (ρ σ))
                              (Prog0, (M_0 ρ(transpose M_0), set_stabilizer ∫ (-σ ∫) σ))
| If_plus1          : forall ρ σ ∫ q Prog0 Prog1,
                      M_1 = (I + ∫)/2
                      -> step((if (probability_of_outcome (set_qubit q ∫ q) ∣0⟩) then Prog1 else Prog0), (ρ σ))
                              (Prog1, (M_1 ρ(transpose M_1), σ))
| While_minus1      : forall ρ σ ∫ q_prime Prog0 Prog1,
                      M_0 = (I - ∫)/2
                      -> step((while (probability_of_outcome (set_qubit q ∫ q) ∣1⟩) do Prog1), (ρ σ))
                      (Prog1, (M_1 ρ(transpose M_1), σ))
| While_plus1


(*

Fail Fixpoint eval_cmd (c: cmd) (v: valuation): valuation :=
    match c with
    | Skip => v
    | Assign x e => set_var v x (eval_expr e v)
    | Seq c1 c2 => eval_cmd c2 (eval_cmd c1 v)
    | If e cthen celse => if Nat.eq_dec (eval_expr e v) 0 then eval_cmd celse v else eval_cmd cthen v
    | While e c1 => eval_cmd c (if Nat.eq_dec (eval_expr e v) 0 then eval_cmd c1 v else v)
end.

Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| stepQubitAssign     : 
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


