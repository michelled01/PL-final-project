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

(* Definition apply_stabilizer (s : nqubits n) (ψ : Vector (2^n)) : (Vector (2^n)) :=
  (* Apply each Pauli operator in s to |ψ⟩ *)
  List.fold_right (fun p ψ' => apply_Pauli p ψ') ψ (Vector.to_list s). *)
Definition stabilizer (n dim: nat) (ψ : Vector (2^n)) (A: Square (2^n)) : Prop :=
    A × ψ = ψ.

(*  by Lemma 4.1 and Proposition 4.2, introduce arith-
metic expressions of stabilizers  *)

(* formulate the assertion language QECV-Assn  *)

(* add Lemma 4.3  *)