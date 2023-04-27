Require Import Reals.
Require Import Psatz.
Require Export QuantumLib.Complex.
Require Import QuantumLib.Quantum.
Require Import List.
Import ListNotations.

(*
TODO: 
- [ ] Define path-sum inductive semantics
- [ ] Define function equivalent to uc_eval that puts the information in the sum/exponent form
- [ ] Prove compose (both in parallel and in sequence) lemmas using path-sum semantics
- [ ] Define a standard basis in path-sum (e.g., CNOT, SWAP, ID, Ph(n), Rz(n), H)
- [ ] Prove basic equivalences (e.g., SWAP(a,b) = SWAP(b,a) =  CNOT(a, b); CNOT(b, a); CNOT(a, b))
*)

Local Open Scope C_scope.
Local Open Scope R_scope.

Inductive pscom (P : nat -> Set) (width : nat) : Set :=
    | pseq : pscom P width -> pscom P width -> pscom P width.
    (*| pwidth1 : P 1%nat -> nat -> pscom P width
    | pwidth2 : P 2%nat -> nat -> nat -> pscom P width.
    Maybe include to use more similar semantics to the unitary? *)

Declare Scope psum_scope.
Delimit Scope psum_scope with psum.
Local Open Scope psum.

Notation "SEQ ( p1 , p2 )" := (pseq p1 p2) (at level 50) : psum_scope.

Definition bv (n : nat) := list nat. 
Definition get_bv {n : nat} (i : nat) (v : bv n) := nth i v O.
Notation " v [ i ]" := (get_bv i v) (at level 0).

Definition bv0 : bv 1 := [ O ].
Definition bv1 : bv 1 := [ S O ].

Definition bit (x : nat) : bv 1 := 
    match x with 
    | 0 => bv0
    | _ => bv1
    end.

(* Phase -> Output -> Path sum *)
Inductive base_path_sum : nat -> Set :=
    | psum_1 : C -> bv 1 -> base_path_sum 1
    | psum_2 : C -> bv 2 -> base_path_sum 2.

Definition base_psum := pscom base_path_sum.

Definition P_ID (x : bv 1) := psum_1 1 x.
Definition P_Ph (n : nat) (x : bv 1) := psum_1 (Cexp ((2 * PI) / (2 ^ n))) x.
Definition P_Rz (n : nat) (x : bv 1) := psum_1 (Cexp (((-1 ^ (1 - x[0]))) * (2 * PI) / (2 ^ n))) x.
Definition P_CX (x : bv 2) := psum_2 C1 ([ x[0] ; ((1 - x[0]) * x[1] + x[0] * (1 - x[1]))%nat]).