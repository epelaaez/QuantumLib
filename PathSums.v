Require Import Reals.
Require Import Psatz.
Require Export QuantumLib.Complex.
Require Import List.
Import ListNotations.

(*
TODO: 
- [ ] Figure out better notation to distinguish from unitary semantics.
- [x] Define path-sum inductive semantics
- [ ] Define function equivalent to uc_eval that puts the information in the sum/exponent form
- [ ] Prove compose (both in parallel and in sequence) lemmas using path-sum semantics
- [ ] Define a standard basis in path-sum (e.g., CNOT, SWAP, ID, Ph(n), Rz(n), H)
- [ ] Prove basic equivalences (e.g., SWAP(a,b) = SWAP(b,a) =  CNOT(a, b); CNOT(b, a); CNOT(a, b))
*)

Local Open Scope C_scope.
Local Open Scope R_scope.

Declare Scope psum_scope.
Delimit Scope psum_scope with psum.
Local Open Scope psum.

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

Inductive pscom (P : nat -> Set) (width : nat) : Set :=
    | pseq : pscom P width -> pscom P width -> pscom P width (* path sum -> path sum -> path sum *)
    | papp1 : P 1%nat -> nat -> pscom P width (* path sum operator -> index -> path sum *)
    | papp2 : P 2%nat -> nat -> nat -> pscom P width. (* path sum -> index -> index -> path sum *)

(* Set the dimension argument to be implicit. *)
Arguments pseq {P width}.
Arguments papp1 {P width}.
Arguments papp2 {P width}.

Notation "p1 , p2 " := (pseq p1 p2) (at level 50) : psum_scope.

(* Functions we can call at each iteration of sum to get output ket and phase polynomial *)
Definition output_bv (width : nat) := nat -> bv width -> bv width.
Definition phase_poly (width : nat) := nat -> bv width -> C.
(* index -> variable bitvector -> output ket/phase polynomial *)

(* Phase -> Output -> Path sum *)
Inductive base_path_sum : nat -> Set :=
    | psum_1 : nat -> phase_poly 1 -> output_bv 1 -> base_path_sum 1
    | psum_2 : nat -> phase_poly 2 -> output_bv 2 -> base_path_sum 2.
    (* range -> phase polynomial -> bitvector -> path sum *)

Definition base_psum := pscom base_path_sum.

(* Clifford + T and Pauli gates *)
Definition P_I := psum_1 0 (fun _ _ => 1) (fun _ x => x).
Definition P_X := psum_1 0 (fun _ _ => 1) (fun _ x => [ (1 - x[0])%nat ]).
Definition P_H := psum_1 1 (fun i x => (-1) ^ (x[0] * i)) (fun i _ => [ i ]).
Definition P_S := psum_1 0 (fun _ x => Cexp (INR x[0] * (PI / 2))) (fun _ x => x).
Definition P_Sdg := psum_1 0 (fun _ x => Copp(Cexp (INR x[0] * (PI / 2)))) (fun _ x => x).
Definition P_T := psum_1 0 (fun _ x => Cexp (INR x[0] * (PI / 4))) (fun _ x => x).
Definition P_CX := psum_2 0 (fun _ _ => 1) (fun _ x => [ x[0] ; ((1 - x[0]) * x[1] + x[0] * (1 - x[1]))%nat]).

Definition I {width} (n : nat) : base_psum width := papp1 P_I n.
Definition X {width} (n : nat) : base_psum width := papp1 P_X n.
Definition H {width} (n : nat) : base_psum width := papp1 P_H n.
Definition S {width} (n : nat) : base_psum width := papp1 P_S n.
Definition Sdg {width} (n : nat) : base_psum width := papp1 P_Sdg n.
Definition T {width} (n : nat) : base_psum width := papp1 P_T n.
Definition CX {width} (n m : nat) : base_psum width := papp2 P_CX n m.

Definition W {width} (n : nat) : base_psum width := H n, S n.
Definition V {width} (n : nat) : base_psum width := Sdg n, H n.
Definition Y {width} (n : nat) : base_psum width := W n, X n, V n.
Definition Z {width} (n : nat) : base_psum width := W n, Y n, V n.

(* From https://arxiv.org/pdf/2003.05841.pdf 
Definition P_Ph (n : nat) (x : bv 1) := psum_1 (Cexp ((2 * PI) / (2 ^ n))) x.
Definition P_Rz (n : nat) (x : bv 1) := psum_1 (Cexp (((-1 ^ (1 - x[0]))) * (2 * PI) / (2 ^ n))) x.
*)

Local Close Scope C_scope.
Local Close Scope R_scope.

(* Define well-typedness *)
Inductive pscom_well_typed {P width} : pscom P width -> Prop :=
    | WT_pseq : forall p1 p2, pscom_well_typed p1 -> pscom_well_typed p2 -> pscom_well_typed (p1, p2)
    | WT_pseq1 : forall p n, n < width -> pscom_well_typed (papp1 p n)
    | WT_pseq2 : forall p m n, n < width -> m < width -> n <> m -> pscom_well_typed (papp2 p n m).

(* Well-typed path sums have width > 0 *)
Lemma pscom_well_typed_implies_width_nonzero : forall {P width} (p : pscom P width),
    pscom_well_typed p -> width > 0.
Proof.
    intros P width p WT.
    induction WT; try apply (Nat.lt_lt_0 n); assumption.
Qed.

(* Define pseq and prove semantics of Y, Z *)