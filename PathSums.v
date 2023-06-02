Require Import Reals.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Export QuantumLib.Complex.

Declare Scope psum.
Local Open Scope psum.

Local Open Scope C.
Local Close Scope R.

Local Coercion Nat.b2n : bool >-> nat.
Local Coercion INR     : nat >-> R.

Definition bv (n : nat) := list bool. 
Definition wf_bv {n} (v : bv n) : Prop := length v = n.
Definition get_bv (i : nat) (l : list bool) := nth i l false.

(* Replaces element with index `i` in list `l` with `v` *)
Fixpoint replace {A : Type} (l : list A) (i : nat) (v : A) := 
  match l with 
  | [] => []
  | a :: l1 => match i with 
               |    0 => v :: l1 
               | S i1 => a :: replace l1 i1 v 
               end 
  end.

(* Gets the elements `i` through `i + j` (exclusive in upper range) of list `l`.
It gets `j` elements starting from index `i`. *)
Definition take {A : Type} (l : list A) (i j : nat) : list A := firstn j (skipn i l).
Example take_last_two_elements_test : take [1 ; 2 ; 3 ; 4] 2 2 = [3 ; 4].
Proof. compute; reflexivity. Qed.

(* Phase polynomial *)
Definition phase_poly (m dim : nat) := bv dim -> bv m -> C.
(* input variable x -> path variables y -> complex number *)

(* Output bitvector *)
Definition output_bv (dim : nat) := bv dim -> bv dim -> bv dim.
(* input variable x -> path variables y -> complex number *)

(* Path sum *)
Inductive pscom (P : nat -> Set) (dim : nat) : Set :=
  | pseq : pscom P dim -> pscom P dim -> pscom P dim (* path sum -> path sum -> path sum *)
  | papp1 : P 1%nat -> nat -> pscom P dim (* base path sum -> index -> path sum *)
  | papp2 : P 2%nat -> nat -> nat -> pscom P dim. (* base path sum -> index -> index -> path sum *)

(* Set the dimension argument to be implicit. *)
Arguments pseq {P dim}.
Arguments papp1 {P dim}.
Arguments papp2 {P dim}.

Notation "p1 , p2 " := (pseq p1 p2) (at level 50) : psum.

(* Phase -> Output -> Path sum *)
Inductive base_path_sum : nat -> Set :=
  | psum_1 m : phase_poly m 1 -> output_bv 1 -> base_path_sum 1
  | psum_2 m : phase_poly m 2 -> output_bv 2 -> base_path_sum 2.
  (* psum {dim} range : phase polynomial -> output bitvector -> path sum *)

Inductive psum : nat -> Set :=
  | psum_n dim m : phase_poly m dim -> output_bv dim -> psum dim.

Definition base_psum := pscom base_path_sum.

(* Our gate set *)
Definition P_I              := psum_1 0 (fun x y => C1) (fun x y => x).
Definition P_H              := psum_1 1 (fun x y => (get_bv 0 x * get_bv 0 y) / 2) (fun x y => [get_bv 0 y]).
Definition P_Rk (k : nat)   := psum_1 0 (fun x y => (get_bv 0 x) / (2 ^ k)) (fun x y => x).
Definition P_Rkdg (k : nat) := psum_1 0 (fun x y => - (get_bv 0 x) / (2 ^ k)) (fun x y => x).
Definition P_CX             := psum_2 0 (fun x y => C1) (fun x y => [get_bv 0 x ; get_bv 0 x && get_bv 1 x]).

Definition I {dim} (i : nat) : base_psum dim := papp1 P_I i.
Definition H {dim} (i : nat) : base_psum dim := papp1 P_H i.
Definition Rk {dim} (k i : nat) : base_psum dim := papp1 (P_Rk k) i.
Definition Rkdg {dim} (k i : nat) : base_psum dim := papp1 (P_Rkdg k) i.
Definition CX {dim} (i j : nat) : base_psum dim := papp2 P_CX i j.

Definition T {dim} (n : nat) : base_psum dim := Rk 3 n.
Definition Tdg {dim} (n : nat) : base_psum dim := Rkdg 3 n.
Definition CZ {dim} (n m : nat) : base_psum dim := H n, CX n m, H n.
Definition SWAP {dim} (n m : nat) : base_psum dim := CX n m, CX m n, CX n m.

Definition CCX {dim} a b c : base_psum dim :=
  H c, CX b c, Tdg c, CX a c, 
  T c, CX b c, Tdg c, CX a c,
  CX a b, Tdg b, CX a b,
  T a, T b, T c, H c.

(* Convert base_psum into psum *)

(* Pad one-dimensional output bitvector function into n-dimensional *)
Definition pad_out_one_dim (dim i : nat) (out : output_bv 1) : output_bv dim :=
  fun x y => replace x i (get_bv 0 (out [get_bv i x] y)).

Example list_of_length_2 : forall (a : list bool),
  length a = 2 -> exists (b c : bool), a = [b ; c].
Proof.
  intros a H.
  destruct a as [| b [| c ]] eqn:E.
  - simpl in H; inversion H. (* Case: a = [] *)
  - simpl in H; inversion H. (* Case: a = [b] *)
  - (* Case: a = [b; c] *)
    exists b, c. 
    simpl in H; inversion H. 
    assert (l = nil).
    apply length_zero_iff_nil; apply H1.
    rewrite H0; reflexivity.
Qed.

Example pad_hadamard_output : forall (a : bv 2) (b : bv 1), wf_bv a ->
  (pad_out_one_dim 2 1 (fun x y => [get_bv 0 y])) a b = (fun x y => [ get_bv 0 x ; get_bv 0 y ]) a b.
Proof.
  intros.
  unfold pad_out_one_dim; unfold wf_bv in H0.
  replace (get_bv 0 [get_bv 0 b]) with (get_bv 0 b) by easy.
  unfold bv in a, b.
  apply list_of_length_2 in H0.
  destruct H0 as [c [d H0]]; rewrite H0.
  compute; reflexivity.
Qed.

(* Pad one-dimensional path-sum into n-dimensional path-sum *)
Definition pad_one_path_sum (dim i : nat) (P : base_path_sum 1) : psum dim :=
  match P with
  | psum_1 m phase out => psum_n dim m phase (pad_out_one_dim dim i out)
  end.

(* Pad two-dimensional output bitvector function into n-dimensional *)
Definition pad_out_two_dim (dim i j : nat) (out : output_bv 2) : output_bv dim :=
  (fun x y => replace (replace x i (get_bv 0 (out [get_bv i x ; get_bv j x] y))) 
                      j (get_bv 1 (out [get_bv i x ; get_bv j x] y))).

(* Pad two-dimensional path-sum into n-dimensional path-sum *)
Definition pad_two_path_sum (dim i j : nat) (P : base_path_sum 2) : psum dim :=
  match P with
  | psum_2 m phase out => psum_n dim m phase (pad_out_two_dim dim i j out)
  end.

Definition composed_poly {dim m m'} (phase : phase_poly m dim) (phase' : phase_poly m' dim) (out : output_bv dim) :=
  fun x y => phase x y + phase' (out x y) (take y m m').

Definition composed_out {dim} (out : output_bv dim) (out' : output_bv dim) :=
  fun x y => out' (out x y) y.

Definition compose_path_sum {dim : nat} (p1 p2 : psum dim) :=
  match p1 with 
  | psum_n dim m phase out => match p2 with
                              | psum_n dim m' phase' out' => psum_n dim (m + m')
                                                                        (composed_poly phase phase' out) 
                                                                        (composed_out out out')
                              end
  end.
Infix "∘" := compose_path_sum : psum.

Fixpoint path_sum_simplify {dim : nat} (p : base_psum dim) : psum dim :=
  match p with 
  | p1 , p2     => (path_sum_simplify p2) ∘ (path_sum_simplify p1)
  | papp1 P i   => pad_one_path_sum dim i P
  | papp2 P i j => pad_two_path_sum dim i j P
  end.

(* Well-typedness *)
Inductive psc_well_typed {P dim} : pscom P dim -> Prop :=
  | WT_pseq : forall p1 p2, psc_well_typed p1 -> psc_well_typed p2 -> psc_well_typed (p1, p2)
  | WT_pseq1 : forall p n, n < dim -> psc_well_typed (papp1 p n)
  | WT_pseq2 : forall p m n, n < dim -> m < dim -> n <> m -> psc_well_typed (papp2 p n m).

(* Well-typed path sums have dim > 0 *)
Lemma psc_well_typed_implies_dim_nonzero : forall {P dim} (p : pscom P dim),
  psc_well_typed p -> dim > 0.
Proof.
  intros P dim p WT.
  induction WT; try apply (Nat.lt_lt_0 n); assumption.
Qed.

(* Boolean version of well typedness *)
Fixpoint psc_well_typed_b {P dim} (p : pscom P dim) : bool :=
  match p with 
  | p1, p2 => psc_well_typed_b p1 && psc_well_typed_b p2
  | papp1 _ n => n <? dim
  | papp2 _ m n => (m <? dim) && (n <? dim) && (negb (m =? n))
  end.

Lemma psc_well_typed_b_equiv : forall {P dim} (p : pscom P dim),
  psc_well_typed_b p = true <-> psc_well_typed p.
Proof.
  intros P dim p. split; intros H.
  - induction p; constructor;
    simpl in H;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H as [? ?]
    | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
    | H : negb (_ =? _) = true |- _ => apply Bool.negb_true_iff in H; apply Nat.eqb_neq in H
    end;
    try apply IHp1;
    try apply IHp2;
    assumption. 
  - induction H; subst; simpl;
    repeat match goal with
    | |- (_ && _)%bool = true => apply Bool.andb_true_iff; split
    | |- (_ <? _) = true => apply Nat.ltb_lt
    | |- negb (_ =? _) = true => apply Bool.negb_true_iff; apply Nat.eqb_neq
    end;
    try apply IHpsc_well_typed1;
    try apply IHpsc_well_typed2;
    assumption.
  Qed.