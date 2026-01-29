From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf Require Import lang notation types tactics.

(** Exercise 3 (LN Exercise 22): Universal Fun *)

Definition Id: val :=
  (Λ, (λ: "x", "x")).
Definition Id_type : type :=
  (∀: #0 → #0).
Lemma Id_typed :
  TY 0; ∅ ⊢ Id : Id_type.
Proof. solve_typing. Qed.

Definition fun_comp : val :=
  (Λ, Λ, Λ, (λ: "f" "g" "x", (App "g" (App "f" "x")))).
Definition fun_comp_type : type :=
  (∀: ∀: ∀: ((#2 → #1) → (#1 → #0) → (#2 → #0))).
Lemma fun_comp_typed :
  TY 0; ∅ ⊢ fun_comp : fun_comp_type.
Proof. 
  (* should be solved by solve_typing. *)
  unfold fun_comp. unfold fun_comp_type.
  solve_typing.
Qed.

Definition swap_args : val :=
  (Λ, Λ, Λ, (λ: "f" "a" "b", ("f" "b" "a"))).
Definition swap_args_type : type :=
  (∀: ∀: ∀: (#2 → #1 → #0) → #1 → #2 → #0).
Lemma swap_args_typed :
  TY 0; ∅ ⊢ swap_args : swap_args_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
  solve_typing.
Qed.


Definition lift_prod : val :=
  (Λ, Λ, Λ, Λ, (λ: "f" "g" "p", ("f" (Fst "p") , "g" (Snd "p")))).
Definition lift_prod_type : type :=
  (∀: ∀: ∀: ∀: (#3 → #2) → (#1 → #0) → (#3 × #1) → (#2 × #0)).
Lemma lift_prod_typed :
  TY 0; ∅ ⊢ lift_prod : lift_prod_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
  solve_typing.
Qed.


Definition lift_sum : val :=
  (Λ, Λ, Λ, Λ, (λ: "f" "g" "p", (Case "p" (λ: "x", InjL ("f" "x")) 
    (λ: "x", InjR ("g" "x"))))).
Definition lift_sum_type : type :=
  (∀: ∀: ∀: ∀: (#3 → #2) → (#1 → #0) → (Sum #3 #1) → (Sum #2 #0)).
Lemma lift_sum_typed :
  TY 0; ∅ ⊢ lift_sum : lift_sum_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
  solve_typing.
Qed.


(** Exercise 5 (LN Exercise 18): Named to De Bruijn *)
Inductive ptype : Type :=
  | PTVar : string → ptype
  | PInt
  | PBool
  | PTForall : string → ptype → ptype
  | PTExists : string → ptype → ptype
  | PFun (A B : ptype).

Declare Scope PType_scope.
Delimit Scope PType_scope with pty.
Bind Scope PType_scope with ptype.
Coercion PTVar: string >-> ptype.
Infix "→" := PFun : PType_scope.
Notation "∀:  x , τ" :=
    (PTForall x τ%pty)
    (at level 100, τ at level 200) : PType_scope.
Notation "∃:  x , τ" :=
    (PTExists x τ%pty)
    (at level 100, τ at level 200) : PType_scope.

Fixpoint debruijn (m: gmap string nat) (A: ptype) : option type :=
  None (* FIXME *). 

(* Example *)
Goal debruijn ∅ (∀: "x", ∀: "y", "x" → "y")%pty = Some (∀: ∀: #1 → #0)%ty.
Proof.
  (* Should be solved by reflexivity. *)
  (* TODO: exercise *)
Admitted.


Goal debruijn ∅ (∀: "x", "x" → ∀: "y", "y")%pty = Some (∀: #0 → ∀: #0)%ty.
Proof.
  (* Should be solved by reflexivity. *)
  (* TODO: exercise *)
Admitted.


Goal debruijn ∅ (∀: "x", "x" → ∀: "y", "x")%pty = Some (∀: #0 → ∀: #1)%ty.
Proof.
  (* Should be solved by reflexivity. *)
  (* TODO: exercise *)
Admitted.


