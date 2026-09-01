module

import Mathlib.Tactic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.SDiff

public inductive Term (V : Type u) [DecidableEq V] [Infinite V] where
  | bvar (i : Nat) : Term V
  | fvar (x : V) : Term V
  | app (t0 t1 : Term V) : Term V
  | abs (t : Term V) : Term V
deriving Repr

namespace Term

public section

variable [DecidableEq V] [Infinite V]

def sizeOf (t : Term V) : Nat :=
  match t with
  | bvar _ => 0
  | fvar _ => 0
  | app t0 t1 => t0.sizeOf + t1.sizeOf + 1
  | abs t => t.sizeOf + 1

instance instSizeOf : SizeOf (Term V) where
  sizeOf := sizeOf

@[simp, grind =]
lemma sizeOf_bvar (i : Nat) : SizeOf.sizeOf (bvar i : Term V) = 0 := by rfl
@[simp, grind =]
lemma sizeOf_fvar (x : V) : SizeOf.sizeOf (fvar x) = 0 := by rfl
@[simp, grind =]
lemma sizeOf_app (t0 t1 : Term V) : SizeOf.sizeOf (app t0 t1) = (SizeOf.sizeOf t0) + (SizeOf.sizeOf t1) + 1 := by rfl
@[simp, grind =]
lemma sizeOf_abs (t : Term V) : SizeOf.sizeOf (abs t) = SizeOf.sizeOf t + 1 := by rfl

def openₖ (t : Term V) (k : Nat) (x : V) : Term V :=
  match t with
  | bvar j => if j = k then fvar x else t
  | app t0 t1 => app (t0.openₖ k x) (t1.openₖ k x)
  | abs t => abs <| t.openₖ (k + 1) x
  | _ => t

@[simp, grind =]
lemma openₖ_bvar_eq (k : Nat) (x : V) : (bvar k).openₖ k x = fvar x := by rw [openₖ, if_pos (by trivial)]
@[simp, grind =]
lemma openₖ_bvar_neq (j k : Nat) (h_neq : j ≠ k) (x : V) : (bvar j).openₖ k x = bvar j := by rw [openₖ, if_neg h_neq]
@[simp, grind =]
lemma openₖ_app (t0 t1 : Term V) (k : Nat) (x : V) : (app t0 t1).openₖ k x = app (t0.openₖ k x) (t1.openₖ k x) := by rw [openₖ]
@[simp, grind =]
lemma openₖ_abs (t : Term V) (k : Nat) (x : V) : (abs t).openₖ k x = abs (t.openₖ (k + 1) x) := by rw [openₖ]
@[simp, grind =]
lemma openₖ_fvar (k : Nat) (x y : V) : (fvar y).openₖ k x = fvar y := by simp!

lemma openₖ_size (t : Term V) (k : Nat) (x : V) : SizeOf.sizeOf (t.openₖ k x) = SizeOf.sizeOf t := by induction t generalizing k <;> grind

abbrev open' (t : Term V) (x : V) := t.openₖ 0 x

@[simp, grind =]
lemma open'_zero (x : V) : (bvar 0).open' x = fvar x := by rfl
@[simp, grind =]
lemma open'_var_ne_zero (j : Nat) (h_neq : j ≠ 0) (x : V) : (bvar j).open' x = bvar j := by grind
@[simp, grind =]
lemma open'_app (t0 t1 : Term V) (x : V) : (app t0 t1).open' x = app (t0.open' x) (t1.open' x) := by rfl
@[simp, grind =]
lemma open'_abs (t : Term V) (x : V) : (abs t).open' x = abs (t.openₖ 1 x) := by rfl
@[simp, grind =]
lemma open'_fvar (x y : V) : (fvar y).open' x = fvar y := by rfl

@[simp, grind =]
lemma open_size (t : Term V) (x : V) : SizeOf.sizeOf (t.open' x) = SizeOf.sizeOf t := by grind [openₖ_size]

def closeₖ (t : Term V) (x : V) (k : Nat) : Term V :=
  match t with
  | fvar y => if x = y then bvar k else t
  | app t0 t1 => app (t0.closeₖ x k) (t1.closeₖ x k)
  | abs t => abs <| t.closeₖ x (k + 1)
  | _ => t

@[simp, grind =]
lemma closeₖ_fvar_eq (x : V) (k : Nat) : (fvar x).closeₖ x k = bvar k := by rw [closeₖ, if_pos (by trivial)]
@[simp, grind =]
lemma closeₖ_fvar_neq (x y : V) (h_neq : x ≠ y) (k : Nat) : (fvar y).closeₖ x k = fvar y := by rw [closeₖ, if_neg h_neq]
@[simp, grind =]
lemma closeₖ_bvar (x : V) j k : (bvar j).closeₖ x k = bvar j := by simp!
@[simp, grind =]
lemma closeₖ_app (t0 t1 : Term V) x k : (app t0 t1).closeₖ x k = app (t0.closeₖ x k) (t1.closeₖ x k) := by rw [closeₖ]
@[simp, grind =]
lemma closeₖ_abs (t : Term V) (x : V) (k : Nat) : (abs t).closeₖ x k = abs (t.closeₖ x (k + 1)) := by rw [closeₖ]

abbrev close (t : Term V) (x : V) := t.closeₖ x 0

@[simp, grind =]
lemma close_fvar_eq (x : V) : (fvar x).close x = bvar 0 := by simp
@[simp, grind =]
lemma close_fvar_neq (x y : V) (h_neq : x ≠ y) : (fvar y).close x = fvar y := by grind
@[simp, grind =]
lemma close_bvar (x : V) j : (bvar j).close x = bvar j := by simp
@[simp, grind =]
lemma close_app (t0 t1 : Term V) x : (app t0 t1).close x = app (t0.close x) (t1.close x) := by simp
@[simp, grind =]
lemma close_abs (t : Term V) (x : V) : (abs t).close x = abs (t.closeₖ x 1) := by simp

def fvars (t : Term V) : Finset V :=
  match t with
  | bvar _ => {}
  | fvar x => {x}
  | app t0 t1 => t0.fvars ∪ t1.fvars
  | abs t => t.fvars

@[simp, grind =]
lemma fvars_bvar (i : Nat) : (bvar i : Term V).fvars = {} := by rw [fvars]
@[simp, grind =]
lemma fvars_fvar (x : V) : (fvar x).fvars = {x} := by rw [fvars]
@[simp, grind =]
lemma fvars_app (t0 t1 : Term V) : (app t0 t1).fvars = t0.fvars ∪ t1.fvars := by rw [fvars]
@[simp, grind =]
lemma fvars_abs (t : Term V) : (abs t).fvars = t.fvars := by rw [fvars]

lemma fvars_openₖ_subset_fvars (t : Term V) (x : V) : (t.openₖ k x).fvars ⊆ t.fvars ∪ {x} := by
  induction t generalizing k
  all_goals grind

lemma fvars_closeₖ_eq_fvars_diff (t : Term V) (x : V) : (t.closeₖ x k).fvars = t.fvars \ {x} := by
  induction t generalizing k
  any_goals grind
  case fvar y => by_cases hxy : x = y <;> grind

lemma fvars_close_eq_fvars_diff (t : Term V) (x : V) : (t.close x).fvars = t.fvars \ {x} := by grind [fvars_closeₖ_eq_fvars_diff]

abbrev fresh (x : V) (t : Term V) := x ∉ t.fvars
abbrev closed (t : Term V) := t.fvars = {}

scoped infix:70 " # " => fresh

@[grind .]
lemma fresh_close (x : V) (t : Term V) : x # (t.close x) := by
  grind [fvars_close_eq_fvars_diff]

lemma close_openₖ
  {t : Term V} {x : V} {k : Nat} (h_fresh : x # t) :
    (t.openₖ k x).closeₖ x k = t := by
  induction t generalizing k
  all_goals grind

lemma close_open (t : Term V) (x : V) (h_fresh : x # t) : (t.open' x).close x = t := by
  rw [open', close]; apply close_openₖ h_fresh

@[simp, grind =]
lemma fresh_closeₖ_eq_self {t : Term V} (h : x # t) : t.closeₖ x k = t := by
  induction t generalizing k
  all_goals grind

lemma open_extₖ (s t : Term V) (h : ∀ x, s.openₖ k x = t.openₖ k x) : s = t := by
  have inst : Infinite V := by assumption
  have x := inst.nonempty.some
  have h' := h x
  induction s generalizing t k with
  | bvar i =>
    cases t
    any_goals grind
    case fvar x =>
      have ⟨ y, hy ⟩ := Infinite.exists_notMem_finset {x}
      specialize h y
      grind
  | fvar y =>
    cases t
    any_goals grind
    case bvar i =>
      simp_all only [openₖ_fvar]
      have ⟨ z, hz ⟩ := Infinite.exists_notMem_finset {y}
      specialize h z
      grind
  | app t0 t1 ht0 ht1 =>
    cases t
    any_goals grind
    case app t0' t1' =>
      have h0 : ∀ x, t0.openₖ k x = t0'.openₖ k x := by
        intro x
        specialize h x
        simp_all
      have h1 : ∀ x, t1.openₖ k x = t1'.openₖ k x := by
        intro x
        specialize h x
        simp_all
      grind
  | abs s hs =>
    cases t
    any_goals grind
    case abs s' =>
      have hss' : ∀ x, s.openₖ (k + 1) x = s'.openₖ (k + 1) x := by
        intro x
        specialize h x
        simp_all
      grind

lemma open_ext (s t : Term V) (h : ∀ x, s.open' x = t.open' x) : s = t := by
  apply open_extₖ
  intro y
  apply (h y)

lemma openₖ_fvars_subset (t : Term V) : (t.openₖ k x).fvars ⊆ t.fvars ∪ {x} := by
  induction t generalizing k
  any_goals grind

lemma openₖ_fvars_superset (t : Term V) : (t.openₖ k x).fvars ⊇ t.fvars := by
  induction t generalizing k
  any_goals grind

@[grind .]
lemma open_fvars_subset (t : Term V) : (t.open' x).fvars ⊆ t.fvars ∪ {x} := by apply fvars_openₖ_subset_fvars

@[grind .]
lemma open_fvars_superset (t : Term V) : (t.open' x).fvars ⊇ t.fvars := by apply openₖ_fvars_superset

lemma open_fvars (t : Term V) : (t.open' x).fvars = t.fvars ∨ (t.open' x).fvars = t.fvars ∪ {x} := by
  have h_lb := open_fvars_superset (x := x) t
  have h_ub := open_fvars_subset (x := x) t
  by_cases h : (t.open' x).fvars = t.fvars ∨ (t.open' x).fvars = t.fvars ∪ {x}
  · exact h
  · grind

end

end Term

