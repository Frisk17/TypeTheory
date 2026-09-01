module

public import TypeTheory.Untyped.Lambda.LocallyNameless.Basic
public import TypeTheory.Untyped.Lambda.LocallyNameless.Rename

public import Mathlib.Data.Fintype.EquivFin

namespace Term

public section

variable [Infinite V] [DecidableEq V]

inductive LC : Term V → Prop where
  | fvar (x : V) : LC (fvar x)
  | app (h0 : LC t0) (h1 : LC t1) : LC (app t0 t1)
  | abs (names : Finset V) (h : ∀ x ∉ names, LC (t.open' x)) : LC (abs t)

@[grind .]
lemma lc_fvar (x : V) : LC (fvar x) := LC.fvar x
@[grind .]
lemma lc_app (t0 t1 : Term V) (h0 : LC t0) (h1 : LC t1) : LC (app t0 t1) :=
  LC.app h0 h1
lemma lc_abs (names : Finset V) (h : ∀ x ∉ names, LC (t.open' x)) : LC (abs t) := LC.abs names h

@[grind →]
lemma lc₀_of_lc_app {t0 t1 : Term V} (h : (app t0 t1).LC) : t0.LC := by
  cases h; trivial
@[grind →]
lemma lc₁_of_lc_app {t0 t1 : Term V} (h : (app t0 t1).LC) : t1.LC := by
  cases h; trivial

structure Body (t : Term V) : Prop where
  lc : ∃ (names : Finset V), ∀ x ∉ names, LC (t.open' x)

lemma body_def (t : Term V) (names : Finset V) (h : ∀ x ∉ names, LC (t.open' x)) :
    t.Body := by apply Body.mk; use names

lemma body_iff_lc_abs (t : Term V) : (abs t).LC ↔ t.Body := by
  constructor
  · intro h
    cases h
    expose_names
    apply body_def _ names h
  · intro ⟨ names, h ⟩
    apply lc_abs names h

@[grind .]
lemma lc_rename_of_lc (t : Term V) (h : t.LC) : (t.rename x y).LC := by
  generalize hn : SizeOf.sizeOf t = n
  induction n using Nat.strong_induction_on generalizing t x y
  case h n hi =>
    cases t with
    | fvar z => by_cases hz : z = x <;> grind
    | bvar i => grind
    | app t0 t1 => cases h; grind
    | abs t =>
      cases h
      case abs names h =>
        rw [rename_abs]
        apply LC.abs (names ∪ {x})
        intro z hz
        have hxz : x ≠ z := by grind
        rw [rename_open_eq_open_rename t hxz]
        grind

lemma open_var_lc  (t : Term V) (h_body : t.Body) : (t.open' x).LC := by
  obtain ⟨ names, h ⟩ := h_body
  have ⟨ y, hy ⟩ := Infinite.exists_notMem_finset (names ∪ t.fvars)
  have hy' : y ∉ names := by grind
  have h_fresh : y # t := by grind
  clear hy
  specialize h y hy'
  rw [←open_rename_eq_open t h_fresh]
  apply lc_rename_of_lc
  exact h

lemma bvar_eq_zero_of_body (i : Nat) (h : (bvar i : Term V).Body) : i = 0 := by
  have x := (Infinite.nonempty V).some
  apply open_var_lc (x := x) at h
  by_cases hi : i = 0
  · exact hi
  · exfalso
    simp_all
    cases h

lemma body₀_of_body_app (t0 t1 : Term V) (h : (app t0 t1).Body) : t0.Body := by
  apply body_def (names := {})
  intro x _
  apply open_var_lc (x := x) at h
  simp at h
  cases h; grind

lemma body₁_of_body_app (t0 t1 : Term V) (h : (app t0 t1).Body) : t1.Body := by
  apply body_def (names := {})
  intro x _
  apply open_var_lc (x := x) at h
  simp at h
  cases h; grind

@[grind .]
lemma body_rename_of_body {t : Term V} (ht : t.Body) : (t.rename x y).Body := by
  rw [←body_iff_lc_abs] at *
  rw [←rename_abs]
  grind

inductive LCAt : Term V → ℕ → Prop where
  | bvar (i : Nat) (hi : i < k) : (bvar i).LCAt k
  | fvar (x : V) : (fvar x).LCAt k
  | app (t0 t1 : Term V) (h0 : t0.LCAt k) (h1 : t1.LCAt k) : (app t0 t1).LCAt k
  | abs (t : Term V) (h : t.LCAt (k + 1)) : (abs t).LCAt k

@[grind .]
lemma lc_at_bvar (i : Nat) (hi : i < k) : (bvar i : Term V).LCAt k := LCAt.bvar i hi
@[grind .]
lemma lc_at_fvar (x : V) : (fvar x).LCAt k := LCAt.fvar x
@[grind .]
lemma lc_at_app {t0 t1 : Term V} (h0 : t0.LCAt k) (h1 : t1.LCAt k) : (app t0 t1).LCAt k := LCAt.app t0 t1 h0 h1
@[grind .]
lemma lc_at_abs {t : Term V} (h : t.LCAt (k + 1)) : (abs t).LCAt k := LCAt.abs t h

@[grind →]
lemma lt_of_bvar_lc_at (h : (bvar i : Term V).LCAt k) : i < k := by
  cases h; trivial
@[grind →]
lemma lc_at₀_of_lc_at_app {t0 t1 : Term V} (h : (app t0 t1).LCAt k) : t0.LCAt k := by
  cases h; trivial
@[grind →]
lemma lc_at₁_of_lc_at_app {t0 t1 : Term V} (h : (app t0 t1).LCAt k) : t1.LCAt k := by
  cases h; trivial
@[grind →]
lemma lc_at_of_lc_at_abs {t : Term V} (h : (abs t).LCAt k) : t.LCAt (k + 1) := by
  cases h; trivial

lemma lc_at_lift_succ {t : Term V} (h : t.LCAt k) : t.LCAt (k + 1) := by
  induction h
  all_goals grind

lemma lc_at_lift_le {t : Term V} (h : t.LCAt j) (hjk : j ≤ k) : t.LCAt k := by
  induction k using Nat.strong_induction_on with
  | h k hi =>
    cases k
    any_goals grind
    case succ k =>
      by_cases hjk' : j = k + 1
      any_goals grind
      specialize hi k (by omega) (by omega)
      grind [lc_at_lift_succ]

lemma lc_at_openₖ_of_lc_at {t : Term V} (h : t.LCAt (k + 1)) : (t.openₖ k x).LCAt k := by
  induction t generalizing k with
  | bvar i => by_cases hik : i = k <;> grind
  | _ => grind

lemma lc_at_zero_open_of_lc_at_one {t : Term V} (h : t.LCAt 1) : (t.open' x).LCAt 0 := by grind [lc_at_openₖ_of_lc_at]

lemma lc_at_of_lc_at_openₖ {t : Term V} (h : ∀ x, (t.openₖ k x).LCAt k) : t.LCAt (k + 1) := by
  have inst : Infinite V := by assumption
  have x := inst.nonempty.some
  induction t generalizing k with
  | app t0 t1 ht0 ht1 =>
    have h0 : ∀ x, (t0.openₖ k x).LCAt k := by
      intro x
      specialize @h x
      grind [lc_at₀_of_lc_at_app]
    have h1 : ∀ x, (t1.openₖ k x).LCAt k := by
      intro x
      specialize @h x
      grind [lc_at₁_of_lc_at_app]
    grind
  | abs t ht =>
    apply lc_at_abs
    simp only [openₖ_abs] at h
    have h' : ∀ x, (t.openₖ (k + 1) x).LCAt (k + 1) := by grind
    grind
  | _ => specialize h x; grind

lemma lc_at_one_of_lc_at_open_zero {t : Term V} (h : ∀ x, (t.open' x).LCAt 0) : t.LCAt 1 := by
  rw [←Nat.zero_add 1]
  apply lc_at_of_lc_at_openₖ
  simp_all [open']

lemma lc_of_lc_at_zero {t : Term V} (h : t.LCAt 0) : t.LC := by
  generalize hn : SizeOf.sizeOf t = n
  induction n using Nat.strong_induction_on generalizing t with
  | h n hi =>
    cases t
    any_goals grind
    case abs t =>
      apply lc_at_of_lc_at_abs at h; rw [Nat.zero_add] at h
      apply lc_abs {}
      intro x hx
      apply @hi (SizeOf.sizeOf (t.open' x)) (by grind) (t.open' x) (lc_at_zero_open_of_lc_at_one h) (by trivial)

lemma lc_at_zero_of_lc {t : Term V} (h : t.LC) : t.LCAt 0 := by
  generalize hn : SizeOf.sizeOf t = n
  induction n using Nat.strong_induction_on generalizing t with
  | h n hi =>
    cases t
    any_goals grind
    case bvar => cases h
    case abs t =>
      rw [body_iff_lc_abs] at h
      apply lc_at_abs; rw [Nat.zero_add]; apply lc_at_one_of_lc_at_open_zero
      intro x
      apply open_var_lc (x := x) at h
      apply hi (SizeOf.sizeOf (t.open' x)) (by grind) h (by grind)

@[simp, grind =]
lemma lc_at_zero_iff_lc {t : Term V} : t.LCAt 0 ↔ t.LC := by
  grind [lc_at_zero_of_lc, lc_of_lc_at_zero]

lemma body_of_lc_at_one {t : Term V} (h : t.LCAt 1) : t.Body := by
  rw [←body_iff_lc_abs]
  apply lc_abs {}
  intro x _
  rw [←lc_at_zero_iff_lc]
  apply lc_at_zero_open_of_lc_at_one
  exact h

lemma lc_at_one_of_body {t : Term V} (h_body : t.Body) : t.LCAt 1 := by
  have h : ∀ (x : V), (t.open' x).LCAt 0 := by
    intro x
    apply open_var_lc (x := x) at h_body
    rw [←lc_at_zero_iff_lc] at h_body
    exact h_body
  apply lc_at_one_of_lc_at_open_zero h

@[simp, grind =]
lemma lc_at_one_iff_body {t : Term V} : t.LCAt 1 ↔ t.Body := by
  grind [lc_at_one_of_body, body_of_lc_at_one]

lemma lc_at_openₖ_eq_self {t : Term V} (h : t.LCAt j) : t.openₖ (j + k) x = t := by
  induction t generalizing j
  all_goals grind

@[simp, grind =]
lemma lc_openₖ_eq_self {t : Term V} (h : t.LC) : t.openₖ k x = t := by
  rw [←lc_at_zero_iff_lc] at h
  rw [←Nat.zero_add k]
  apply lc_at_openₖ_eq_self h

lemma open_close_varₖ {t : Term V} (h : t.LCAt k) : (t.closeₖ x k).openₖ k x = t := by
  induction t generalizing k
  all_goals grind

lemma open_close_var {t : Term V} (h : t.LC) : (t.close x).open' x = t := by
  rw [close, open']
  rw [←lc_at_zero_iff_lc] at h
  apply open_close_varₖ h

end

end Term

