module

public import TypeTheory.Untyped.Lambda.LocallyNameless.Basic

namespace Term

variable [DecidableEq V] [Infinite V]

public section

def rename (t : Term V) (x y : V) : Term V :=
  match t with
  | fvar z =>
    if z = x then fvar y
    else t
  | bvar i => bvar i
  | app t0 t1 => app (t0.rename x y) (t1.rename x y)
  | abs t => abs (t.rename x y)

@[simp, grind =]
lemma rename_fvar_eq (x y : V) : (fvar x).rename x y = fvar y := by simp!
@[simp, grind =]
lemma rename_fvar_neq (x y z : V) (h_neq : z ≠ x) : (fvar z).rename x y = fvar z := by rw [rename, if_neg (by trivial)]
@[simp, grind =]
lemma rename_bvar (i : Nat) (x y : V) : (bvar i).rename x y = bvar i := by simp!
@[simp, grind =]
lemma rename_app (t0 t1 : Term V) (x y : V) : (app t0 t1).rename x y = app (t0.rename x y) (t1.rename x y) := by simp!
@[simp, grind =]
lemma rename_abs (t : Term V) (x y : V) : (abs t).rename x y = abs (t.rename x y) := by simp!

private lemma rename_openₖ_eq_openₖ_rename (t : Term V) (hxz : x ≠ z) : (t.rename x y).openₖ k z = (t.openₖ k z).rename x y := by
  induction t generalizing k x y z
  any_goals grind
  case fvar w => by_cases h : w = x <;> grind

lemma rename_open_eq_open_rename (t : Term V) (hxz : x ≠ z) : (t.rename x y).open' z = (t.open' z).rename x y := by
  grind [rename_openₖ_eq_openₖ_rename]

lemma openₖ_rename_eq_openₖ (t : Term V) (h_fresh : x # t) : (t.openₖ k x).rename x y = t.openₖ k y := by
  induction t generalizing x y k
  all_goals grind

lemma open_rename_eq_open (t : Term V) (h_fresh : x # t) : (t.open' x).rename x y = t.open' y := by grind [openₖ_rename_eq_openₖ]

end

end Term

