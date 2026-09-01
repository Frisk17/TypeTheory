module

public import TypeTheory.Untyped.Lambda.LocallyNameless.Basic
public import TypeTheory.Untyped.Lambda.LocallyNameless.LC

namespace Term

public section

variable [DecidableEq V] [Infinite V]

def subst (t u : Term V) (x : V) : Term V :=
  match t with
  | fvar y =>
    if x = y then u else t
  | bvar _ => t
  | app t0 t1 => app (t0.subst u x) (t1.subst u x)
  | abs t => abs (t.subst u x)

notation:60 "[" x:61 " ⟶ " u:60 "] " t:60 => subst t u x

@[simp, grind =]
lemma subst_fvar_eq (x : V) : [x ⟶ u] (fvar x) = u := by simp!
@[simp, grind =]
lemma subst_fvar_neq (x y : V) (hxy : x ≠ y) : [x ⟶ u] (fvar y) = fvar y := by simp! [*]
@[simp, grind =]
lemma subst_bvar : [x ⟶ u] (bvar i : Term V) = bvar i := by simp!
@[simp, grind =]
lemma subst_app (t0 t1 : Term V) : [x ⟶ u] (app t0 t1) = app ([x ⟶ u] t0) ([x ⟶ u] t1) := by simp!
@[simp, grind =]
lemma subst_abs (t : Term V) : [x ⟶ u] (abs t) = abs ([x ⟶ u] t) := by simp!

lemma subst_openₖ_var
  (x y : V) (hyx : y ≠ x) (h_lc : u.LC) :
    ([x ⟶ u] t).openₖ k y = [x ⟶ u] t.openₖ k y := by
  induction t generalizing k
  any_goals grind
  case fvar z => by_cases hzx : z = x <;> grind

lemma subst_open_var
  (x y : V) (hyx : y ≠ x) (h_lc : u.LC) :
    ([x ⟶ u] t).open' y = [x ⟶ u] t.open' y := by
  rw [open']; apply subst_openₖ_var x y hyx h_lc

lemma subst_closeₖ_var
  (x y : V) (hyx : y ≠ x) (h_fresh : y # u) :
    [x ⟶ u] (t.closeₖ y k) = ([x ⟶ u] t).closeₖ y k := by
  induction t generalizing k
  any_goals grind
  case fvar z =>
    by_cases hzx : z = x
    all_goals grind

lemma subst_close_var
  (x y : V) (hyx : y ≠ x) (h_fresh : y # u) :
    [x ⟶ u] (t.close y) = ([x ⟶ u] t).close y := by
  rw [close]; apply subst_closeₖ_var x y hyx h_fresh

lemma lc_of_subst_lc (x : V) (ht : t.LC) (hu : u.LC) : ([ x ⟶ u ] t).LC := by
  generalize hn : SizeOf.sizeOf t = n
  induction n using Nat.strong_induction_on generalizing t
  case h n hi =>
    cases t
    any_goals grind
    case fvar y => by_cases hxy : x = y <;> grind
    case abs t =>
      simp
      rw [body_iff_lc_abs] at ht
      apply lc_abs {x}
      intro y hy
      rw [subst_open_var _ _ (by grind) hu]
      apply open_var_lc (x := y) at ht
      apply @hi (SizeOf.sizeOf (t.open' y)) (by grind) (t.open' y) ht (by trivial)

lemma body_of_subst_body (x : V) (ht : t.Body) (hu : u.LC) : ([x ⟶ u] t).Body := by
  rw [←body_iff_lc_abs]
  apply lc_abs {x}
  intro y hy
  rw [subst_open_var _ _ (by grind) hu]
  apply open_var_lc at ht
  apply lc_of_subst_lc _ ht hu

@[simp, grind =]
lemma subst_fresh {t : Term V} (h_fresh : x # t) : [x ⟶ u] t = t := by
  induction t
  all_goals grind

lemma subst_commute {e f t : Term V}
  (hxy : x ≠ y)
  (h_fresh : y # e) :
    [x ⟶ e] [y ⟶ f] t = [y ⟶ [x ⟶ e] f] [x ⟶ e] t := by
  induction t
  all_goals grind

end

end Term

