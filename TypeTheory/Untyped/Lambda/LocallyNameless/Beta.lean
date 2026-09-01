module

public import TypeTheory.Untyped.Lambda.LocallyNameless.Basic
public import TypeTheory.Untyped.Lambda.LocallyNameless.LC
public import TypeTheory.Untyped.Lambda.LocallyNameless.Subst

namespace Term

public section

variable {V} [Infinite V] [DecidableEq V]

def openTermₖ (t : Term V) (k : Nat) (u : Term V) : Term V :=
  match t with
  | bvar i => if i = k then u else t
  | fvar _ => t
  | app t0 t1 => app (t0.openTermₖ k u) (t1.openTermₖ k u)
  | abs t => abs (t.openTermₖ (k + 1) u)

@[simp, grind =]
lemma openTermₖ_bvar_eq : (bvar k : Term V).openTermₖ k u = u := by simp!
@[simp, grind =]
lemma openTermₖ_bvar_neq (hik : i ≠ k) : (bvar i : Term V).openTermₖ k u = bvar i := by simp! [*]
@[simp, grind =]
lemma openTermₖ_fvar : (fvar x : Term V).openTermₖ k u = fvar x := by rfl
@[simp, grind =]
lemma openTermₖ_app {t0 t1 : Term V} : (app t0 t1).openTermₖ k u = app (t0.openTermₖ k u) (t1.openTermₖ k u) := by rfl
@[simp, grind =]
lemma openTermₖ_abs {t : Term V} : (abs t).openTermₖ k u = abs (t.openTermₖ (k + 1) u) := by rfl

abbrev openTerm (t : Term V) (u : Term V) : Term V := t.openTermₖ 0 u

infixl:60 " ^ " => openTerm

lemma openTermₖ_fvar_eq_openₖ {t : Term V} : t.openTermₖ k (fvar x) = t.openₖ k x := by
  induction t generalizing k
  all_goals grind

lemma openTerm_fvar_eq_open {t : Term V} : t ^ (fvar x) = t.open' x := by
  simp [openTermₖ_fvar_eq_openₖ]

lemma openTermₖ_fvars_superset (s t : Term V) : (s.openTermₖ k t).fvars ⊇ s.fvars := by
  induction s generalizing k
  all_goals grind

lemma openTermₖ_fvars_subset (s t : Term V) : (s.openTermₖ k t).fvars ⊆ s.fvars ∪ t.fvars := by
  induction s generalizing k
  all_goals grind

lemma openTerm_fvars_superset (s t : Term V) : (s ^ t).fvars ⊇ s.fvars := by
  apply openTermₖ_fvars_superset

lemma openTerm_fvars_subset (s t : Term V) : (s ^ t).fvars ⊆ s.fvars ∪ t.fvars := by apply openTermₖ_fvars_subset

lemma openTermₖ_fvars (s t : Term V) : (s.openTermₖ k t).fvars = s.fvars ∪ t.fvars ∨ (s.openTermₖ k t).fvars = s.fvars := by
  induction s generalizing k
  all_goals grind

lemma openTerm_fvars (s t : Term V) : (s ^ t).fvars = s.fvars ∪ t.fvars ∨ (s ^ t).fvars = s.fvars := by apply openTermₖ_fvars

lemma lc_at_of_openTermₖ_lc_at {t u : Term V} (ht : t.LCAt (k + 1)) (hu : u.LCAt k) : t.openTermₖ k u |>.LCAt k := by
  induction t generalizing k
  any_goals grind
  case abs t ht =>
    apply lc_at_lift_le (k := k + 1) (hjk := Nat.le_succ k) at hu
    grind

@[grind .]
lemma lc_of_open_body {t u : Term V} (h_lc : u.LC) (h_body : t.Body) : (t ^ u).LC := by
  rw [←lc_at_zero_iff_lc] at h_lc
  rw [←lc_at_one_iff_body] at h_body
  rw [←Nat.zero_add 1] at h_body
  rw [←lc_at_zero_iff_lc]
  grind [lc_at_of_openTermₖ_lc_at]

lemma subst_introₖ {t u : Term V} (h_fresh : x # t) : t.openTermₖ k u = [x ⟶ u] (t.openₖ k x) := by
  induction t generalizing k
  all_goals grind

lemma subst_intro {t u : Term V} (h_fresh : x # t) : t ^ u = [x ⟶ u] (t.open' x) := by grind [subst_introₖ]

@[grind .]
lemma openTermₖ_lc_at_le {t u : Term V} (h_lc_at : t.LCAt j) (hjk : j ≤ k) : t.openTermₖ k u = t := by
  induction t generalizing j k
  any_goals grind
  case abs t hi =>
    simp
    apply lc_at_of_lc_at_abs at h_lc_at
    apply @hi (j + 1) (k + 1) h_lc_at (by omega)

lemma openTermₖ_lc_at {t u : Term V} (h_lc_at : t.LCAt k) : t.openTermₖ k u = t := by rw [openTermₖ_lc_at_le h_lc_at (by omega)]

lemma openTerm_lc {t u : Term V} (h_lc : t.LC) : t ^ u = t := by rw [openTerm, openTermₖ_lc_at (by rw [lc_at_zero_iff_lc]; exact h_lc)]

lemma subst_openTermₖ {t u v : Term V} (h_lc_at : u.LCAt j) (hjk : j ≤ k) : [x ⟶ u] (t.openTermₖ k v) = ([x ⟶ u] t).openTermₖ k ([x ⟶ u] v) := by
  induction t generalizing k
  all_goals grind

lemma rename_openTermₖ {s t : Term V} :
    (s.openTermₖ k t).rename x y = (s.rename x y).openTermₖ k (t.rename x y) := by
  induction s generalizing k
  any_goals grind
  case fvar z => by_cases hzx : z = x <;> grind

@[simp, grind =]
lemma rename_openTerm {s t : Term V} :
    (s ^ t).rename x y = (s.rename x y) ^ (t.rename x y) := by
  grind [rename_openTermₖ]

lemma fvars_openTermₖ_subset {s t : Term V} :
    (s.openTermₖ k t).fvars ⊆ s.fvars ∪ t.fvars := by
  induction s generalizing k <;> grind

@[grind .]
lemma fvars_openTerm_subset {s t : Term V} : (s ^ t).fvars ⊆ s.fvars ∪ t.fvars := by
  grind only [fvars_openTermₖ_subset]

lemma subst_openTerm {t u v : Term V} (h_lc : u.LC) : [x ⟶ u] (t ^ v) = ([x ⟶ u] t) ^ ([x ⟶ u] v) := by
  grind only [lc_of_lc_at_zero, subst_openTermₖ, lc_at_zero_iff_lc]

inductive βStep : Term V → Term V → Prop where
  | beta (s t : Term V) (hs : s.Body) (ht : t.LC) :
    βStep (app (abs s) t) (s.openTerm t)
  | app₀ (ht₀ : βStep t₀ t₀') (ht₁_lc : t₁.LC) :
    βStep (app t₀ t₁) (app t₀' t₁)
  | app₁ (ht₁ : βStep t₁ t₁') (ht₀_lc : t₀.LC) :
    βStep (app t₀ t₁) (app t₀ t₁')
  | abs
    (names : Finset V) (ht : ∀ x ∉ names, βStep (t.open' x) (t'.open' x)) :
      βStep (abs t) (abs t')

infix:59 " →β " => βStep

@[grind .]
lemma βStep_beta {s t : Term V} (hs : s.Body) (ht : t.LC) :
    app (abs s) t →β s.openTerm t :=
  βStep.beta s t hs ht
@[grind .]
lemma βStep_app₀ {t₀ t₁ t₀' : Term V} (ht₀ : t₀ →β t₀') (ht₁_lc : t₁.LC) :
    app t₀ t₁ →β app t₀' t₁ :=
  βStep.app₀ ht₀ ht₁_lc
@[grind .]
lemma βStep_app₁ {t₀ t₁ t₁' : Term V} (ht₁ : t₁ →β t₁') (ht₀_lc : t₀.LC) :
    app t₀ t₁ →β app t₀ t₁' :=
  βStep.app₁ ht₁ ht₀_lc
lemma βStep_abs {t t' : Term V}
  (names : Finset V)
  (ht : ∀ x ∉ names, (t.open' x) →β (t'.open' x)) :
    abs t →β abs t' :=
  βStep.abs names ht

@[grind .]
lemma βStep_lc_left {t u : Term V}
  (h : t →β u) :
    t.LC := by
  induction h
  any_goals grind
  case abs _ _ t t' names ht ht_ih =>
    apply lc_abs names ht_ih
  case beta _ _ s t hs ht =>
    apply lc_app
    · rw [body_iff_lc_abs]
      exact hs
    · exact ht

@[grind .]
lemma βStep_lc_right {t u : Term V}
  (h : t →β u) : 
    u.LC := by
  induction h
  any_goals grind
  case abs _ _ t t' names ht ht_ih =>
    apply lc_abs names ht_ih

lemma βStep_rename_of_βStep {t u : Term V}
  (ht : t →β u) :
    t.rename x y →β u.rename x y := by
  induction ht with
  | app₀ => grind
  | app₁ => grind
  | @abs t t' names ht ht_ih =>
    repeat rw [rename_abs]
    apply βStep_abs (names ∪ {x} ∪ {y})
    intro z hz
    repeat rw [rename_open_eq_open_rename (hxz := by grind)]
    apply ht_ih z (by grind)
  | beta s t hs ht =>
    simp
    apply βStep_beta <;> grind

abbrev βReduces : Term V → Term V → Prop := Relation.ReflTransGen βStep

infix:59 " →β* " => βReduces

@[grind .]
lemma βReduces_refl (t : Term V) : t →β* t := Relation.ReflTransGen.refl
@[grind .]
lemma βReduces_head {s t u : Term V} (hst : s →β t) (htu : t →β* u) : s →β* u := by
  apply Relation.ReflTransGen.head hst htu
@[grind .]
lemma βReduces_tail {s t u : Term V} (hst : s →β* t) (htu : t →β u) : s →β* u := by
  apply Relation.ReflTransGen.tail hst htu

lemma βReduces_cases_head {a b : Term V} : a →β* b → a = b ∨ ∃ c, a →β c ∧ c →β* b := by
  intro h
  apply Relation.ReflTransGen.cases_head at h
  grind

@[grind .]
lemma βReduces_of_βStep {s t : Term V} (hst : s →β t) : s →β* t := by
  apply βReduces_head (t := t)
  · trivial
  · apply βReduces_refl

@[grind .]
lemma βReduces_app₀ {t₀ t₀' t₁ : Term V} (ht₀ : t₀ →β* t₀') (ht₁ : t₁.LC) : app t₀ t₁ →β* app t₀' t₁ := by
  induction ht₀
  all_goals grind
@[grind .]
lemma βReduces_app₁ {t₀ t₁ t₁' : Term V} (ht₁ : t₁ →β* t₁') (ht₀ : t₀.LC) : app t₀ t₁ →β* app t₀ t₁' := by
  induction ht₁
  all_goals grind

lemma βReduces_abs {t t' : Term V}
  (names : Finset V)
  (h : ∀ x ∉ names, t.open' x →β* t'.open' x) :
    abs t →β* abs t' := by
  have inst : Infinite V := by assumption
  have ⟨ x, hx ⟩ := inst.exists_notMem_finset (names ∪ t.fvars ∪ t'.fvars)
  specialize h x (by grind)
  generalize hs : t.open' x = s at *
  generalize hs' : t'.open' x = s' at *
  induction h using Relation.ReflTransGen.head_induction_on generalizing t t' with
  | refl =>
    subst_eqs
    have h : ∀ y, t'.open' y = t.open' y := by
      intro y
      rw [←open_rename_eq_open (x := x) (h_fresh := by grind) (t := t)]
      rw [←open_rename_eq_open (x := x) (h_fresh := by grind) (t := t')]
      rw [hs']
    apply open_ext at h
    rw [h]
  | @head s c hsc hcs' hi =>
    change c →β* s' at hcs'
    subst_eqs
    apply βReduces_head (t := (c.close x).abs)
    · apply βStep_abs names
      intro y hy
      rw [←open_close_var (x := x) (t := c) (by grind)] at hsc
      rw [←open_rename_eq_open (h_fresh := by grind) (x := x)]
      rw [←open_rename_eq_open (t := c.close x) (h_fresh := by grind) (x := x)]
      apply βStep_rename_of_βStep hsc
    · apply hi
      · grind
      · rw [open_close_var]
        grind
      · trivial

end

end Term

