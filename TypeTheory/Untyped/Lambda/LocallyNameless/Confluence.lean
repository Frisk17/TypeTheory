module
public import TypeTheory.Untyped.Lambda.LocallyNameless.Beta

namespace Term

public section

variable [Infinite V] [DecidableEq V]

inductive βPStep : Term V → Term V → Prop where
  | refl (t : Term V) (ht : t.LC) : βPStep t t
  | app (ht₀ : βPStep t₀ t₀') (ht₁ : βPStep t₁ t₁') :
    βPStep (app t₀ t₁) (app t₀' t₁')
  | abs
    (names : Finset V) (ht : ∀ x ∉ names, βPStep (t.open' x) (t'.open' x)) :
      βPStep (abs t) (abs t')
  | beta
    (s s' t t' : Term V) (names : Finset V)
    (hs_step : ∀ x ∉ names, βPStep (s.open' x) (s'.open' x))
    (ht_step : βPStep t t') :
      βPStep (app (abs s) t) (s'.openTerm t')

infix:59 " →ₚ " => βPStep

@[grind .]
lemma βPStep_refl {t : Term V} (ht : t.LC) : t →ₚ t := βPStep.refl t ht
@[grind .]
lemma βPStep_app {t₀ t₁ t₀' t₁' : Term V} (ht₀ : t₀ →ₚ t₀') (ht₁ : t₁ →ₚ t₁') : app t₀ t₁ →ₚ app t₀' t₁' := βPStep.app ht₀ ht₁
lemma βPStep_abs {t t' : Term V} (names : Finset V) (ht : ∀ x ∉ names, t.open' x →ₚ t'.open' x) : abs t →ₚ abs t' := βPStep.abs names ht
lemma βPStep_beta {t t' u u' : Term V}
  (names : Finset V)
  (ht : ∀ x ∉ names, t.open' x →ₚ t'.open' x)
  (hu : u →ₚ u') :
    app (abs t) u →ₚ t'.openTerm u' :=
  βPStep.beta t t' u u' names ht hu

lemma βPStep_lc_of_lc {t t' : Term V}
  (ht : t.LC) (h_step : t →ₚ t') :
    t'.LC := by
  induction h_step
  any_goals grind
  case abs t t' names hi hi' =>
    apply lc_abs names
    rw [body_iff_lc_abs] at ht
    intro x hx
    apply open_var_lc (x := x) at ht
    grind
  case beta s s' t t' names hs_step ht' hi hi' =>
    have hs := (body_iff_lc_abs s).mp (lc₀_of_lc_app ht)
    have ht := lc₁_of_lc_app ht
    apply lc_of_open_body
    · apply hi' ht
    · rw [←body_iff_lc_abs]
      apply lc_abs names
      intro x hx
      apply hi x hx
      apply open_var_lc
      exact hs

@[grind .]
lemma βPStep_lc_left {t t' : Term V} (ht : t →ₚ t') : t.LC := by
  induction ht
  any_goals grind
  case abs t t' names h hi =>
    apply lc_abs names
    intro x hx
    apply hi x hx
  case beta s s' t t' names hs_step ht_step hsi hti =>
    apply lc_app
    · apply lc_abs names
      intro x hx
      apply hsi x hx
    · exact hti

@[grind .]
lemma βPStep_lc_right {t t' : Term V} (ht : t →ₚ t') : t'.LC := by
  have ht' := βPStep_lc_left ht
  apply βPStep_lc_of_lc ht' ht

lemma subst_βPStep_of_βPStep' {s t t' : Term V}
  (hs : s.LC)
  (h_step : t →ₚ t') :
    [x ⟶ t] s →ₚ [x ⟶ t'] s := by
  have ht : t.LC := βPStep_lc_left h_step
  generalize hn : SizeOf.sizeOf s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n hi =>
    cases s
    any_goals grind
    case abs s =>
      have ht' : t'.LC := βPStep_lc_of_lc ht h_step
      repeat rw [subst_abs]
      apply βPStep_abs {x}
      intro y hy
      rw [subst_open_var x y (by grind) ht]
      rw [subst_open_var x y (by grind) ht']
      rw [body_iff_lc_abs] at hs
      apply open_var_lc (x := y) at hs
      apply hi (SizeOf.sizeOf (s.open' y)) (by grind) hs (by trivial)

lemma subst_βPStep_of_βPStep {s s' t t' : Term V}
  (hs_step : s →ₚ s')
  (ht_step : t →ₚ t') :
    [x ⟶ t] s →ₚ [x ⟶ t'] s' := by
  have hs := βPStep_lc_left hs_step
  have ht := βPStep_lc_left ht_step
  have ht' := βPStep_lc_right ht_step
  induction hs_step with
  | refl => grind only [subst_βPStep_of_βPStep']
  | app => grind
  | @abs s s' names hi hi' =>
    repeat rw [subst_abs]
    apply βPStep_abs (names ∪ {x})
    intro y hy
    rw [subst_open_var x y (by grind) ht]
    rw [subst_open_var x y (by grind) ht']
    rw [body_iff_lc_abs] at hs
    apply open_var_lc (x := y) at hs
    apply hi' y (by grind) hs
  | beta s s' u u' names hs_step hu_step hsi hui =>
    have hu := lc₁_of_lc_app hs
    have hs := (body_iff_lc_abs s).mp (lc₀_of_lc_app hs)
    simp
    have h : ([x ⟶ t'] s') ^ ([x ⟶ t'] u') = [x ⟶ t'] s' ^ u' := by
      have inst : Infinite V := by assumption
      have ⟨ y, hy ⟩ := inst.exists_notMem_finset (([x ⟶ t'] s').fvars ∪ {x} ∪ (t'.fvars) ∪ (s'.fvars))
      rw [subst_intro (x := y) (by grind)]
      rw [subst_open_var _ _ (by grind) ht']
      rw [←subst_commute (by grind) (by grind)]
      rw [←subst_intro (by grind)]
    rw [←h]
    apply βPStep_beta (names ∪ {x})
    · intro y hy
      rw [subst_open_var x y (by grind) ht]
      rw [subst_open_var x y (by grind) ht']
      apply hsi y (by grind)
      apply open_var_lc _ hs
    · apply hui hu

lemma open_βPStep_of_βPStep {s s' t t' : Term V}
  (names : Finset V)
  (hs : ∀ x ∉ names, s.open' x →ₚ s'.open' x)
  (ht : t →ₚ t') :
    s ^ t →ₚ s' ^ t' := by
  have inst : Infinite V := by assumption
  have ⟨ x, hx ⟩ := inst.exists_notMem_finset (s.fvars ∪ s'.fvars ∪ names)
  rw [subst_intro (x := x) (by grind)]
  rw [subst_intro (x := x) (by grind)]
  specialize hs x (by grind)
  apply subst_βPStep_of_βPStep hs ht

lemma βPStep_rename_of_βPStep {t u : Term V}
  (ht : t →ₚ u) :
    t.rename x y →ₚ u.rename x y := by
  induction ht with
  | refl w hw =>
    have hw_rename_lc : (w.rename x y).LC := lc_rename_of_lc w hw
    apply βPStep_refl hw_rename_lc
  | app ht₀ ht₁ ht₀_ih ht₁_ih => grind
  | @abs t t' names ht ht_ih =>
    simp
    apply βPStep_abs (names ∪ {x})
    intro z hz
    repeat rw [rename_open_eq_open_rename]
    all_goals grind
  | beta s s' t t' names hs_step ht_step hs_step_ih ht_step_ih =>
    simp_all
    apply βPStep_beta (names ∪ {x})
    · intro z hz
      repeat rw [rename_open_eq_open_rename]
      all_goals grind
    · grind

lemma βPStep_diamond' {s t t' : Term V}
  (ht : s →ₚ t)
  (ht' : s →ₚ t') :
    ∃ u, t →ₚ u ∧ t' →ₚ u :=
  match ht, ht' with
  | βPStep.refl _ _, hst' => ⟨ t', ⟨ hst', βPStep_refl (βPStep_lc_right hst') ⟩ ⟩
  | hst, βPStep.refl _ _ => ⟨ t, ⟨ βPStep_refl (βPStep_lc_right hst), hst ⟩ ⟩
  | @βPStep.abs _ _ _ s t names hst, @βPStep.abs _ _ _ _ t' names' hst' => by
    have inst : Infinite V := by assumption
    have ⟨ x, hx ⟩ := inst.exists_notMem_finset (names ∪ names' ∪ s.fvars ∪ t.fvars ∪ t'.fvars)
    have hst_x := hst x (by grind only [= Finset.mem_union])
    have hst'_x := hst' x (by grind only [= Finset.mem_union])
    have ⟨ u, ⟨ htu, ht'u ⟩ ⟩ := βPStep_diamond' hst_x hst'_x
    have hu_fresh : x # (u.close x) := fresh_close x u
    have hu_lc := βPStep_lc_right htu
    rw [←open_close_var (x := x) hu_lc] at htu ht'u
    use (u.close x).abs
    constructor <;> (
      apply βPStep_abs {x}
      intro y hy
      apply βPStep_rename_of_βPStep (x := x) (y := y) at htu
      apply βPStep_rename_of_βPStep (x := x) (y := y) at ht'u
      rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at htu
      rw [open_rename_eq_open _ (by grind only)] at htu
      rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at ht'u
      rw [open_rename_eq_open _ (by grind only)] at ht'u
      trivial)
  | @βPStep.app _ _ _ s₀ t₀ s₁ t₁ ht₀ ht₁, @βPStep.app _ _ _ _ u₀ _ u₁ hu₀ hu₁ => by
    have ⟨ v₀, hv₀ ⟩ := βPStep_diamond' ht₀ hu₀
    have ⟨ v₁, hv₁ ⟩ := βPStep_diamond' ht₁ hu₁
    use (app v₀ v₁); grind only [βPStep_app]
  | βPStep.beta s s₀ t t₀ names₀ hs₀ ht₀, βPStep.beta _ s₁ _ t₁ names₁ hs₁ ht₁ => by
    have inst : Infinite V := by assumption
    have ⟨ x, hx ⟩ := inst.exists_notMem_finset (names₀ ∪ names₁ ∪ s₀.fvars ∪ s₁.fvars)
    have hs₀x := hs₀ x (by grind only [= Finset.mem_union])
    have hs₁x := hs₁ x (by grind only [= Finset.mem_union])
    have ⟨ s', ⟨ hs'₀, hs'₁ ⟩ ⟩ := βPStep_diamond' hs₀x hs₁x
    have ⟨ t', ⟨ ht'₀, ht'₁ ⟩ ⟩ := βPStep_diamond' ht₀ ht₁
    have hs' := βPStep_lc_right hs'₀
    rw [←open_close_var (x := x) hs'] at hs'₀
    rw [←open_close_var (x := x) hs'] at hs'₁
    have h_fresh := fresh_close x s'
    use (s'.close x) ^ t'
    constructor <;> (
      apply open_βPStep_of_βPStep (names₀ ∪ names₁) (ht := by grind only)
      intro y hy
      apply βPStep_rename_of_βPStep (x := x) (y := y) at hs'₀
      apply βPStep_rename_of_βPStep (x := x) (y := y) at hs'₁
      rw [open_rename_eq_open _ h_fresh] at hs'₀
      rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at hs'₀
      rw [open_rename_eq_open _ h_fresh] at hs'₁
      rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at hs'₁
      trivial
    )
  | βPStep.beta s s' t t' names hs ht, @βPStep.app _ _ _ _ u _ v hu hv =>
    match _ : hu with
    | βPStep.refl _ _ => by
      have ⟨ w, ⟨ ht'w, hvw ⟩ ⟩ := βPStep_diamond' ht hv
      use s' ^ w
      constructor
      · apply open_βPStep_of_βPStep names
        · intro x hx
          apply βPStep_refl (βPStep_lc_right (hs x hx))
        · trivial
      · apply βPStep_beta names hs hvw
    | @βPStep.abs _ _ _ _ w names' hw => by
      have inst : Infinite V := by assumption
      have ⟨ x, hx ⟩ := inst.exists_notMem_finset (names ∪ names' ∪ s'.fvars ∪ w.fvars)
      have hsx := hs x (by grind only [= Finset.mem_union])
      have hsw := hw x (by grind only [= Finset.mem_union])
      have ⟨ a, ⟨ hs'a, hwa ⟩ ⟩ := βPStep_diamond' hsx hsw
      have ha := βPStep_lc_right hs'a
      rw [←open_close_var (x := x) ha] at hs'a
      rw [←open_close_var (x := x) ha] at hwa
      have h : ∀ y, s'.open' y →ₚ (a.close x).open' y ∧ w.open' y →ₚ (a.close x).open' y := by
        intro y
        apply βPStep_rename_of_βPStep (x := x) (y := y) at hs'a
        apply βPStep_rename_of_βPStep (x := x) (y := y) at hwa
        have h_fresh := fresh_close x a
        rw [open_rename_eq_open _ h_fresh] at hs'a
        rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at hs'a
        rw [open_rename_eq_open _ h_fresh] at hwa
        rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at hwa
        trivial
      have ⟨ b, ⟨ ht'b, hvb ⟩ ⟩ := βPStep_diamond' ht hv
      use (a.close x) ^ b
      constructor
      · apply open_βPStep_of_βPStep {}
        · intro y hy
          apply (h y).1
        · trivial
      · apply βPStep_beta {}
        · intro y hy
          apply (h y).2
        · trivial
  | @βPStep.app _ _ _ _ _ _ _ _ _, βPStep.beta s s' t t' names hs ht => by
    rename_i u v hu hv
    suffices h' : ∃ u_1, s' ^ t' →ₚ u_1 ∧ u.app v →ₚ u_1 by
      obtain ⟨ u, h' ⟩ := h'
      use u
      grind only
    exact (match _ : hu with
    | βPStep.refl _ _ => by
      have ⟨ w, ⟨ ht'w, hvw ⟩ ⟩ := βPStep_diamond' ht hv
      use s' ^ w
      constructor
      · apply open_βPStep_of_βPStep names
        · intro x hx
          apply βPStep_refl (βPStep_lc_right (hs x hx))
        · trivial
      · apply βPStep_beta names hs hvw
    | @βPStep.abs _ _ _ _ w names' hw => by
      have inst : Infinite V := by assumption
      have ⟨ x, hx ⟩ := inst.exists_notMem_finset (names ∪ names' ∪ s'.fvars ∪ w.fvars)
      have hsx := hs x (by grind only [= Finset.mem_union])
      have hsw := hw x (by grind only [= Finset.mem_union])
      have ⟨ a, ⟨ hs'a, hwa ⟩ ⟩ := βPStep_diamond' hsx hsw
      have ha := βPStep_lc_right hs'a
      rw [←open_close_var (x := x) ha] at hs'a
      rw [←open_close_var (x := x) ha] at hwa
      have h : ∀ y, s'.open' y →ₚ (a.close x).open' y ∧ w.open' y →ₚ (a.close x).open' y := by
        intro y
        apply βPStep_rename_of_βPStep (x := x) (y := y) at hs'a
        apply βPStep_rename_of_βPStep (x := x) (y := y) at hwa
        have h_fresh := fresh_close x a
        rw [open_rename_eq_open _ h_fresh] at hs'a
        rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at hs'a
        rw [open_rename_eq_open _ h_fresh] at hwa
        rw [open_rename_eq_open _ (by grind only [= Finset.mem_union])] at hwa
        trivial
      have ⟨ b, ⟨ ht'b, hvb ⟩ ⟩ := βPStep_diamond' ht hv
      use (a.close x) ^ b
      constructor
      · apply open_βPStep_of_βPStep {}
        · intro y hy
          apply (h y).1
        · trivial
      · apply βPStep_beta {}
        · intro y hy
          apply (h y).2
        · trivial)

lemma βReduces_of_βPStep {t t' : Term V}
  (htt' : t →ₚ t') :
    t →β* t' := by
  induction htt' with
  | refl t h => apply βReduces_refl
  | @app t₀ t₀' t₁ t₁' ht₀ ht₁ hti₀ hti₁ =>
    calc
      _ →β* t₀'.app t₁ := by grind
      _ →β* _ := by grind
  | @abs t t' names ht ht_ih =>
    apply βReduces_abs names
    trivial
  | beta s s' t t' names hs_step ht_step hs_step_ih ht_step_ih =>
    have ht_lc : t.LC := by grind
    have ht'_lc : t'.LC := by grind
    calc
      _ →β* s'.abs.app t := by
        apply βReduces_app₀
        · apply βReduces_abs names
          intro x hx
          apply hs_step_ih x hx
        · trivial
      _ →β* s'.abs.app t' := by
        apply βReduces_app₁
        · trivial
        · apply lc_abs names
          intro x hx
          specialize hs_step x hx
          grind
      _ →β _ := by
        apply βStep_beta
        · rw [←body_iff_lc_abs]
          apply lc_abs names
          intro x hx
          specialize hs_step x hx
          grind
        · trivial

lemma βPStep_of_βStep {t t' : Term V}
  (htt' : t →β t') :
    t →ₚ t' := by
  induction htt'
  any_goals grind
  case beta s t hs ht =>
    rcases hs with ⟨ names, hs ⟩
    apply βPStep_beta names
    · intro x hx
      apply βPStep_refl
      apply hs x hx
    · apply βPStep.refl _ ht
  case abs t t' names ht hti =>
    apply βPStep_abs names
    intro x hx
    apply hti x hx

abbrev βPReduces : Term V → Term V → Prop := Relation.ReflTransGen βPStep

infix:59 " →ₚ* " => βPReduces

@[grind .]
lemma βPReduces_refl (t : Term V) : t →ₚ* t := Relation.ReflTransGen.refl
@[grind .]
lemma βPReduces_head {s t u : Term V} (hst : s →ₚ t) (htu : t →ₚ* u) : s →ₚ* u := by
  apply Relation.ReflTransGen.head hst htu
@[grind .]
lemma βPReduces_tail {s t u : Term V} (hst : s →ₚ* t) (htu : t →ₚ u) : s →ₚ* u := by
  apply Relation.ReflTransGen.tail hst htu

lemma βReduces_of_βPReduces {t t' : Term V}
  (htt' : t →ₚ* t') :
    t →β* t' := by
  induction htt' with
  | refl => apply βReduces_refl
  | @tail t' t'' h htt'' hi =>
    calc
      _ →β* t' := by trivial
      _ →β* _ := by apply βReduces_of_βPStep htt''

lemma βPReduces_of_βReduces {t t' : Term V}
  (htt' : t →β* t') :
    t →ₚ* t' := by
  induction htt' with
  | refl => apply βPReduces_refl
  | @tail t' t'' htt' ht't'' hi =>
    calc
      _ →ₚ* t' := by trivial
      _ →ₚ _ := by
        apply βPStep_of_βStep ht't''

lemma βPReduces_iff_βReduces {t t' : Term V} : t →ₚ* t' ↔ t →β* t' := by
  grind [βPReduces_of_βReduces, βReduces_of_βPReduces]

lemma βPReduces_eq_βReduces : βPReduces = (@βReduces V _ _) := by
  ext; simp [βPReduces_iff_βReduces]

abbrev Diamond (r : α → α → Prop) := ∀ a b c, r a b ∧ r a c → ∃ d, r b d ∧ r c d

lemma βPStep_diamond : Diamond (@βPStep V (by assumption) (by assumption)) := by
  intro a b c ⟨ h0, h1 ⟩
  apply βPStep_diamond' (s := a) (t := b) (t' := c) h0 h1

private lemma diamond_ReflTransGen_step_of_diamond
  (hr : Diamond r)
  (hab : r a b) (hac : (Relation.ReflTransGen r) a c) :
    ∃ d, (Relation.ReflTransGen r) b d ∧ r c d := by
  induction hac with
  | refl =>
    use b
  | @tail c' c hac' hc'c hi =>
    obtain ⟨ d, ⟨ hbd, hc'd ⟩ ⟩ := hi
    have ⟨ d', ⟨ hcd', h ⟩ ⟩ := hr c' c d (by grind)
    use d'; grind

lemma diamond_ReflTransGen_of_diamond (hr : Diamond r) :
    Diamond (Relation.ReflTransGen r) := by
  intro a b c ⟨ hab, hac ⟩
  induction hac with
  | refl =>
    use b
  | @tail c' c hac' hc'c hi =>
    obtain ⟨ d', ⟨ hbd', hc'd' ⟩ ⟩ := hi
    have ⟨ e, hce, hd'e ⟩ := diamond_ReflTransGen_step_of_diamond hr hc'c hc'd'
    use e
    constructor
    · calc
        (Relation.ReflTransGen r) _ d' := hbd'
        r _ _ := hd'e 
    · trivial

lemma diamond_βPReduces : Diamond (@βPReduces V _ _) := by
  apply diamond_ReflTransGen_of_diamond
  apply βPStep_diamond

lemma diamond_βReduces : Diamond (@βReduces V _ _) := by
  rw [←βPReduces_eq_βReduces]
  apply diamond_βPReduces

end

end Term

