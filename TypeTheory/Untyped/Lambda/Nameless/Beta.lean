module

import Mathlib.Tactic
public import TypeTheory.Untyped.Lambda.Nameless.Basic

namespace Term

public section

inductive βStep : Term → Term → Prop where
  | app0 (t0 t0' t1 : Term) : βStep (app t0 t1) (app t0' t1)
  | app1 (t0 t1 t1' : Term) (ht1 : βStep t1 t1') : βStep (app t0 t1) (app t0 t1')
  | abs (t t' : Term) (ht : βStep t t') : βStep (abs t) (abs t')
  | beta (t t' : Term) : βStep (app (abs t) t') (↑⁻¹ [ 0 := ↑¹ t' ] t)

infix:55 " ⟶ " => βStep

inductive βPStep : Term → Term → Prop where
  | refl (t : Term) : βPStep t t
  | app (ht0 : βPStep t0 t0') (ht1 : βPStep t1 t1') :
    βPStep (app t0 t1) (app t0' t1')
  | abs (ht : βPStep t t') : βPStep (abs t) (abs t')
  | beta (t t' : Term) : βPStep (app (abs t) t') (↑⁻¹ [ 0 := ↑¹ t' ] t)

infix:55 " →ₚ " => βPStep

@[grind .]
lemma βPStep_refl (t : Term) : t →ₚ t := βPStep.refl t

@[grind .]
lemma βPStep_app (ht0 : t0 →ₚ t0') (ht1 : t1 →ₚ t1') : app t0 t1 →ₚ app t0' t1' := βPStep.app ht0 ht1

@[grind .]
lemma βPStep_abs (ht : t →ₚ t') : abs t →ₚ abs t' := βPStep.abs ht

lemma βPStep_of_shift (ht : t →ₚ t') : t.shift k c →ₚ t'.shift k c := by
  induction ht generalizing c
  any_goals grind
  case beta t t' =>
    simp
    suffices h : ∀ j, ([ j := (t'.shift k c).shift (j + 1) 0 ] t.shift k (c + j + 1)).unshift 1 j = (([ j := t'.shift (j + 1) 0 ] t).unshift 1 j).shift k c by
      specialize h 0; rw [add_zero, zero_add] at h
      rw [←h]
      apply βPStep.beta
    intro j
    induction t generalizing j c with
    | var x =>
      sorry
    | app => grind
    | abs t ht =>
      simp
      sorry

lemma βPStep_subst_of_βPStep_terms₁
  (t0 t1 t1' : Term) (x : Nat) (ht1 : t1 →ₚ t1') :
    [ x := t0 ] t1 →ₚ [ x := t0 ] t1' := by
  induction ht1 generalizing x t0 with
  | refl => apply βPStep.refl
  | app hab hcd htia htib => grind
  | @abs t t' ht hi => grind
  | @beta t t' =>
    simp only [subst_app, subst_abs]
    have h : ↑⁻¹ [ 0 := ↑¹ [ x := t0 ] t' ] [ x + 1 := ↑¹ t0 ] t = [ x := t0 ] ↑⁻¹ [ 0 := ↑¹ t' ] t := by
      rw [subst_unshift]
      · have ht_shift : (↑¹ t0).Unshiftable 1 0 := by apply unshiftable_of_shift
        rw [subst_commute₀ (↑¹ t0) (↑¹ t') t ht_shift (by linarith)]
        rw [shift_subst_eq_subst_shift₀]
      · linarith
      · apply unshiftable_of_subst
    rw [←h]; apply βPStep.beta (([ x + 1 := ↑¹ t0 ] t)) ([ x := t0 ] t')

lemma βPStep_subst_of_βPStep_terms₀
  (t0 t0' t1 : Term) (x : Nat) (ht1 : t0 →ₚ t0') :
    [ x := t0 ] t1 →ₚ [ x := t0' ] t1 := by
  induction t1 generalizing x t0 t0'
  any_goals grind
  case abs t1 hi =>
    simp
    apply βPStep.abs
    specialize hi (↑¹ t0) (↑¹ t0') (x + 1)
    suffices h : ↑¹ t0 →ₚ ↑¹ t0' by grind
    clear hi
    induction ht1
    any_goals grind
    · simp
      sorry
    · simp
      sorry

lemma βPStep_subst_of_βPStep_terms
  (t0 t0' t1 t1' : Term) (x : Nat) (ht0 : t0 →ₚ t0') (ht1 : t1 →ₚ t1') :
    [ x := t0 ] t1 →ₚ [ x := t0' ] t1' := by
  sorry

end

end Term

