module

import Mathlib.Tactic

public import Mathlib.Logic.Relation
public import TypeTheory.Simple.Lambda.DeBruijn.Basic

open Ty

namespace Expr

public section

inductive βStep : Γ ⊢ t → Γ ⊢ t → Prop where
  | app₀ (e₀ : Γ ⊢ fn t₀ t₁) (e₁ : Γ ⊢ t₀) (he₀ : βStep e₀ e₀') :
    βStep (app e₀ e₁) (app e₀' e₁)
  | app₁ (e₀ : Γ ⊢ fn t₀ t₁) (e₁ : Γ ⊢ t₀) (he₁ : βStep e₁ e₁') :
      βStep (app v₀ e₁) (app v₀ e₁')
  | abs (he : βStep e e') : βStep (abs e) (abs e')
  | beta (e₀ : (t₀ :: Γ) ⊢ t₁) (e₁ : Γ ⊢ t₀) : βStep (app (abs e₀) e₁) ([v₁] e₀)

infix:59 " →β " => βStep

@[grind .]
lemma βStep_app₀ {e₀ : Γ ⊢ fn t₀ t₁} {e₁ : Γ ⊢ t₀}
  (he₀ : e₀ →β e₀') : (app e₀ e₁) →β (app e₀' e₁) := βStep.app₀ e₀ e₁ he₀
@[grind .]
lemma βStep_app₁ {e₀ : Γ ⊢ fn t₀ t₁} {e₁ : Γ ⊢ t₀}
  (he₁ : e₁ →β e₁') : (app e₀ e₁) →β (app e₀ e₁') := βStep.app₁ e₀ e₁ he₁
@[grind .]
lemma βStep_abs {e e' : t₀ :: Γ ⊢ t}
  (he : e →β e') : abs e →β abs e' := βStep.abs he
@[grind .]
lemma βStep_beta {e₀ : (t₀ :: Γ) ⊢ t₁} {e₁ : Γ ⊢ t₀} : (app (abs e₀) e₁) →β [e₁]e₀ := βStep.beta e₀ e₁

@[grind .]
lemma not_βStep_var (x : Γ ∋ t) : ¬((var x) →β e) := by
  intro h; cases h

@[grind .]
lemma not_βStep_unit : ¬(unit →β e) := by
  intro h; cases h

abbrev βReduces : Γ ⊢ t → Γ ⊢ t → Prop := Relation.ReflTransGen βStep

infix:59 " →β* " => βReduces

@[grind .]
lemma βReduces_refl : e →β* e := Relation.ReflTransGen.refl
@[grind .]
lemma βReduces_tail (he₀e₁ : e₀ →β* e₁) (he₁e₂ : e₁ →β e₂) : e₀ →β* e₂ := Relation.ReflTransGen.tail he₀e₁ he₁e₂
@[grind .]
lemma βReduces_head (he₀e₁ : e₀ →β e₁) (he₁e₂ : e₁ →β* e₂) : e₀ →β* e₂ := Relation.ReflTransGen.head he₀e₁ he₁e₂

lemma βReduces_ind_tail
  {motive : (e e' : Γ ⊢ t) → e →β* e' → Prop}
  (refl : (e : Γ ⊢ t) → motive e e βReduces_refl)
  (tail : (e₀ e₁ e₂ : Γ ⊢ t) → (he₀e₁ : e₀ →β* e₁) → (he₁e₂ : e₁ →β e₂) → motive e₀ e₁ he₀e₁ → motive e₀ e₂ (βReduces_tail he₀e₁ he₁e₂))
  (hee' : e →β* e') :
    motive e e' hee' := by induction hee' <;> grind
lemma βReduces_ind_head
  {motive : (e e' : Γ ⊢ t) → e →β* e' → Prop}
  (refl : (e : Γ ⊢ t) → motive e e βReduces_refl)
  (head : (e₀ e₁ e₂ : Γ ⊢ t) → (he₀e₁ : e₀ →β e₁) → (he₁e₂ : e₁ →β* e₂) → motive e₁ e₂ he₁e₂ → motive e₀ e₂ (βReduces_head he₀e₁ he₁e₂))
  (hee' : e →β* e') :
    motive e e' hee' := by induction hee' using Relation.ReflTransGen.head_induction_on <;> grind

@[grind .]
lemma βReduces_app₀ (he₀ : e₀ →β* e₀') : app e₀ e₁ →β* app e₀' e₁ := by
  induction he₀ using βReduces_ind_tail with
  | refl e₀ => apply βReduces_refl
  | tail e₀ e₀' e₀'' he₀' he₀'' hi =>
    calc
      _ →β* app e₀' e₁ := hi
      _ →β _ := βStep_app₀ he₀''

@[grind .]
lemma βReduces_app₁ (he₁ : e₁ →β* e₁') : app e₀ e₁ →β* app e₀ e₁' := by
  induction he₁ using βReduces_ind_tail with
  | refl _ => apply βReduces_refl
  | tail e₁ e₁' e₁'' he₁' he₁'' hi =>
    calc
      _ →β* app e₀ e₁' := hi
      _ →β _ := βStep_app₁ he₁''

@[grind .]
lemma βReduces_abs (he : e →β* e') : abs e →β* abs e' := by
  induction he using βReduces_ind_tail with
  | refl _ => apply βReduces_refl
  | tail e e' e'' he' he''  hi =>
    calc
      _ →β* abs e' := hi
      _ →β _ := βStep_abs he''

end

end Expr

