module

import Mathlib.Tactic

public import Mathlib.Logic.Relation

inductive Ty where
  | bool
  | arrow : Ty → Ty → Ty

inductive PreTerm (V : Ty → Type) : Ty → Type _ where
  | var : V t → PreTerm V t
  | app : PreTerm V (.arrow t₀ t₁) → PreTerm V t₀ → PreTerm V t₁
  | abs : (V t₀ → PreTerm V t₁) → PreTerm V (.arrow t₀ t₁)

abbrev Term ty := ∀ {V}, PreTerm V ty
abbrev Term₁ t₀ t₁ := ∀ {V}, (x : V t₀) → PreTerm V t₁

def embedType (t : Ty) : Type :=
  match t with
  | .bool => Bool
  | .arrow t₀ t₁ => (embedType t₀) → (embedType t₁)

instance : Inhabited (Ty → Type) where
  default := embedType

namespace PreTerm

def squash (e: PreTerm (PreTerm V) t) : PreTerm V t :=
  match e with
  | var x => x
  | app e₀ e₁ => app e₀.squash e₁.squash
  | abs e' => abs fun x => (e' (var x)).squash

end PreTerm

namespace Term

def subst (e₀ : Term₁ t₀ t₁) (e₁ : Term t₀) : Term t₁ := e₀ e₁ |>.squash

abbrev abs (e : Term₁ t₀ t₁) : Term (.arrow t₀ t₁) := PreTerm.abs e
abbrev app (e₀ : Term (.arrow t₀ t₁)) (e₁ : Term t₀) : Term t₁ :=
  PreTerm.app e₀ e₁

inductive βStep : Term t → Term t → Prop where
  | beta (e₀ : Term₁ t₀ t₁) (e₁ : Term t₀) :
    βStep (app (abs e₀) e₁) (subst e₀ e₁)
  | app₀ (e₀ : Term (.arrow t₀ t₁)) (e₁ : Term t₀) (he₀ : βStep e₀ e₀') :
    βStep (app e₀ e₁) (app e₀' e₁)
  | app₁ (e₀ : Term (.arrow t₀ t₁)) (e₁ : Term t₀) (he₁ : βStep e₁ e₁') :
    βStep (app e₀ e₁) (app e₀ e₁')

local infix:59 " →β " => βStep

@[grind .]
lemma βStep_beta : app (abs e₀) e₁ →β subst e₀ e₁ := βStep.beta e₀ e₁
lemma βStep_app₀ (he₀ : e₀ →β e₀') : app e₀ e₁ →β app e₀' e₁ := βStep.app₀ e₀ e₁ he₀
lemma βStep_app₁ (he₁ : e₁ →β e₁') : app e₀ e₁ →β app e₀ e₁' := βStep.app₁ e₀ e₁ he₁

lemma not_βStep_abs : ¬(abs e →β e') := by
  intro h
  generalize hx : (fun {V} => abs e) = x at *
  rw [funext_iff] at hx
  specialize hx embedType
  cases h
  all_goals grind

abbrev βReduces : Term t → Term t → Prop := Relation.ReflTransGen βStep

local infix:59 " →β* " => βReduces

inductive SN : Term t → Prop where
  | intro {e : Term t} (he : ∀ e', e →β e' → e'.SN) : e.SN

@[grind .]
lemma sn_intro {e : Term t} (he : ∀ e', e →β e' → e'.SN) : e.SN := SN.intro he

@[grind .]
lemma sn_βReduces_of_sn (he : e.SN) (hee' : e →β* e') : e'.SN := by
  induction hee' with
  | refl => exact he
  | @tail e' e'' hee' he'e'' he' => cases he'; grind

lemma sn_of_sn_app₀  (h : SN (app e₀ e₁)) : e₀.SN := by
  generalize he : (fun {V} => (app e₀ e₁)) = e at h
  induction h generalizing e₀ with
  | @intro e' h hi =>
    apply sn_intro
    intro e₀' he₀'
    subst_eqs
    specialize h (app e₀' e₁) (by apply βStep_app₀; trivial)
    specialize hi (app e₀' e₁)
    apply hi
    · apply βStep_app₀
      trivial
    · trivial

lemma sn_of_sn_app₁  (h : SN (app e₀ e₁)) : e₁.SN := by
  generalize he : (fun {V} => (app e₀ e₁)) = e at h
  induction h generalizing e₁ with
  | @intro e' h hi =>
    apply sn_intro
    intro e₁' he₁'
    subst_eqs
    specialize h (app e₀ e₁') (by apply βStep_app₁; trivial)
    specialize hi (app e₀ e₁')
    apply hi
    · apply βStep_app₁
      trivial
    · trivial

lemma sn_abs : SN (abs e) := by
  apply sn_intro
  intro e' h
  apply not_βStep_abs at h
  trivial

end Term

