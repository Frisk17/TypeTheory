module

import Mathlib.Tactic

public import Mathlib.Data.Finite.Defs

public inductive PreTerm V where
  | var : V → PreTerm V
  | app : PreTerm V → PreTerm V → PreTerm V
  | abs : (V → PreTerm V) → PreTerm V

public abbrev Term := ∀ {V}, PreTerm V
public abbrev Term₁ := ∀ {V}, V → PreTerm V

namespace PreTerm

public section

def squash (t : PreTerm (PreTerm V)) : PreTerm V :=
  match t with
  | var x => x
  | app t₀ t₁ => app t₀.squash t₁.squash
  | abs t => abs fun x => (t (var x)).squash

end

end PreTerm

namespace Term

def subst (s : Term₁) (t : Term) : Term := (s t).squash

open PreTerm

inductive βStep : Term → Term → Prop where
  | beta {s : Term₁} {t : Term} : βStep (app (abs s) t) (subst s t)
  | app₀ {t₀ t₀' t₁ : Term} (ht₀ : βStep t₀ t₀') : βStep (app t₀ t₁) (app t₀' t₁)
  | app₁ {t₀ t₁ t₁' : Term} (ht₁ : βStep t₁ t₁') : βStep (app t₀ t₁) (app t₀ t₁')

end Term

