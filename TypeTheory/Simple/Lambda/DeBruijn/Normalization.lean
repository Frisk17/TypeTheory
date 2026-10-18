module

import Mathlib.Tactic

public import TypeTheory.Simple.Lambda.DeBruijn.Beta

open Ty

namespace Expr

public section

mutual
inductive Nf : Γ ⊢ t → Type where
  | ne (he : Ne e) : Nf e
  | abs (he : Nf e) : Nf (abs e)

inductive Ne : Γ ⊢ t → Type where
  | unit : Ne unit
  | var (x : Γ ∋ t) : Ne (var x)
  | app (he₀ : Ne e₀) (he₁ : Nf e₁) : Ne (app e₀ e₁)
end

abbrev ne_of_app_nf (h : (app e₀ e₁).Nf) : (app e₀ e₁).Ne := by
  rcases h; trivial

abbrev ne₀_of_app_nf (h : (app e₀ e₁).Nf) : e₀.Ne := by
  cases h
  case ne he =>
    cases he
    trivial

abbrev nf₀_of_app_nf (h : (app e₀ e₁).Nf) : e₀.Nf := by
  apply Nf.ne
  apply ne₀_of_app_nf h

abbrev nf₁_of_app_nf (h : (app e₀ e₁).Nf) : e₁.Nf := by
  cases h
  case ne he =>
    cases he
    trivial

abbrev Nf' t := (Γ : Ctx) → Σ e : Γ ⊢ t, @Nf Γ t e
abbrev Ne' t := (Γ : Ctx) → Option (Σ e : Γ ⊢ t, @Ne Γ t e)

end

end Expr

namespace Ty

public section

abbrev denote (t : Ty) : Type :=
  match t with
  | unit => Expr.Ne' unit
  | fn t₀ t₁ => (denote t₀) → (denote t₁)

notation:60 "⟦ " t:60 " ⟧" => denote t

end

end Ty

namespace Ctx

public section

abbrev denote (Γ : Ctx) : Type :=
  match Γ with
  | [] => Unit
  | t :: Γ => t.denote × (denote Γ)

notation:60 "⟦ " t:60 " ⟧" => denote t

end

end Ctx

namespace Expr

public section

def denote (e : Γ ⊢ t) : ⟦ Γ ⟧ → ⟦ t ⟧ :=
  match e with
  | var x =>
    let rec lookup {Γ} (x : Γ ∋ t) (s : ⟦ Γ ⟧) : ⟦ t ⟧ :=
      match x with
      | Ctx.Mem.head => s.fst
      | Ctx.Mem.tail y => lookup y s.snd
    fun s => lookup x s
  | app e₀ e₁ => fun s => (denote e₀ s) (denote e₁ s)
  | abs e => fun s x => denote e (x, s)
  | unit => fun _ _ => some <| Sigma.mk unit Ne.unit

private def liftHead {Γ : Ctx} {t : Ty} : Ne' t :=
  fun Γ' =>
    if h_prefix : (t :: Γ) <+: Γ' then
      have h : t :: (Γ ++ List.drop (t :: Γ).length Γ') = Γ' := by
        rw [← List.cons_append]
        rw [← List.prefix_iff_eq_append]
        apply h_prefix
      have h : Γ' = t :: (Γ ++ List.drop (t :: Γ).length Γ') := by grind
      let y' : Γ' ∋ t := h.symm ▸ .head
      let y : Γ' ⊢ t := var y'
      have hy : Ne (var y') := Ne.var y'
      some <| Sigma.mk y hy
    else
      none

mutual
def reflect (e : Ne' t) : ⟦ t ⟧ :=
  match t with
  | .unit => fun Γ => do
    let e ← e Γ
    some <| Sigma.mk e.fst e.snd
  | .fn _ t₁ =>
    fun x =>
      let x' := reify x
      let e' : Ne' t₁ := fun Γ => do
        let z := x' Γ
        let f ← e Γ
        pure <| Sigma.mk (app f.fst z.fst) (Ne.app f.snd z.snd)
      reflect e'

def reify {t : Ty} (s : ⟦ t ⟧) : Nf' t :=
  match t with
  | .unit => fun Γ =>
    match s Γ with
    | some e =>
      Sigma.mk e.fst <| Nf.ne e.snd
    | none =>
      Sigma.mk unit <| Nf.ne Ne.unit
  | .fn t₀ t₁ => fun Γ =>
    let x : Ne' t₀ := liftHead (Γ := Γ)
    let e' := (reify (s (reflect x))) (t₀ :: Γ)
    let e : Γ ⊢ .fn t₀ t₁ := abs <| e'.fst
    Sigma.mk e <| Nf.abs e'.snd
end

private def reflectCtx (Γ : Ctx) : ⟦ Γ ⟧ :=
  match Γ with
  | [] => ()
  | t :: Γ => (reflect (liftHead (Γ := Γ) (t := t)), reflectCtx Γ)

def normalize (e : Γ ⊢ t) : Σ e : Γ ⊢ t, @Nf Γ t e :=
  let s := e.denote (reflectCtx Γ)
  reify s Γ

private def id : ∅ ⊢ (.fn .unit .unit) := abs ♯0
#eval id
#eval normalize id |>.fst

private def foo : [.unit] ⊢ .unit := app (abs ♯0) ♯0

#eval foo

#eval normalize foo |>.fst

end

end Expr

