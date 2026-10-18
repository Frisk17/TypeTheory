module

import Mathlib.Tactic

public inductive Ty where
  | unit : Ty
  | fn : Ty → Ty → Ty
deriving Repr, DecidableEq

public abbrev Ctx := List Ty

namespace Ctx

public section

inductive Mem : Ctx → Ty → Type where
  | head : Mem (t :: Γ) t
  | tail : Mem Γ t → Mem (t' :: Γ) t
deriving Repr, DecidableEq

infix:50 " ∋ " => Mem

@[grind .]
abbrev mem_head (t : Ty) : t :: Γ ∋ t := Mem.head
@[grind .]
abbrev mem_tail (h_mem : Γ ∋ t) : (t' :: Γ) ∋ t := Mem.tail h_mem

abbrev mem_get (Γ : Ctx) (n : Fin Γ.length) : Γ ∋ Γ.get n :=
  match Γ with
  | [] =>
    False.elim (Fin.elim0 n)
  | x :: Γ =>
    Fin.cases
      (mem_head x)
      (fun m => mem_tail (mem_get Γ m))
      n

def toNat (h : Γ ∋ t) : Nat :=
  match h with
  | .head => 0
  | .tail h' =>
    1 + toNat h'

end

end Ctx

public inductive Expr : Ctx → Ty → Type _ where
  | unit : Expr Γ Ty.unit
  | var (h : Γ ∋ ty) : Expr Γ ty
  | abs (e : Expr (t₀ :: Γ) t₁) : Expr Γ (.fn t₀ t₁)
  | app (e₀ : Expr Γ (.fn t₀ t₁)) (e₁ : Expr Γ t₀) : Expr Γ t₁
deriving DecidableEq

namespace Expr

public section

infix:59 " ⊢ " => Expr

open Std.Format in
def repr (e : Γ ⊢ t) (p : Nat) : Std.Format :=
  match e with
  | unit =>
    text s!"()"
  | var x =>
    text s!"{Ctx.toNat x}"
  | app e₀ e₁ =>
    paren (joinSep [e₀.repr p, e₁.repr p] (text " "))
  | abs e' =>
    paren (join ["λ.", e'.repr p])

instance instRepr : Repr (Γ ⊢ t) where
  reprPrec := repr

def ofFin (n : Fin (List.length Γ)) : Γ ⊢ Γ.get n := var (Ctx.mem_get Γ n)
def ofNat (n : Nat) (hn := by grind) : Γ ⊢ Γ.get ⟨ n, hn ⟩ := ofFin ⟨ n, hn ⟩

notation:max "♯" n:60 => ofNat n

private example : ∅ ⊢ (.fn .unit .unit) := abs ♯0

def ext (ρ : ∀ {t}, Γ ∋ t → Δ ∋ t) (e : t :: Γ ⊢ t') : t :: Δ ⊢ t' :=
  match e with
  | unit => unit
  | var x =>
    match x with
    | .head =>
      var (Ctx.mem_head t)
    | .tail y =>
      var (Ctx.mem_tail (ρ y))
  | app e₀ e₁ =>
    app (ext ρ e₀) (ext ρ e₁)
  | abs e' =>
    have ρ' : ∀ {t''}, t :: Γ ∋ t'' → t :: Δ ∋ t'' :=
      fun {t''} ht'' =>
        match ht'' with
        | .head => Ctx.mem_head t
        | .tail z => Ctx.mem_tail (ρ z)
    abs (ext ρ' e')

def rename (ρ : ∀ {t}, Γ ∋ t → Δ ∋ t) (e : Γ ⊢ t) : Δ ⊢ t :=
  match e with
  | unit => unit
  | var x => var (ρ x)
  | app e₀ e₁ =>
    app (e₀.rename ρ) (e₁.rename ρ)
  | abs e =>
    abs (ext ρ e)

@[simp, grind =]
lemma rename_var (ρ : ∀ {t}, Γ ∋ t → Δ ∋ t) (x : Γ ∋ t) :
    rename ρ (var x) = var (ρ x) := by rfl
@[simp, grind =]
lemma rename_app (ρ : ∀ {t}, Γ ∋ t → Δ ∋ t) : rename ρ (app e₀ e₁) = app (e₀.rename ρ) (e₁.rename ρ) := by rfl
@[simp, grind =]
lemma rename_abs (ρ : ∀ {t}, Γ ∋ t → Δ ∋ t) : rename ρ (abs e) = abs (ext ρ e) := by rfl

abbrev weaken (x : Γ ∋ t) : t' :: Γ ∋ t := Ctx.mem_tail x

abbrev permute (x : t₀ :: t₁ :: Γ ∋ t) : t₁ :: t₀ :: Γ ∋ t :=
  match x with
  | .head =>
    .tail .head
  | .tail y =>
    match y with
    | .head => .head
    | .tail z => .tail <| .tail z

def exts (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t) (x : t :: Γ ∋ t') : t :: Δ ⊢ t' :=
  match x with
  | .head => var (Ctx.mem_head t)
  | .tail y =>
    rename weaken (σ y)

@[simp, grind =]
lemma exts_var_head (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t) : exts σ .head = var (Ctx.mem_head t) := by rfl
@[simp, grind =]
lemma exts_var_tail
  (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t)
  (y : Γ ∋ t') :
    exts σ (Ctx.Mem.tail y : t :: Γ ∋ t') = rename weaken (σ y) := by rfl

def subst (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t) (e : Γ ⊢ t) : Δ ⊢ t :=
  match e with
  | unit => unit
  | var x => σ x
  | app e₀ e₁ => app (subst σ e₀) (subst σ e₁)
  | @abs t₀ _ t₁ e' =>
    abs (subst (exts σ) e')

@[simp, grind =]
lemma subst_var (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t) (x : Γ ∋ t) : subst σ (var x) = σ x := by rfl
@[simp, grind =]
lemma subst_app (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t) : subst σ (app e₀ e₁) = app (subst σ e₀) (subst σ e₁) := by rfl
@[simp, grind =]
lemma subst_abs (σ : ∀ {t}, Γ ∋ t → Δ ⊢ t) : subst σ (abs e) = abs (subst (exts σ) e) := by rfl

def substSingle (e : t₀ :: Γ ⊢ t₁) (e' : Γ ⊢ t₀) : Γ ⊢ t₁ :=
  subst (σSingle e') e
  where
    σSingle {Γ t} (e : Γ ⊢ t) : ∀ {t'}, t :: Γ ∋ t' → Γ ⊢ t' :=
      fun {t'} x =>
        match x with
        | .head => e
        | .tail y => var y

notation:60 "[" e':60 "] " e:60 => substSingle e e'

@[simp, grind =]
lemma subst_single_var_head (e : Γ ⊢ t) : [e] (var Ctx.Mem.head) = e := by
  simp! [substSingle, substSingle.σSingle]
@[simp, grind =]
lemma subst_single_var_tail (e : Γ ⊢ t) : [e] (var (Ctx.Mem.tail y)) = var y := by
  simp! [substSingle, substSingle.σSingle]
@[simp, grind =]
lemma subst_single_app (e : Γ ⊢ t) : [e] (app e₀ e₁) = app ([e] e₀) ([e] e₁) := by simp [substSingle]

end

end Expr

