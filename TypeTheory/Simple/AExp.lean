module

import Mathlib.Tactic

public inductive Ty where
  | bool
  | nat
deriving Repr, DecidableEq

public inductive AExp : Ty → Type where
  | true : AExp Ty.bool
  | false : AExp Ty.bool
  | ifThen : AExp Ty.bool → AExp t → AExp t → AExp t
  | zero : AExp .nat
  | succ : AExp .nat → AExp .nat
  | pred : AExp .nat → AExp .nat
  | isZero : AExp .nat → AExp .bool
deriving Repr, DecidableEq

namespace AExp

public section

def sizeOf (t : AExp ty) : Nat :=
  match t with
  | true | false | zero => 0
  | ifThen e₀ e₁ e₂ => e₀.sizeOf + e₁.sizeOf + e₂.sizeOf + 1
  | succ n => n.sizeOf + 1
  | pred n => n.sizeOf + 1
  | isZero n => n.sizeOf + 1

instance : SizeOf (AExp ty) where
  sizeOf := sizeOf

@[simp, grind =]
lemma sizeOf_true : SizeOf.sizeOf true = 0 := by rfl
@[simp, grind =]
lemma sizeOf_false : SizeOf.sizeOf false = 0 := by rfl
@[simp, grind =]
lemma sizeOf_zero : SizeOf.sizeOf zero = 0 := by rfl
@[simp, grind =]
lemma sizeOf_ifThen : SizeOf.sizeOf (ifThen e₀ e₁ e₂) = SizeOf.sizeOf e₀ + SizeOf.sizeOf e₁ + SizeOf.sizeOf e₂ + 1 := by rfl
@[simp, grind =]
lemma sizeOf_succ : SizeOf.sizeOf (succ n) = SizeOf.sizeOf n + 1 := by rfl
@[simp, grind =]
lemma sizeOf_pred : SizeOf.sizeOf (pred n) = SizeOf.sizeOf n + 1 := by rfl
@[simp, grind =]
lemma sizeOf_isZero : SizeOf.sizeOf (isZero n) = SizeOf.sizeOf n + 1 := by rfl

inductive IsValue : AExp ty → Prop where
  | true : IsValue true
  | false : IsValue false
  | zero : IsValue zero
  | succ (n : AExp .nat) : IsValue n → IsValue (succ n)

@[grind .]
lemma is_value_true : true.IsValue := IsValue.true
@[grind .]
lemma is_value_false : false.IsValue := IsValue.false
@[grind .]
lemma is_value_zero : zero.IsValue := IsValue.zero
@[grind .]
lemma is_value_succ {n : AExp .nat} (hn : n.IsValue) : IsValue (succ n) := IsValue.succ n hn
@[grind .]
lemma not_is_value_if_else : ¬IsValue (ifThen a b c) := by
  intro h; cases h
@[grind .]
lemma not_is_value_is_zero : ¬IsValue (isZero n) := by
  intro h; cases h
@[grind .]
lemma not_is_value_pred : ¬IsValue (pred n) := by
  intro h; cases h
@[grind .]
lemma value_of_succ_value (h : IsValue (succ n)) : IsValue n := by
  cases h; trivial

abbrev Value ty := {t : AExp ty // t.IsValue}

@[grind .]
lemma is_value_succ' (n : Value .nat) : IsValue (succ n) := by
  apply is_value_succ n.prop

def eval (t : AExp ty) : Value ty :=
  match t with
  | true => ⟨ true, by grind ⟩
  | false => ⟨ false, by grind ⟩
  | ifThen condition e₀ e₁ =>
    let b := condition.eval
    match hb : (b : AExp .bool) with
    | true => ⟨ e₀.eval, by grind ⟩
    | false => ⟨ e₁.eval, by grind ⟩
    | ifThen _ _ _ => by grind
    | isZero _ => by grind
  | zero => ⟨ zero, by grind ⟩
  | pred n => evalPred n.eval
  | succ n => ⟨ succ n.eval, by grind ⟩
  | isZero n =>
    let m := n.eval
    match _ : (m : AExp .nat) with
    | zero => ⟨ true, by grind ⟩
    | succ m => ⟨ false, by grind ⟩
    | pred _ => by grind
    | ifThen _ _ _ => by grind
termination_by (SizeOf.sizeOf t)
decreasing_by all_goals grind
where
  evalPred (x : Value .nat) : Value .nat :=
    match _ : (x : AExp .nat) with
    | succ n => ⟨ n, by grind ⟩
    | zero => ⟨ zero, by grind ⟩ 
    | pred _ => by grind
    | ifThen _ _ _ => by grind

end

end AExp

