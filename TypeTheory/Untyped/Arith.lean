module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

public inductive AExp where
  | true : AExp
  | false : AExp
  | ifElse : AExp → AExp → AExp → AExp
  | zero : AExp
  | succ : AExp → AExp
  | pred : AExp → AExp
  | isZero : AExp → AExp
deriving Repr, DecidableEq, BEq

namespace AExp

public section

instance instOfNat : OfNat AExp n where
  ofNat := helper n
    where
      helper : Nat → AExp
        | 0 => AExp.zero
        | m + 1 => AExp.succ <| helper m

@[simp, grind .]
def consts : AExp → Finset AExp
  | true => {true}
  | false => {false}
  | zero => {zero}
  | ifElse t0 t1 t2 => consts t0 ∪ consts t1 ∪ consts t2
  | succ t => consts t
  | pred t => consts t
  | isZero t => consts t

@[grind .]
lemma consts_subset_true_false_zero (e : AExp) :
    e.consts ⊆ {true, false, zero} := by induction e <;> grind

@[simp, grind .]
def size : AExp → Nat
  | true | false | zero => 1
  | ifElse t0 t1 t2 => 1 + size t0 + size t1 + size t2
  | succ t => 1 + size t
  | pred t => 1 + size t
  | isZero t => 1 + size t

def depth : AExp → Nat
  | true | false | zero => 1
  | ifElse t0 t1 t2 => 1 + [depth t0, depth t1, depth t2].max (by simp)
  | succ t => 1 + depth t
  | pred t => 1 + depth t
  | isZero t => 1 + depth t

lemma consts_card_le_size (e : AExp) : e.consts.card ≤ size e := by induction e <;> grind

inductive IsNumeric : AExp → Prop where
  | zero : IsNumeric 0
  | succ : IsNumeric e → IsNumeric (succ e)

@[grind .]
lemma zero_is_numeric : IsNumeric 0 := by apply IsNumeric.zero

@[grind .]
lemma succ_is_numeric (h : IsNumeric e) : IsNumeric (succ e) := by apply IsNumeric.succ h

@[grind .]
lemma cases_is_numeric (h : IsNumeric e) :
    e = 0 ∨ (∃ e', IsNumeric e' ∧ e = succ e') := by cases h <;> grind

inductive Reduces₁ : AExp → AExp → Prop where
  | ifTrue : Reduces₁ (ifElse true t0 t1) t0
  | ifFalse : Reduces₁ (ifElse false t0 t1) t1
  | ifElse (h : Reduces₁ e e') :
      Reduces₁ (ifElse e t0 t1) (ifElse e' t0 t1)
  | succ (h : Reduces₁ e e') : Reduces₁ (succ e) (succ e')
  | pred (h : Reduces₁ e e') : Reduces₁ (pred e) (pred e')
  | predZero : Reduces₁ (pred 0) 0
  | predSucc (h_numeric : IsNumeric e) : Reduces₁ (pred (succ e)) e
  | isZero (h : Reduces₁ e e') (h_numeric : IsNumeric e) : Reduces₁ (isZero e) (isZero e')
  | isZeroZero : Reduces₁ (isZero 0) true
  | isZeroSucc : Reduces₁ (isZero (succ e)) false

scoped infix:40 " ⟶ " => Reduces₁

@[grind .]
lemma if_true_reduces : AExp.ifElse AExp.true t0 t1 ⟶ t0 := by
  apply Reduces₁.ifTrue

@[grind .]
lemma if_false_reduces : AExp.ifElse AExp.false t0 t1 ⟶ t1 := by
  apply Reduces₁.ifFalse

@[grind .]
lemma if_else_reduces (h : e ⟶ e') : AExp.ifElse e t0 t1 ⟶ AExp.ifElse e' t0 t1 := by
  apply Reduces₁.ifElse h

@[grind .]
lemma succ_reduces (h : e ⟶ e') : AExp.succ e ⟶ AExp.succ e' := by apply Reduces₁.succ h

@[grind .]
lemma pred_reduces (h : e ⟶ e') : AExp.pred e ⟶ AExp.pred e' := by apply Reduces₁.pred h

@[grind .]
lemma pred_zero_reduces : AExp.pred 0 ⟶ 0 := by apply Reduces₁.predZero

@[grind .]
lemma pred_succ_reduces (h_numeric : e.IsNumeric) : AExp.pred (AExp.succ e) ⟶ e := by apply Reduces₁.predSucc h_numeric

@[grind .]
lemma is_zero_reduces (h : e ⟶ e') (h_numeric : e.IsNumeric) : AExp.isZero e ⟶ AExp.isZero e' := by apply Reduces₁.isZero h h_numeric

@[grind .]
lemma is_zero_zero : AExp.isZero 0 ⟶ true := by apply Reduces₁.isZeroZero

@[grind .]
lemma is_zero_succ : AExp.isZero (AExp.succ e) ⟶ false := by apply Reduces₁.isZeroSucc

@[grind]
def reducible (e : AExp) := ∃e', e ⟶ e'

@[grind]
def normal (e : AExp) := ¬∃e', e ⟶ e'

@[grind .]
lemma reducible_iff_not_normal (e : AExp) : e.reducible ↔ ¬e.normal := by grind

@[grind .]
lemma normal_iff_not_reducible (e : AExp) : ¬e.reducible ↔ e.normal := by grind

@[grind .]
lemma normal_of_true : true.normal := by
  intro h; obtain ⟨ e', h ⟩ := h
  tauto

@[grind .]
lemma normal_of_false : false.normal := by
  intro h; obtain ⟨ e', h ⟩ := h
  tauto

@[grind .]
lemma normal_zero : zero.normal := by
  intro h; obtain ⟨ e, h ⟩ := h
  tauto

@[grind .]
lemma normal_numeric (e : AExp) (h_numeric : e.IsNumeric) : e.normal := by
  induction h_numeric with
  | zero => apply normal_zero
  | @succ e' h h' =>
    intro ⟨ e'', h'' ⟩
    cases h''; grind

@[grind .]
theorem reduces_deterministic (h0 : e ⟶ e') (h1 : e ⟶ e'') : e' = e'' := by
  induction e generalizing e' e'' with
  | true | false | zero => tauto
  | ifElse t0 t1 t2 hi0 hi1 hi2 =>
    cases h0 <;> cases h1 <;> try grind
    all_goals tauto
  | isZero t hi =>
    cases h0 <;> cases h1 <;> try tauto
    case isZeroSucc a b hba hb =>
      have h_reducible : b.succ.reducible := by use a
      grind
    case isZero a b hab ha =>
      have h_reducible : a.succ.reducible := by use b
      grind
  | succ t => cases h0; cases h1; grind
  | pred t hi =>
    cases h0 <;> cases h1 <;> try tauto
    case predSucc a he'' he''a =>
      have h_reducible : e''.succ.reducible := by use a
      grind
    case pred he' b he'b =>
      have h_reducible : e'.succ.reducible := by use b
      grind

end

end AExp

