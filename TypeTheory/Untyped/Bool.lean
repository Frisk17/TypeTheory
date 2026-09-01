module

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

public inductive BExp where
  | true : BExp
  | false : BExp
  | ifElse : BExp → BExp → BExp → BExp
deriving Repr, DecidableEq, BEq

namespace BExp

public section

inductive Reduces₁ : BExp → BExp → Prop where
  | ifTrue : Reduces₁ (ifElse true t0 t1) t0
  | ifFalse : Reduces₁ (ifElse false t0 t1) t1
  | ifElse (h : Reduces₁ e e') :
      Reduces₁ (ifElse e t0 t1) (ifElse e' t0 t1)

scoped infix:40 " ⟶ " => Reduces₁

@[grind .]
lemma if_true_reduces_fst : Reduces₁ (BExp.ifElse BExp.true t0 t1) t0 := by
  apply Reduces₁.ifTrue

@[grind .]
lemma if_false_reduces_snd : Reduces₁ (BExp.ifElse BExp.false t0 t1) t1 := by
  apply Reduces₁.ifFalse

@[grind .]
lemma if_reduces_recursive (h : Reduces₁ e e') : Reduces₁ (BExp.ifElse e t0 t1) (BExp.ifElse e' t0 t1) := by
  apply Reduces₁.ifElse h

@[grind .]
theorem reduces_deterministic (h0 : Reduces₁ e e') (h1 : Reduces₁ e e'') : e' = e'' := by
  induction e generalizing e' e'' with
  | true | false => tauto
  | ifElse t0 t1 t2 hi0 hi1 hi2 =>
    cases h0 <;> cases h1 <;> try grind
    all_goals tauto

@[grind]
def reducible (e : BExp) := ∃e', e ⟶ e'

@[grind]
def normal (e : BExp) := ¬∃e', e ⟶ e'

@[grind .]
lemma reducible_iff_not_normal (e : BExp) : e.reducible ↔ ¬e.normal := by grind

@[grind .]
lemma normal_iff_not_reducible (e : BExp) : ¬e.reducible ↔ e.normal := by grind

@[grind .]
lemma normal_of_true : true.normal := by
  intro h; obtain ⟨ e', h ⟩ := h
  tauto

@[grind .]
lemma normal_of_false : false.normal := by
  intro h; obtain ⟨ e', h ⟩ := h
  tauto

@[grind .]
lemma value_of_normal (e : BExp) (h_normal : e.normal) : e = true ∨ e = false := by
  induction e with
  | true | false => simp
  | ifElse t0 t1 t2 hi0 hi1 hi2 =>
    suffices ifElse t0 t1 t2 |>.reducible from by
      grind
    cases t0 with
    | true =>
      use t1
      apply Reduces₁.ifTrue
    | false =>
      use t2
      apply Reduces₁.ifFalse
    | ifElse t0' t1' t2' =>
      by_cases h_normal' : t0'.ifElse t1' t2' |>.normal
      · grind
      · rw [←normal_iff_not_reducible, not_not] at h_normal'
        obtain ⟨ e', h_reduces ⟩ := h_normal'
        use e'.ifElse t1 t2
        apply Reduces₁.ifElse h_reduces

def Reduces := Relation.ReflTransGen Reduces₁

scoped infix:40 " ⟶⋆ " => Reduces

@[grind .]
lemma Reduces.refl (e : BExp) : e ⟶⋆ e := Relation.ReflTransGen.refl
@[grind .]
lemma Reduces.tail {e e' e'' : BExp} (hee' : e ⟶⋆ e') (he'e'' : e' ⟶ e'') : e ⟶⋆ e'' := Relation.ReflTransGen.tail hee' he'e''
@[grind .]
lemma Reduces.head {e e' e'' : BExp} (hee' : e ⟶ e') (he'e'' : e' ⟶⋆ e'') : e ⟶⋆ e'' := Relation.ReflTransGen.head hee' he'e''

@[grind .]
lemma Reduces.cases_head {a b : BExp} (hab : a ⟶⋆ b) :
    a = b ∨ ∃ c : BExp, a ⟶ c ∧ c ⟶⋆ b := by
  cases Relation.ReflTransGen.cases_head hab with
  | inl _ =>
    grind
  | inr hc =>
    right; obtain ⟨ c, hc ⟩ := hc
    use c
    constructor
    · grind
    · obtain ⟨ -, hc ⟩ := hc
      apply hc

theorem Reduces.induction
  {motive : (x : BExp) → (y : BExp) → (x ⟶⋆ y) → Prop}
  (refl : (a : BExp) → motive a a (by apply Relation.ReflTransGen.refl))
  (head : (a b c : BExp) → (hab : a ⟶ b) → (hbc : b ⟶⋆ c) → motive b c hbc → motive a c (Reduces.head hab hbc))
  (h : a ⟶⋆ b) :
    motive a b h := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => apply refl
  | @head x y hxy hyb hi => apply head x y b hxy hyb hi

theorem normal_unique
  (t u u' : BExp)
  (h : t ⟶⋆ u) (h' : t ⟶⋆ u')
  (h_normal : u.normal) (h_normal' : u'.normal) :
    u = u' := by
  induction h using Reduces.induction with
  | refl => grind
  | head a b c hab hbc hi =>
    cases Reduces.cases_head h' with
    | inl h'' => grind
    | inr h'' =>
      obtain ⟨ b', ⟨ hab', hcu' ⟩ ⟩ := h''
      grind

def eval₁ (t : BExp) (ht : t.reducible) : {t' // t ⟶ t'} :=
  match t with
  | true | false => by grind
  | ifElse a b c =>
    match _ : a with
    | true => ⟨ b, by grind ⟩
    | false => ⟨ c, by grind ⟩
    | ifElse _ _ _ =>
      let a' := eval₁ a (by grind)
      ⟨ ifElse ↑a' b c, by grind ⟩

@[grind .]
lemma eval₁_size (t : BExp) (ht : t.reducible) :
    SizeOf.sizeOf (eval₁ t ht).val < SizeOf.sizeOf t := by
  fun_induction eval₁ <;> grind

def decNormal (t : BExp) : Decidable (t.normal) :=
  match _ : t with
  | true => Decidable.isTrue (by grind)
  | false => Decidable.isTrue (by grind)
  | ifElse _ _ _ => Decidable.isFalse (by grind)

instance instDecidableNormal (t : BExp) : Decidable (t.normal) := decNormal t 

def eval (t : BExp) : {t' // t ⟶⋆ t'} :=
  if _ : t.normal then ⟨ t, by grind ⟩
  else
    have h_decreasing : SizeOf.sizeOf (eval₁ t (by grind)).val < SizeOf.sizeOf t := by apply eval₁_size
    ⟨ eval <| eval₁ t (by grind), by grind ⟩
termination_by t

end

end BExp

