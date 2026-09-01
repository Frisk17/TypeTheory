module

import Mathlib.Tactic

public inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | abs : Term → Term
deriving Repr

namespace Term

public section

def shift (t : Term) (k c : Nat) : Term :=
  match t with
  | var m =>
    if m ≥ c then var <| m + k
    else var m
  | app t0 t1 => app (shift t0 k c) (shift t1 k c)
  | abs t' => abs <| shift t' k (c + 1)

@[simp, grind .]
lemma shift_var_ge (k c : Nat) (hm : m ≥ c) : (var m).shift k c = var (m + k) := by grind [shift]

@[simp, grind .]
lemma shift_var_lt (k c : Nat) (hm : m < c) : (var m).shift k c = var m := by grind [shift]

@[simp, grind .]
lemma shift_app (k c : Nat) (t0 t1 : Term) : (app t0 t1).shift k c = app (t0.shift k c) (t1.shift k c) := by grind [shift]

@[simp, grind .]
lemma shift_abs (k c : Nat) (t : Term) : (abs t).shift k c = abs (t.shift k (c + 1)) := by grind [shift]

@[simp, grind .]
lemma shift_comp (k k' c : Nat) (t : Term) : (t.shift k c).shift k' c = t.shift (k + k') c := by
  induction t generalizing c <;> grind

lemma shift_commute (k k' c c' : Nat) (t : Term) (hcc' : c ≤ c') : (t.shift k' c').shift k c = (t.shift k c).shift k' (c' + k) := by
  induction t generalizing c c' with
  | var x =>
    by_cases hxc' : x ≥ c' <;> by_cases hxc : x ≥ c
    any_goals linarith
    all_goals grind
  | _ => grind

@[simp, grind .]
lemma shift_zero (t : Term) : (t.shift 0 c) = t := by fun_induction shift <;> grind

inductive Unshiftable : Term → Nat → Nat  → Prop where
  | var_lt (x : Nat) (h_lt : x < c) : Unshiftable (var x) k c
  | var_ge (x : Nat) (h_ge : x ≥ c + k) : Unshiftable (var x) k c
  | app (h0 : Unshiftable t0 k c) (h1 : Unshiftable t1 k c) : Unshiftable (app t0 t1) k c
  | abs (ht : Unshiftable t k (c + 1)) : Unshiftable (abs t) k c

@[grind .]
lemma unshiftable_of_var_lt (x : Nat) (h_lt : x < c) : Unshiftable (var x) k c := Unshiftable.var_lt x h_lt

@[grind .]
lemma unshiftable_of_var_ge (x : Nat) (h_ge : x ≥ c + k) : Unshiftable (var x) k c := Unshiftable.var_ge x h_ge

@[grind .]
lemma unshiftable_app_of_unshiftable (h0 : Unshiftable t0 k c) (h1 : Unshiftable t1 k c) : Unshiftable (app t0 t1) k c := Unshiftable.app h0 h1

@[grind .]
lemma unshiftable_abs_of_unshiftable (ht : Unshiftable t k (c + 1)) : Unshiftable (abs t) k c := Unshiftable.abs ht

@[grind .]
lemma lt_or_ge_of_unshiftable_var (x : Nat) (hx : (var x).Unshiftable k c) : x < c ∨ x ≥ c + k := by cases hx <;> grind

@[grind .]
lemma unshiftable_of_unshiftable_app₀ (h : (app t0 t1).Unshiftable k c) : t0.Unshiftable k c := by cases h; assumption

@[grind .]
lemma unshiftable_of_unshiftable_app₁ (h : (app t0 t1).Unshiftable k c) : t1.Unshiftable k c := by cases h; assumption

@[grind .]
lemma unshiftable_of_unshiftable_abs (h : (abs t).Unshiftable k c) : t.Unshiftable k (c + 1) := by cases h; assumption

def unshift (t : Term) (k c : Nat) : Term :=
  match t with
  | var m =>
    if m ≥ c then var <| m - k
    else var m
  | app t0 t1 => app (unshift t0 k c) (unshift t1 k c)
  | abs t' => abs <| unshift t' k (c + 1)

notation:70 "↑¹ " t:60 => shift t 1 0
notation:70 "↑⁻¹ " t:60 => unshift t 1 0

@[simp, grind .]
lemma unshift_var_ge (h_ge : m ≥ c) : (var m).unshift k c = var (m - k) := by unfold unshift; rw [if_pos h_ge]

@[simp, grind .]
lemma unshift_var_lt (h_lt : m < c) : (var m).unshift k c = var m := by unfold unshift; rw [if_neg (by rw [Nat.not_le]; assumption)]

@[simp, grind .]
lemma unshift_app : (app t0 t1).unshift k c = app (t0.unshift k c) (t1.unshift k c) := by rfl

@[simp, grind .]
lemma unshift_abs : (abs t).unshift k c = abs (t.unshift k (c + 1)) := by rfl

@[grind .]
lemma unshiftable_of_shift (t : Term) : t.shift k c |>.Unshiftable k c := by fun_induction shift <;> grind

@[grind .]
lemma unshiftable_of_shift' (t : Term) : (t.shift (k + 1) i).Unshiftable 1 (k + i) := by induction t generalizing k i <;> grind

@[grind .]
lemma unshiftable_of_shift₀
  (t : Term) :
    (t.shift (k + 1 + i) j).Unshiftable (k + 1) (i + j) := by
  induction t generalizing i j
  all_goals grind

@[simp, grind .]
lemma unshift_shift_eq_self {t : Term} : unshift (shift t k c) k c = t := by
  induction t generalizing c <;> grind

@[simp, grind .]
lemma shift_unshift_eq_self (ht : t.Unshiftable k c) : shift (unshift t k c) k c = t := by
  induction t generalizing c <;> grind

lemma eq_shift_of_unshiftable {t : Term} (h : t.Unshiftable k c) :
    ∃ t' : Term, t = t'.shift k c := by
  induction h with
  | @var_lt c k x lt => use (var x); simp [*]
  | @var_ge c k x ge => use (var (x - k)); grind
  | app t0 t1 ht0 ht1 =>
    obtain ⟨ t0', ht0 ⟩ := ht0
    obtain ⟨ t1', ht1 ⟩ := ht1
    use (app t0' t1')
    simp [*]
  | abs t ht =>
    obtain ⟨ t', ht ⟩ := ht
    use t'.abs
    simp [*]

noncomputable def witness_shift_of_unshiftable {t : Term} (h : t.Unshiftable k c) : {t' : Term // t = t'.shift k c} := by
  let t' := eq_shift_of_unshiftable h |>.choose
  refine ⟨ t', by grind ⟩

def subst (t : Term) (x : Nat) (t' : Term) :=
  match t with
  | var y =>
    if x = y then t'
    else t
  | app t0 t1 =>
    app (subst t0 x t') (subst t1 x t')
  | abs t'' =>
    abs (subst t'' (x + 1) (↑¹ t'))

notation:60 "[ " x:61 " := " t:61 " ] " t':60 => subst t' x t

@[simp, grind .]
lemma subst_var_eq (t : Term) (x : Nat) : [ x := t ] (var x) = t := by simp [subst]

@[simp, grind .]
lemma subst_var_neq (t : Term) (x y : Nat) (h : x ≠ y) : [ x := t ] (var y) = var y := by simp [subst]; grind

@[simp, grind .]
lemma subst_app (t0 t1 t : Term) : [ x := t ] (app t0 t1) = app ([ x := t ] t0) ([ x := t ] t1) := by rfl

@[simp, grind .]
lemma subst_abs (t t' : Term) (x : Nat) : [ x := t' ] (abs t) = abs ([ x + 1 := ↑¹ t' ] t) := by rfl

lemma subst_unshift
  (t t' : Term) (hx : x ≥ c) (ht : t.Unshiftable k c) :
    [ x := t' ] (t.unshift k c) = ([ x + k := t'.shift k c ] t).unshift k c := by
  have ⟨ e, he ⟩ := witness_shift_of_unshiftable ht
  rw [he]; clear he ht t
  induction e generalizing x t' c with
  | var y => grind
  | app t0 t1 ht0 ht1 => simp [*]; grind
  | abs t ht =>
    simp [*]
    specialize @ht (x + 1) (c + 1) (↑¹ t') (by linarith)
    rw [unshift_shift_eq_self, add_assoc, add_comm 1, ←add_assoc, ←shift_commute] at ht
    · grind
    · linarith

lemma subst_unshiftable_eq_self
  (t t' : Term) (ht : t.Unshiftable (k + 1) j) :
    [ k + j := t'.shift j 0 ] t = t := by
  have ⟨ t, ht ⟩ := t.witness_shift_of_unshiftable ht
  subst_eqs; clear ht
  induction t generalizing j with
  | var x => grind
  | app t0 t1 ht0 ht1 => simp [*]
  | abs t ht =>
    simp [*]
    specialize @ht (j + 1)
    grind

@[grind .]
lemma unshiftable_of_subst (i : Nat) (t t' : Term) :
    ([ i := t'.shift (i + 1) 0 ] t).Unshiftable 1 i := by
  induction t generalizing i with
  | var x => by_cases h : i = x <;> (simp [*]; grind [unshiftable_of_shift'])
  | _ => grind

@[grind .]
lemma subst_shift_eq_self
  (t t' : Term) : [ c := t' ] (shift t 1 c) = shift t 1 c := by
    induction t generalizing c t' with
    | app t0 t1 ht0 ht1 => simp_all
    | _ => simp [shift]; grind

lemma shift_shift_yay (p : Term) (i j k : Nat) : (p.shift j k).shift i (j + k) = p.shift (i + j) k := by
  induction p generalizing k <;> grind

lemma shift_subst_eq_subst_shift
  (p q : Term) :
    ([ x + j := p.shift j 0 ] q).shift i j = [ x + i + j := p.shift (i + j) 0 ] q.shift i j := by
  induction q generalizing j with
  | var y =>
    by_cases hxjy : x + j = y <;> by_cases hy : y ≥ j <;> simp [*]
    any_goals linarith
    any_goals grind
    subst_eqs
    rw [add_assoc x j i, add_comm j i, ←add_assoc]
    simp [*]
    apply shift_shift_yay
  | _ => grind

lemma shift_subst_eq_subst_shift₀
  (p q : Term) :
    ([ x := p ] q).shift i 0 = [ x + i := p.shift i 0 ] q.shift i 0 := by
  rw [←@shift_zero 0 p, ←Nat.add_zero x,
    Nat.add_assoc, Nat.add_comm 0, ←Nat.add_assoc]
  rw [shift_subst_eq_subst_shift]
  simp

lemma subst_commute
  (p q t : Term)
  (hp : p.Unshiftable (y + 1) 0)
  (hxy : x ≠ y) :
    [ x + i := p.shift i 0 ] [ y + i := q.shift i 0 ] t = [ y + i := ([ x := p ] q).shift i 0 ] [ x + i := p.shift i 0 ] t := by
  induction t generalizing p q i with
  | var z =>
    by_cases hxz : x + i = z <;> by_cases hyz : y + i = z <;> try simp [*] <;> subst_eqs
    · grind only
    · rw [subst_unshiftable_eq_self]
      have ⟨ r, hr ⟩ := p.witness_shift_of_unshiftable hp
      clear hp
      subst_eqs; simp
      apply unshiftable_of_shift₀
    · rw [shift_subst_eq_subst_shift₀]
  | app t0 t1 ht0 ht1 => grind
  | abs t ht => simp [*]; grind

lemma subst_commute₀
  (p q t : Term)
  (hp : p.Unshiftable 1 0)
  (hx : x ≠ 0) :
    [ x := p ] [ 0 := q ] t = [ 0 := ([ x := p ] q) ] [ x := p ] t := by
  conv =>
    lhs
    rw [←Nat.add_zero x]
    rw [←@shift_zero 0 p]
    arg 1
    rw [←Nat.add_zero 0]
    rw [←@shift_zero 0 q]
  conv =>
    rhs
    rw [←Nat.add_zero 0]
    arg 1
    rw [←Nat.add_zero x]
    rw [←@shift_zero 0 p]
  rw [subst_commute p q t hp hx]
  grind

end

end Term

