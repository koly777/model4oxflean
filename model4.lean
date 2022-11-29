import model_theory.semantics
import data.list.prod_sigma
import model_theory.syntax
import tactic

universes u v w w'

namespace first_order
namespace language
open_locale first_order
open Structure
open cardinal

variables {L : language.{u v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The language consisting of two unary relations. -/
protected def unary_preds : language :=
language.mk₂ empty empty empty bool empty

def up₁ : language.unary_preds.relations 1 := tt
def up₂ : language.unary_preds.relations 1 := ff 

namespace unary_preds

instance : is_relational (language.unary_preds) := language.is_relational_mk₂

end unary_preds

protected def sentence.unary_card_ge (pred : language.unary_preds.relations 1) (n) : language.unary_preds.sentence :=
((((((list.fin_range n).product (list.fin_range n)).filter (λ ij : _ × _, ij.1 ≠ ij.2)).map
  (λ (ij : _ × _), ∼ ((& ij.1).bd_equal (& ij.2)))).foldr (⊓) ⊤) ⊓ 
  (((list.fin_range n).map (λ i, pred.bounded_formula ![var (sum.inr i)])).foldr (⊓) ⊤)).exs 

protected def sentence.not_unary_card_ge  (pred : language.unary_preds.relations 1) (n) : language.unary_preds.sentence :=
((((((list.fin_range n).product (list.fin_range n)).filter (λ ij : _ × _, ij.1 ≠ ij.2)).map
  (λ (ij : _ × _), ∼ ((& ij.1).bd_equal (& ij.2)))).foldr (⊓) ⊤) ⊓ 
  (((list.fin_range n).map (λ i, ∼ (pred.bounded_formula ![var (sum.inr i)]))).foldr (⊓) ⊤)).exs 

protected def sentence.unary_disjoint : language.unary_preds.sentence :=
∼ ((up₁.bounded_formula ![var (sum.inr 0)]) ⊓ (up₂.bounded_formula  ![var (sum.inr 0)])).ex

protected def Theory.disjoint_unary_preds : language.unary_preds.Theory := 
set.range (sentence.unary_card_ge up₁) ∪ set.range (sentence.unary_card_ge up₂) ∪ 
set.range (sentence.not_unary_card_ge up₁) ∪ set.range (sentence.not_unary_card_ge up₂) ∪ {sentence.unary_disjoint}

@[simp] lemma sentence.realize_unary_card_ge {M : Type u} [language.unary_preds.Structure M] (n) (pred) : 
M ⊨ sentence.unary_card_ge pred n ↔ ↑n ≤ cardinal.mk {x : M // rel_map pred ![x]} :=
begin
   rw [← lift_mk_fin, ← lift_le, lift_lift, lift_mk_le, sentence.unary_card_ge, sentence.realize,
    bounded_formula.realize_exs],
  split,
  rintro ⟨xs, h⟩,
  rw bounded_formula.realize_inf at h,
  cases h with hl hr,
  rw bounded_formula.realize_foldr_inf at hr,
  simp at hr,
  rw bounded_formula.realize_foldr_inf at hl,
  simp at hl,
  fconstructor,
  fconstructor,
  
  intro i,
  use (xs i),
  specialize hr i,
  rw ← matrix.vec_single_eq_const at hr,
  exact hr,
  intros i j ij,
  contrapose! ij,
  specialize hl _ i j ij rfl,
  simp at hl,
  simp,
  exact hl,

  intro xs,
  induction xs,
  induction xs,
  fconstructor,
  intros i,
  use (xs_to_fun i),
  rw bounded_formula.realize_inf,
  split,
  rw bounded_formula.realize_foldr_inf,
  simp,
  intros φ x x₁ h h₁,
  rw ← h₁,
  simp,
  rw function.injective at xs_inj',
  specialize @xs_inj' x x₁,
  contrapose! xs_inj',
  rw ne.def,
  split,
  ext1,
  exact xs_inj',
  exact h,

  rw bounded_formula.realize_foldr_inf,
  simp,
  intros a,
  rw ← matrix.vec_single_eq_const,
  rw ← subtype.val_eq_coe,
  cases (xs_to_fun a),
  simp,
  exact property,
end

@[simp] lemma sentence.realize_not_unary_card_ge {M : Type u} [language.unary_preds.Structure M] (n) (pred) : 
M ⊨ sentence.not_unary_card_ge pred n ↔ ↑n ≤ cardinal.mk {x : M // ¬(rel_map pred ![x])} :=
begin
   rw [← lift_mk_fin, ← lift_le, lift_lift, lift_mk_le, sentence.not_unary_card_ge, sentence.realize,
    bounded_formula.realize_exs],
  split,
  rintro ⟨xs, h⟩,
  rw bounded_formula.realize_inf at h,
  cases h with hl hr,
  rw bounded_formula.realize_foldr_inf at hr,
  simp at hr,
  rw bounded_formula.realize_foldr_inf at hl,
  simp at hl,
  fconstructor,
  fconstructor,
  
  intro i,
  use (xs i),
  specialize hr i,
  rw ← matrix.vec_single_eq_const at hr,
  exact hr,
  intros i j ij,
  contrapose! ij,
  specialize hl _ i j ij rfl,
  simp at hl,
  simp,
  exact hl,

  intro xs,
  induction xs,
  induction xs,
  fconstructor,
  intros i,
  use (xs_to_fun i),
  rw bounded_formula.realize_inf,
  split,
  rw bounded_formula.realize_foldr_inf,
  simp,
  intros φ x x₁ h h₁,
  rw ← h₁,
  simp,
  rw function.injective at xs_inj',
  specialize @xs_inj' x x₁,
  contrapose! xs_inj',
  rw ne.def,
  split,
  ext1,
  exact xs_inj',
  exact h,

  rw bounded_formula.realize_foldr_inf,
  simp,
  intros a,
  rw ← matrix.vec_single_eq_const,
  rw ← subtype.val_eq_coe,
  cases (xs_to_fun a),
  simp,
  exact property,
end

@[simp] lemma sentence.realize_unary_disjoint {M : Type u} [language.unary_preds.Structure M] :
M ⊨ sentence.unary_disjoint ↔ disjoint {x : M | rel_map up₁ ![x]} {x : M | rel_map up₂ ![x]} :=
begin
  rw sentence.unary_disjoint,
  rw sentence.realize,
  rw formula.realize,
  rw disjoint_iff,
  simp,
  rw set.eq_empty_iff_forall_not_mem,
  simp,
  simp_rw ← matrix.vec_single_eq_const,
  simp_rw fin.snoc,
  simp,
end

@[simp] lemma model_infinite_unary_pred_theory_iff {M : Type u} [language.unary_preds.Structure M] (pred) : 
M ⊨ (set.range (sentence.unary_card_ge pred)) ↔ infinite {x : M // rel_map pred ![x]} :=
begin
  simp,
  rw infinite_iff,
  rw aleph_0_le,
end

@[simp] lemma model_infinite_not_unary_pred_theory_iff {M : Type u} [language.unary_preds.Structure M] (pred) : 
M ⊨ (set.range (sentence.not_unary_card_ge pred)) ↔ infinite {x : M // ¬ (rel_map pred ![x])} :=
begin
  simp,
  rw infinite_iff,
  rw aleph_0_le,
end

end language
end first_order
