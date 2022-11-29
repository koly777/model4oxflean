import model4 model_theory.bundled 

instance modelA : (first_order.language.unary_preds).Structure (fin 3 × ℕ) := 
first_order.language.Structure.mk₂ empty.elim empty.elim empty.elim 
(λ (b : bool), bool.rec {x : fin 3 × ℕ | x.fst = 0} {x : fin 3 × ℕ | x.fst = 1} b) empty.elim

instance modelB : (first_order.language.unary_preds).Structure (fin 2 × ℕ) := 
first_order.language.Structure.mk₂ empty.elim empty.elim empty.elim 
(λ (b : bool), bool.rec {x : fin 2 × ℕ | x.fst = 0} {x : fin 2 × ℕ | x.fst = 1} b) empty.elim

lemma modelA₁up₁ : (fin 3 × ℕ) ⊨ (set.range (first_order.language.sentence.unary_card_ge first_order.language.up₁)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₁,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 1,
  use x_snd + 1,
  simp,
end

lemma modelB₁up₁ : (fin 2 × ℕ) ⊨ (set.range (first_order.language.sentence.unary_card_ge first_order.language.up₁)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₁,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 1,
  use x_snd + 1,
  simp,
end

lemma modelA₂up₁ : (fin 3 × ℕ) ⊨ (set.range (first_order.language.sentence.not_unary_card_ge first_order.language.up₁)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₁,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 2,
  use x_snd + 1,
  simp,
  intro h,
  simp at h,
  injections_and_clear,
  simp at *,
  norm_num at h_1,
end

lemma modelB₂up₁ : (fin 2 × ℕ) ⊨ (set.range (first_order.language.sentence.not_unary_card_ge first_order.language.up₁)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₁,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 2,
  use x_snd + 1,
  simp,
  intro h,
  simp at h,
  injections_and_clear,
  simp at *,
  norm_num at h_1,
end

lemma modelA₃ : (fin 3 × ℕ) ⊨ (first_order.language.sentence.unary_disjoint) :=
begin
  simp,
  rw first_order.language.up₁,
  rw first_order.language.up₂,
  simp,
  rw disjoint_iff,
  simp,
  rw set.eq_empty_iff_forall_not_mem,
  simp,
end

lemma modelB₃ : (fin 2 × ℕ) ⊨ (first_order.language.sentence.unary_disjoint) :=
begin
  simp,
  rw first_order.language.up₁,
  rw first_order.language.up₂,
  simp,
  rw disjoint_iff,
  simp,
  rw set.eq_empty_iff_forall_not_mem,
  simp,
end

lemma modelA₁up₂ : (fin 3 × ℕ) ⊨ (set.range (first_order.language.sentence.unary_card_ge first_order.language.up₂)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₂,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 0,
  use x_snd + 1,
  simp,
end

lemma modelB₁up₂ : (fin 2 × ℕ) ⊨ (set.range (first_order.language.sentence.unary_card_ge first_order.language.up₂)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₂,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 0,
  use x_snd + 1,
  simp,
end

lemma modelA₂up₂ : (fin 3 × ℕ) ⊨ (set.range (first_order.language.sentence.not_unary_card_ge first_order.language.up₂)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₂,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 2,
  use x_snd + 1,
  simp,
  intro h,
  simp at h,
  injections_and_clear,
  simp at *,
  norm_num at h_1,
end

lemma modelB₂up₂ : (fin 2 × ℕ) ⊨ (set.range (first_order.language.sentence.not_unary_card_ge first_order.language.up₂)) :=
begin
  simp,
  refine set.infinite_coe_iff.mpr _,
  rw first_order.language.up₂,
  simp,
  refine set.infinite_of_not_bdd_above _,
  rw not_bdd_above_iff',
  intros x,
  induction x,
  fconstructor,
  fconstructor,
  use 1,
  use x_snd + 1,
  simp,
  intro h,
  simp at h,
  exact h
end

instance modelAT : (fin 3 × ℕ) ⊨ (first_order.language.Theory.disjoint_unary_preds) :=
begin
  rw first_order.language.Theory.disjoint_unary_preds,
  rw first_order.language.Theory.model_union_iff,
  rw first_order.language.Theory.model_union_iff,
  rw first_order.language.Theory.model_union_iff,
  rw first_order.language.Theory.model_union_iff,
  split,
  split,
  split,
  split,
  exact modelA₁up₁,
  exact modelA₁up₂,
  exact modelA₂up₁,
  exact modelA₂up₂,
  rw first_order.language.Theory.model_singleton_iff,
  exact modelA₃,
end


instance modelBT : (fin 2 × ℕ) ⊨ (first_order.language.Theory.disjoint_unary_preds) :=
begin
  rw first_order.language.Theory.disjoint_unary_preds,
  rw first_order.language.Theory.model_union_iff,
  rw first_order.language.Theory.model_union_iff,
  rw first_order.language.Theory.model_union_iff,
  rw first_order.language.Theory.model_union_iff,
  split,
  split,
  split,
  split,
  exact modelB₁up₁,
  exact modelB₁up₂,
  exact modelB₂up₁,
  exact modelB₂up₂,
  rw first_order.language.Theory.model_singleton_iff,
  exact modelB₃,
end

lemma modelAℵ₀ : cardinal.mk (fin 3 × ℕ) = cardinal.aleph_0 := 
begin
  rw ← cardinal.denumerable_iff,
  fconstructor,
  exact denumerable.of_encodable_of_infinite (fin 3 × ℕ),
end

lemma modelBℵ₀ : cardinal.mk (fin 2 × ℕ) = cardinal.aleph_0 := 
begin
  rw ← cardinal.denumerable_iff,
  fconstructor,
  exact denumerable.of_encodable_of_infinite (fin 2 × ℕ),
end

def ModelA : first_order.language.Theory.Model (first_order.language.Theory.disjoint_unary_preds) := 
{ carrier := fin 3 × ℕ }

def ModelB : first_order.language.Theory.Model (first_order.language.Theory.disjoint_unary_preds) := 
{ carrier := fin 2 × ℕ }