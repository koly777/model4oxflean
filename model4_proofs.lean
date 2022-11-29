import model4_c
import model_theory.satisfiability

lemma not_iso_A_B : is_empty (first_order.language.equiv first_order.language.unary_preds (fin 3 × ℕ) (fin 2 × ℕ)) := 
begin
  rw is_empty_iff,
  intro f,
  induction f with fbij h₂ h₁,
  simp at *,
  have h₃ := h₁ (first_order.language.up₁),
  specialize h₁ (first_order.language.up₂),

  specialize h₃ ![(2, 1)],
  specialize h₁ ![(2, 1)],
  rw matrix.vec_single_eq_const at *,
  simp at *,
  rw ← function.const_def at *,
  rw ← matrix.vec_single_eq_const at *,
  rw ← matrix.vec_single_eq_const at *,
  generalize eq₁ : (fbij (2, 1)) = x,
  rw eq₁ at *,
  induction x,
  induction x_fst,
  cases x_fst_val,
  rw first_order.language.Structure.rel_map_apply₁ at *,
  rw first_order.language.Structure.rel_map_apply₁ at *,
  rw first_order.language.up₁ at *,
  rw first_order.language.up₂ at *,
  simp at *,
  injections_and_clear,
  norm_num at h_1,
  cases x_fst_val,
  rw first_order.language.Structure.rel_map_apply₁ at *,
  rw first_order.language.Structure.rel_map_apply₁ at *,
  rw first_order.language.up₁ at *,
  rw first_order.language.up₂ at *,
  simp at *,
  injections_and_clear,
  norm_num at *,
  simp at *,
  clear h₃ h₁ h₂,
  rw nat.succ_lt_succ_iff at *,
  rw nat.succ_lt_succ_iff at *,
  linarith,
end

example : ¬ (cardinal.categorical (cardinal.aleph_0) (first_order.language.Theory.disjoint_unary_preds)) := 
begin
  rw cardinal.categorical,
  simp,
  fconstructor,
  use ModelA,
  split,
  rw ModelA,
  simp,
  exact modelAℵ₀,
  use ModelB,
  split,
  exact modelBℵ₀,
  exact not_iso_A_B,
end