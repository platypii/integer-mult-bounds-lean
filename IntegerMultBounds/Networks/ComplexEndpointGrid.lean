import IntegerMultBounds.Networks.ComplexEndpoints
import IntegerMultBounds.Networks.GaussianPrecision

/-! Physical source and sink corrections preserve the exact denominator and
both integer numerator bounds. They require no additional precision reserve
before entering the raw grouped network or after completing it. -/
namespace IntegerMultBounds.Networks.GaussianPrecision
open BinaryWalsh ComplexEndpoints

 theorem bounded_character_mul {h n M : ℕ} (u x : BinaryWalsh.Address h)
    {z : ℂ} (hz : BoundedGrid n M z) : BoundedGrid n M (chi u x*z) := by
  unfold chi sign
  split_ifs
  · simpa using hz
  · simpa using bounded_neg hz

theorem bounded_character_product {ι : Type*} [DecidableEq ι] {h n M : ℕ}
    (s : Finset ι) (u : BinaryWalsh.Address h) (x : ι → BinaryWalsh.Address h)
    {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid n M ((∏ j ∈ s,chi u (x j))*z) := by
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,mul_assoc]
    exact bounded_character_mul u (x i) ih

theorem bounded_signColumns {h k n M : ℕ} (u : BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid n M (signColumns k u f x) := by
  intro x
  rw [signColumns_apply]
  exact bounded_character_product Finset.univ u x (hf x)

theorem bounded_I_pow_mul {n M : ℕ} (d : ℕ) {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid n M (Complex.I^d*z) := by
  induction d with
  | zero => simpa using hz
  | succ d ih =>
    rw [pow_succ',mul_assoc]
    exact bounded_I_mul ih

/-- Actual source signs preserve the original input grid for every named role,
including arbitrary dirty scratch arrays. -/
theorem bounded_correctInput {k n M : ℕ}
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k)
    (hg : ∀ wire address,BoundedGrid n M (stored wire address)) :
    ∀ wire address,BoundedGrid n M (correctInput k stored wire address) := by
  intro wire address
  rcases wire with b | b | s
  · exact bounded_signColumns (terminalVector b) _ (hg (Sum.inl b)) address
  · exact hg (Sum.inr (Sum.inl b)) address
  · exact hg (Sum.inr (Sum.inr s)) address

/-- Sink signs, runtime fourth-root phase, negation and physical bank exchange
leave the actual completed denominator and numerator reserve unchanged. -/
theorem bounded_correctOutput {k n M : ℕ}
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k)
    (hg : ∀ wire address,BoundedGrid n M (stored wire address)) :
    ∀ wire address,BoundedGrid n M (correctOutput k stored wire address) := by
  intro wire address
  rcases wire with b | b | s
  · change BoundedGrid n M (Complex.I^(27*k)*
      (signColumns k (terminalVector b) (stored (Sum.inr (Sum.inl b))) address))
    exact bounded_I_pow_mul (27*k)
      (bounded_signColumns (terminalVector b) _ (hg (Sum.inr (Sum.inl b))) address)
  · exact bounded_neg (hg (Sum.inl b) address)
  · exact hg (Sum.inr (Sum.inr s)) address

end IntegerMultBounds.Networks.GaussianPrecision
