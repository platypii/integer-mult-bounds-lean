import IntegerMultBounds.Networks.GaussianBoundedArithmetic
import IntegerMultBounds.Networks.BinaryColumnFrame

/-! Every actual binary phase frame has an explicit grid bound, without a
residual-factor certificate or nondegeneracy premise. This applies to the
role-specific frames retained by the actual grouped network compiler. -/
namespace IntegerMultBounds.Networks.GaussianPrecision
open BinaryWalsh

 theorem bounded_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (n M : ℕ)
    (hf : ∀ i ∈ s,BoundedGrid n M (f i)) : BoundedGrid n (s.card*M) (∑ i ∈ s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero n 0
  | @insert i s hi ih =>
    have h := bounded_add (hf i (Finset.mem_insert_self ..))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

theorem bounded_div_pow_two {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) (d : ℕ) :
    BoundedGrid (n+d) M (z/(2:ℂ)^d) := by
  induction d with
  | zero => simpa using hz
  | succ d ih =>
    rw [pow_succ,div_mul_eq_div_div]
    exact bounded_half ih

theorem bounded_walsh {h n M : ℕ} (f : Arrays h) (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid n (2^h*M) (walsh h f x) := by
  intro x
  have hs := bounded_finset_sum Finset.univ (fun y => chi x y*f y) n M (fun y _ => by
    unfold chi sign
    split_ifs
    · simpa using hf y
    · simpa using bounded_neg (hf y))
  simpa only [Finset.card_univ,address_card,walsh_apply] using hs

theorem bounded_frame {h n M : ℕ} (q : Address h → ZMod 4) (f : Arrays h)
    (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid (n+h) (M*4^h) (frame q f x) := by
  have h0 := bounded_walsh f hf
  have h1 : ∀ x,BoundedGrid (n+h) (2^h*M) ((walshEquiv h).symm f x) := by
    intro x
    change BoundedGrid (n+h) (2^h*M) ((volume h)⁻¹*walsh h f x)
    simpa only [volume,div_eq_mul_inv,mul_comm] using bounded_div_pow_two (h0 x) h
  have h2 := bounded_walsh (BinaryPhase.phaseDiagonal q ((walshEquiv h).symm f))
    (fun x => bounded_phase_mul (q x) (h1 x))
  intro x
  have he : 2^h*(2^h*M)=M*4^h := by
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,show 2*h=h+h by omega,pow_add]
    ring
  simpa only [frame_apply,he] using h2 x

theorem bounded_tensor_phase_frame {h k n M : ℕ} (q : Address h → ZMod 4)
    (f : BinaryColumns.Arrays h k) (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid (n+k*h) (M*4^(k*h))
      (BinaryColumns.tensorColumns k (frame q).toLinearMap f x) := by
  have hh := bounded_operator_prod
    (List.ofFn (fun j : Fin k => BinaryColumns.liftColumn j (frame q).toLinearMap)) h
    (fun T hT n M f hf => by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hT
      intro x
      exact bounded_frame q (fun y => f (Function.update x j y))
        (fun y => hf (Function.update x j y)) (x j)) n M f hf
  simpa only [List.length_ofFn,BinaryColumns.tensorColumns] using hh

theorem bounded_rational_label_frame {h k n M : ℕ} (hs : (Labels.binary h).IsSymm)
    (U : Submodule (ZMod 2) (Address h))
    (f : BinaryColumns.Arrays h k) (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid (n+k*h) (M*4^(k*h)) (BinaryColumnFrame.rationalLabelFrame hs k U f x) :=
  bounded_tensor_phase_frame _ f hf

end IntegerMultBounds.Networks.GaussianPrecision
