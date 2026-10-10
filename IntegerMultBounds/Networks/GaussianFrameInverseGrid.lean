import IntegerMultBounds.Networks.GaussianFrameGrid

/-! Exact inverse-frame grids for decoding actually stored network roles.
The budget follows from the literal inverse Walsh/phase operator. -/
namespace IntegerMultBounds.Networks.GaussianPrecision
open BinaryWalsh

theorem bounded_frame_inverse {h n M : ℕ} (q : Address h → ZMod 4)
    (f : Arrays h) (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid (n+h) (M*4^h) ((frame q).symm f x) := by
  have he := frame_edge q (fun _ => 0) f
  rw [frame_zero] at he
  rw [he]
  exact bounded_frame _ f hf

theorem bounded_tensor_phase_frame_inverse {h k n M : ℕ}
    (q : Address h → ZMod 4) (f : BinaryColumns.Arrays h k)
    (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid (n+k*h) (M*4^(k*h))
      (BinaryColumns.tensorColumns k (frame q).symm.toLinearMap f x) := by
  have hh := bounded_operator_prod
    (List.ofFn (fun j : Fin k => BinaryColumns.liftColumn j (frame q).symm.toLinearMap)) h
    (fun T hT n M f hf => by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hT
      intro x
      exact bounded_frame_inverse q (fun y => f (Function.update x j y))
        (fun y => hf (Function.update x j y)) (x j)) n M f hf
  simpa only [List.length_ofFn,BinaryColumns.tensorColumns] using hh

theorem bounded_rational_label_frame_inverse {h k n M : ℕ}
    (hs : (Labels.binary h).IsSymm) (U : Submodule (ZMod 2) (Address h))
    (f : BinaryColumns.Arrays h k) (hf : ∀ x,BoundedGrid n M (f x)) :
    ∀ x,BoundedGrid (n+k*h) (M*4^(k*h))
      ((BinaryColumnFrame.rationalLabelFrame hs k U).symm f x) :=
  bounded_tensor_phase_frame_inverse _ f hf

end IntegerMultBounds.Networks.GaussianPrecision
