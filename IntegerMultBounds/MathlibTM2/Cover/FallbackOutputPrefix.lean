module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPaddingOutput

/-! The residual output accumulator in physical record order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {Q d W : ℕ} [NeZero Q]

/-- Look up the input bit at the inverse image of a live output address. -/
def imageWord (m : Matrix (Fin d) (Fin d) (ZMod Q)) (input : Fin (Q^d*W) → ZMod 2)
    (i : Fin (Q^d*W)) : ZMod 2 :=
  let pos := finProdFinEquiv.symm i
  input (index (m⁻¹.mulVec (coordinates pos.1)) pos.2)

theorem eq_imageWord (m : Matrix (Fin d) (Fin d) (ZMod Q)) (unit : IsUnit m.det)
    (input word : Fin (Q^d*W) → ZMod 2)
    (effect : ∀ x k, word (index (m.mulVec x) k) = input (index x k)) :
    word = imageWord m input := by
  funext i
  obtain ⟨⟨addr,k⟩,rfl⟩ := finProdFinEquiv.surjective i
  have h := effect (m⁻¹.mulVec (coordinates addr)) k
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv m unit,Matrix.one_mulVec] at h
  simpa [imageWord,index] using h

variable (active : ℕ → Bool) (matrix : ℕ → Matrix (Fin d) (Fin d) (ZMod Q))
  (input : ℕ → Fin (Q^d*W) → ZMod 2)

def outputRecord (j : ℕ) : List (Fin (prime+4)) :=
  payloadWord (SparseRoleCircuit.encode ∘ (if active j then imageWord (matrix j) (input j) else input j))

def outputPrefix (j : ℕ) (tail : List (Fin (prime+4))) :=
  ((List.range j).flatMap (outputRecord active matrix input)).reverse ++ tail

theorem outputPrefix_succ (j : ℕ) (tail : List (Fin (prime+4))) :
    outputPrefix active matrix input (j+1) tail =
      (outputRecord active matrix input j).reverse ++ outputPrefix active matrix input j tail := by
  simp [outputPrefix,List.range_succ,List.reverse_append,List.append_assoc]

theorem outputRecord_live {j : ℕ} (live : active j = true) (unit : IsUnit (matrix j).det)
    (word : Fin (Q^d*W) → ZMod 2)
    (effect : ∀ x k, word (index ((matrix j).mulVec x) k) = input j (index x k)) :
    outputRecord active matrix input j = payloadWord (SparseRoleCircuit.encode ∘ word) := by
  rw [eq_imageWord _ unit _ _ effect]
  simp [outputRecord,live]

local instance (b : ℕ) : NeZero (ActualAffineScaling.modulus b) := ⟨(ActualAffineScaling.modulus_pos b).ne'⟩

theorem outputRecord_padding {n b j : ℕ} (pad : active j = false)
    (m : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod (ActualAffineScaling.modulus b)))
    (bits : ℕ → Fin ((ActualAffineScaling.modulus b)^(n+1)*W) → ZMod 2) (array : Record.Array n 1 b W)
    (encoded : Record.scalarArray array = SparseRoleCircuit.encode ∘ bits j) :
    outputRecord active m bits j = payloadWord array := by
  simpa [outputRecord,pad,← encoded] using Record.payloadWord_scalarArray array

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
