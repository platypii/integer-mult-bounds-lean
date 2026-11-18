module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorLayout

/-! A constant padding record survives the anchor permutation for either sign. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {r d b W : ℕ}
local notation "M" => modulus b
local instance : NeZero M := ⟨(modulus_pos b).ne'⟩

theorem paddingOutput {N w : ℕ}
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (inputs : ℕ → Array d 1 b W) (outs : List (Array d 1 b W))
    (result : (signedInputs table w N inputs).Forall₂ Correct outs) (j : ℕ) (inside : j < N)
    (symbol : Fin 4) (padding : scalarArray (inputs j) = fun _ => symbol) :
    (outs.drop j).flatMap payloadWord = payloadWord (inputs j) ++ (outs.drop (j+1)).flatMap payloadWord := by
  have lo : j < (signedInputs table w N inputs).length := by simpa [signedInputs] using inside
  have hi : j < outs.length := result.length_eq ▸ lo
  let matrix := table (LabelStock.residue r w 1 j)
  let neg := negativeAnchor (classPivots matrix) matrix
  have correct : Correct (neg,inputs j) outs[j] := by
    simpa [neg,matrix,signedInputs,List.get_eq_getElem] using result.get lo hi
  have unchanged : scalarArray outs[j] = scalarArray (inputs j) := by
    funext pos
    obtain ⟨⟨addr,k⟩,rfl⟩ := finProdFinEquiv.surjective pos
    let x : Fin (d+1) → ZMod M := coordinates addr
    have eq := correct_scalar neg _ _ correct (signedAddress neg x) k
    rw [signedAddress_involutive,padding] at eq
    simpa [padding,index,x] using eq
  rw [← List.getElem_cons_drop hi,List.flatMap_cons,← payloadWord_scalarArray outs[j],unchanged,payloadWord_scalarArray]

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
