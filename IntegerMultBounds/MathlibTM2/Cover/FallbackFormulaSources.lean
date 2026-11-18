module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaLayout

/-! One matrix reader serves the physical label, projector, zero, and one tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node
variable {ι : Type} {T m M A : ℕ} [NeZero M]

def sourceMap (matrixSlot : ι → Bool) : Leaf (Entry ι m) → Fin 7 ↪ Fin 10
  | .input (b,_,_) => if matrixSlot b then ⟨![0,1,7,3,4,5,6],by decide⟩ else Fin.castLEEmb (by decide)
  | .zero => ⟨![0,1,8,3,4,5,6],by decide⟩
  | .one => ⟨![0,1,9,3,4,5,6],by decide⟩

def sourcePorts (bank : Fin 10 ↪ Fin T) (matrixSlot : ι → Bool) (a : Leaf (Entry ι m)) : Fin 7 ↪ Fin T :=
  (sourceMap matrixSlot a).trans bank

theorem sourcePorts_ready (bank : Fin 10 ↪ Fin T) (matrixSlot : ι → Bool)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (R : Regs T A)
    (packed : ∀ b, ∃ tail, R (bank (if matrixSlot b then 7 else 2)) = matrixWords A H (mat b) ++ tail)
    (width : (R (bank 1)).length = H) (zeroWord : R (bank 8) = binSyms H 0)
    (oneWord : R (bank 9) = binSyms H (1 : ZMod M).val)
    (free : ∀ i : Fin 10, i ∈ [0,4,5,6] → R (bank i) = []) (a : Leaf (Entry ι m)) :
    leafReady (fun c _ => sourcePorts bank matrixSlot c) mat H a (sourcePorts bank matrixSlot a 3) R := by
  refine ⟨rfl,?_⟩
  cases a with
  | input x =>
    obtain ⟨b,i,j⟩ := x
    have h := packed b
    cases eq : matrixSlot b <;> simp only [eq,Bool.false_eq_true,ite_false,ite_true] at h <;>
      simp only [sourcePorts,sourceMap,eq,Bool.false_eq_true,ite_false,ite_true] <;>
      refine ⟨h,width,?_⟩ <;> intro k hk <;> fin_cases k <;> first | exact free _ (by decide) | contradiction
  | zero => exact ⟨by simpa [sourcePorts,sourceMap,Leaf.value] using zeroWord,free 4 (by decide),free 5 (by decide)⟩
  | one => exact ⟨oneWord,free 4 (by decide),free 5 (by decide)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
