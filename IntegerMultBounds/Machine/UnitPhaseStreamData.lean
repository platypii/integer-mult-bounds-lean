import IntegerMultBounds.Machine.UnitPhaseFullStream
import IntegerMultBounds.Machine.ButterflyStreamData

/-! Actual phase coefficient contexts come from the literal flattened input
array. Only readable records require contexts; the terminal dummy is used
solely in the restored blank workspace and is never read by the machine. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamData
noncomputable section
open DelimitedRadixRecord (Context)
open ButterflyStreamData (Coefficient full position)
variable {n : ℕ}

def terminal (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) : Context 2 :=
  ⟨full f p xs,position p xs n,[],[],[],[]⟩
def contexts (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : ℕ) : Context 2 :=
  if h : i<n then ButterflyStreamData.context f p xs ⟨i,h⟩ else terminal f p xs

theorem tape (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : ℕ) (hi : i<n) :
    (contexts f p xs i).tape=full f p xs := by
  rw [contexts,dite_eq_left hi]
  exact ButterflyStreamData.context_tape _ _ _ _

theorem start (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : ℕ) (hi : i<n) :
    (contexts f p xs i).start=position p xs i := by
  rw [contexts,dite_eq_left hi]
  exact ButterflyStreamData.context_start _ _ _ _

theorem components (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : ℕ) (hi : i<n) :
    (contexts f p xs i).re=(xs ⟨i,hi⟩).1 ∧ (contexts f p xs i).im=(xs ⟨i,hi⟩).2 := by
  rw [contexts,dite_eq_left hi]
  exact ⟨rfl,rfl⟩

theorem adjacent (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) :
    ∀ i,i+1<n → (contexts f p xs (i+1)).tape=(contexts f p xs i).tape ∧
      (contexts f p xs (i+1)).start=(contexts f p xs i).start+
        (contexts f p xs i).re.length+(contexts f p xs i).im.length+2 := by
  intro i hi
  have hi' : i<n := by omega
  constructor
  · rw [tape _ _ _ _ hi,tape _ _ _ _ hi']
  · rw [start _ _ _ _ hi,start _ _ _ _ hi',
      (components f p xs i hi').1,(components f p xs i hi').2]
    exact ButterflyStreamData.position_succ p xs ⟨i,hi'⟩

theorem widths (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    ∀ i<n,(contexts f p xs i).re.length=w ∧ (contexts f p xs i).im.length=w := by
  intro i hi
  rw [(components f p xs i hi).1,(components f p xs i hi).2]
  exact hw _

end
end IntegerMultBounds.Machine.UnitPhaseStreamData
