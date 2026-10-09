import IntegerMultBounds.Machine.UnitPhaseStreamData

/-! The physical stream endpoint is exactly the flattened coefficient array
obtained by applying the runtime full-address unit phase to each record.
Output serialization follows actual result widths, independent of reserved
payload padding or unrelated spectator cells. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ButterflyStreamData (Coefficient prefixTape position)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {n : ℕ}

def components (a : Coefficient) : ℕ → List (Fin 2) := fun j => if j=0 then a.1 else a.2
def result (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (xs : Fin n → Coefficient) (i : Fin n) : Coefficient :=
  let p := UnitPhaseRecordKernel.exponent v axis m ws (BinaryAddressTableData.row s.bits i.val)
  (UnitPhaseNumerator.words p 0 (components (xs i)),UnitPhaseNumerator.words p 1 (components (xs i)))

theorem sources (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) :
    UnitPhaseRecordRead.sources (UnitPhaseStreamData.contexts f p xs i.val)=components (xs i) := by
  funext j
  unfold UnitPhaseRecordRead.sources components
  rw [(UnitPhaseStreamData.components f p xs i.val i.isLt).1,
    (UnitPhaseStreamData.components f p xs i.val i.isLt).2]

theorem output_prefix (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin n → Coefficient) (tail : Tapes 4 2)
    (ho : tail.tape 2=g ∧ tail.head 2=r) (k : ℕ) (hk : k≤n) :
    (UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail k).tape 2=
      prefixTape g r (result v axis m ws xs) k ∧
    (UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail k).head 2=
      position r (result v axis m ws xs) k := by
  induction k with
  | zero => simpa [UnitPhaseStreamLoop.tails,ButterflyStreamData.prefixTape,ButterflyStreamData.position,
      CyclicRowCycle.rowPrefix,putWord] using ho
  | succ k ih =>
    have hi : k<n := by omega
    have h := ih (by omega)
    change putWord
      ((UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail k).tape 2)
      ((UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail k).head 2)
      (DelimitedRadixRecord.complex
        (UnitPhaseNumerator.words (UnitPhaseRecordKernel.exponent v axis m ws (BinaryAddressTableData.row s.bits k)) 0
          (UnitPhaseRecordRead.sources (UnitPhaseStreamData.contexts f p xs k)))
        (UnitPhaseNumerator.words (UnitPhaseRecordKernel.exponent v axis m ws (BinaryAddressTableData.row s.bits k)) 1
          (UnitPhaseRecordRead.sources (UnitPhaseStreamData.contexts f p xs k))))=_ ∧
      (UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail k).head 2+
        (UnitPhaseNumerator.words (UnitPhaseRecordKernel.exponent v axis m ws (BinaryAddressTableData.row s.bits k)) 0
          (UnitPhaseRecordRead.sources (UnitPhaseStreamData.contexts f p xs k))).length+
        (UnitPhaseNumerator.words (UnitPhaseRecordKernel.exponent v axis m ws (BinaryAddressTableData.row s.bits k)) 1
          (UnitPhaseRecordRead.sources (UnitPhaseStreamData.contexts f p xs k))).length+2=_
    rw [h.1,h.2,sources f p xs ⟨k,hi⟩]
    constructor
    · exact ButterflyStreamData.prefixTape_succ g r (result v axis m ws xs) ⟨k,hi⟩
    · exact (ButterflyStreamData.position_succ r (result v axis m ws xs) ⟨k,hi⟩).symm

end
end IntegerMultBounds.Machine.UnitPhaseStreamEndpoint
