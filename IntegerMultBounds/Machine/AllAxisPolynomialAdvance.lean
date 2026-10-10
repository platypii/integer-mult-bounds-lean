import IntegerMultBounds.Machine.AllAxisPolynomialFull

/-! Exact next-source and next-counter boundary of the actual polynomial
body. The boundary uses the last real coefficient, never a terminal read. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialAdvance
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open AllAxisPolynomialFull (nextTail)
variable {s : Shape}

theorem counter (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    (nextTail order v rows m ws i z ctx R).tape 1=
      CountedLoopReuseAlphabet.binary (BinaryAddressTableData.row s.bits (i+1)) ∧
    (nextTail order v rows m ws i z ctx R).head 1=1 := by
  exact ⟨rfl,rfl⟩

theorem count (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    (nextTail order v rows m ws i z ctx R).tape 3=z.tape 3 ∧
    (nextTail order v rows m ws i z ctx R).head 3=z.head 3 := by
  exact ⟨rfl,rfl⟩

theorem source (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) (hR : 0<R) :
    (nextTail order v rows m ws i z ctx R).tape 0=(ctx (R-1)).tape ∧
    (nextTail order v rows m ws i z ctx R).head 0=
      (ctx (R-1)).start+(ctx (R-1)).re.length+(ctx (R-1)).im.length+2 := by
  let b := AllAxisPolynomialRecord.prepared order v rows m ws
    (BinaryAddressTableData.row s.bits i) (AllAxisPolynomialFull.advanced s.bits i z)
  let p := AllAxisPhaseFlagsCaller.phase v m ws (BinaryAddressTableData.row s.bits i)
  have hf := AllAxisPolynomialRecord.prepared_flags order v rows m ws
    (BinaryAddressTableData.row s.bits i) (AllAxisPolynomialFull.advanced s.bits i z)
  have hc := AllAxisPolynomialRecord.prepared_core order v rows m ws
    (BinaryAddressTableData.row s.bits i) (AllAxisPolynomialFull.advanced s.bits i z)
  have hs : UnitPhasePolynomialLoop.state b ctx p R=
      UnitPhaseSharedCoefficient.streamOutput (UnitPhasePolynomialLoop.state b ctx p (R-1)) (ctx (R-1)) p := by
    conv_lhs => rw [show R=(R-1)+1 by omega]
    rw [UnitPhasePolynomialLoop.state,UnitPhaseSharedCoefficient.output_eq _ _ _
      (UnitPhasePolynomialLoop.state_flags b ctx p hf (R-1))
      (UnitPhasePolynomialLoop.state_core b ctx p hc (R-1))]
  change (UnitPhasePolynomialLoop.state b ctx p R).tape 56=_ ∧
    (UnitPhasePolynomialLoop.state b ctx p R).head 56=_
  rw [hs]
  simp [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape]

end
end IntegerMultBounds.Machine.AllAxisPolynomialAdvance
