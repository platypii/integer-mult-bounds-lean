import IntegerMultBounds.Machine.BinaryPackedRowCountPlaced

/-! Paid original-header fiber-count preparation and erasure are linear in the
number of fibers. Positive prefix/intervening dimensions are explicit. -/
namespace IntegerMultBounds.Machine.BinaryPackedRowCountBudget
open BinaryPackedRowCount (powerBits productBits rowBits)

private theorem length_le (xs : List Bool) (c : GrowingCounterData.Canonical xs) :
    xs.length ≤ Counter.value xs+1 :=
  (GrowingCounterData.canonical_width xs c).trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)

def cost (P w G : ℕ) :=
  FixedBasePowerDescriptor.constant 2*2^w+53*(P*2^w)+53*(P*2^w*G)+
    2*(powerBits w).length+2*(productBits P w).length+71

theorem bound (P w G : ℕ) (hP : 0 < P) (hG : 0 < G) :
    cost P w G ≤ (FixedBasePowerDescriptor.constant 2+110)*(P*2^w*G)+75 := by
  have hq : (powerBits w).length ≤ 2^w+1 := by
    rw [powerBits,PackedOffsetPowerHeader.power_bits]
    simpa only [RecursiveChildQuotientsConstant.bits_value] using
      length_le (RecursiveChildQuotientsConstant.bits (2^w)) (RecursiveChildQuotientsConstant.bits_canonical _)
  have hp : (productBits P w).length ≤ P*2^w+1 := by
    simpa only [productBits,DimensionProductDescriptor.bits_value] using
      length_le (DimensionProductDescriptor.bits P (2^w)) (DimensionProductDescriptor.bits_canonical _ _)
  have hPQ : P*2^w ≤ P*2^w*G := Nat.le_mul_of_pos_right _ hG
  have hQ : 2^w ≤ P*2^w*G := (Nat.le_mul_of_pos_left _ hP).trans hPQ
  have hc := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hQ
  unfold cost
  nlinarith

/-- Native fixed-control constructor with the bound in actual fiber count. -/
theorem constructs_linear {a : ℕ} (hs : Fin 4 → List Bool) (P w G : ℕ)
    (hP : 0 < P) (hG : 0 < G)
    (hp : Counter.value (hs 0)=P) (hg : Counter.value (hs 1)=G) (hw : Counter.value (hs 3)=w)
    (cp : GrowingCounterData.Canonical (hs 0)) (cg : GrowingCounterData.Canonical (hs 1))
    (cw : GrowingCounterData.Canonical (hs 3)) :
    HoareTime (BinaryPackedRowCount.program (a := a))
      (fun z => z=BinaryPackedRowCount.input hs) (fun z => z=BinaryPackedRowCount.output hs P w G)
      ((FixedBasePowerDescriptor.constant 2+110)*(P*2^w*G)+75) := by
  apply (BinaryPackedRowCount.constructs hs P w G hG hp hg hw cp cg cw).consequence
    (fun _ h => h) (fun _ h => h)
  change FixedBasePowerDescriptor.constant 2*2^w+53*(P*2^w)+53*(P*2^w*G)+
    (2*(powerBits w).length+2*(productBits P w).length+12)+59 ≤ _
  have hb := bound P w G hP hG
  dsimp only [cost] at hb
  omega

/-- Erasure charges the actual retained descriptor and returns its head zero. -/
theorem cleanup_bound (P w G : ℕ) :
    2*(rowBits P w G).length+4 ≤ 2*(P*2^w*G)+6 := by
  have hl := length_le (rowBits P w G) (BinaryPackedRowCount.row_canonical P w G)
  rw [BinaryPackedRowCount.row_value] at hl
  omega

end IntegerMultBounds.Machine.BinaryPackedRowCountBudget
