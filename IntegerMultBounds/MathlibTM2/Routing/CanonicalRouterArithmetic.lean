module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageArithmetic
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry

/-! One logarithmic gap and reservoir-compatible stride supply all arithmetic
bounds of every residue profile. The scale is the original record width plus one. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Layer.CompactDigits
noncomputable section

def canonicalRouterGap (n : ℕ) : ℕ := 6 + 4 * Nat.clog 2 (n + 2)

def canonicalRouterStride (n : ℕ) : ℕ := 64 * canonicalRouterGap n

theorem canonicalRouterGap_pos (n : ℕ) : 0 < canonicalRouterGap n := by
  unfold canonicalRouterGap
  omega

theorem canonicalRouter_radix (n : ℕ) : 64 * (n + 1) ^ 4 ≤ 2 ^ canonicalRouterGap n := by
  have hlog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 2) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) (n + 2))
  have hpow := Nat.pow_le_pow_left hlog 4
  have he : 2 ^ canonicalRouterGap n = 64 * (2 ^ Nat.clog 2 (n + 2)) ^ 4 := by
    unfold canonicalRouterGap
    rw [Nat.mul_comm 4 (Nat.clog 2 (n + 2)), pow_add, pow_mul]
    norm_num
  rw [he]
  exact Nat.mul_le_mul_left 64 hpow

theorem canonicalRouter_gap (n : ℕ) :
    1024 * (n + 1) ^ 4 ≤ 2 ^ (canonicalRouterStride n - 1 - canonicalRouterGap n) := by
  have hg : 6 ≤ canonicalRouterGap n := by unfold canonicalRouterGap; omega
  have hexp : canonicalRouterGap n + 4 ≤ canonicalRouterStride n - 1 - canonicalRouterGap n := by
    unfold canonicalRouterStride
    omega
  have hr := Nat.mul_le_mul_left 16 (canonicalRouter_radix n)
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) hexp
  rw [pow_add] at hp
  norm_num at hp
  nlinarith

theorem routerDigits_le_width (n K G : ℕ) : routerDigits n K G ≤ n :=
  (Nat.div_le_self (n - K) (K + 3 * G)).trans (Nat.sub_le n K)

theorem canonicalRouterSlots_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    p.n ≤ n ∧ p.n * p.G ≤ n := by
  dsimp only
  refine ⟨routerDigits_le_width n _ _, ?_⟩
  have ht := routerProfileParameters_total n (canonicalRouterStride n) (canonicalRouterGap n) hn r
  change 3 * ((routerProfileParameters n (canonicalRouterStride n)
    (canonicalRouterGap n) r.val).n * (routerProfileParameters n (canonicalRouterStride n)
    (canonicalRouterGap n) r.val).G) + _ = n at ht
  omega

/-- Canonical geometry bounds every descriptor family by one linear magnitude. -/
theorem canonicalRouterDescriptorMagnitude_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    liveDescriptorMagnitude
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val) 0 repairLiveMode ≤ 4 * n + 1 := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have hm := liveDescriptorMagnitude_le p 0 repairLiveMode
  have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
  have hd : p.n ≤ n := routerDigits_le_width n _ _
  have hk : p.K ≤ n := hn
  have hg : p.G ≤ n := by
    change canonicalRouterGap n ≤ n
    unfold canonicalRouterStride at hn
    omega
  change liveDescriptorMagnitude p 0 repairLiveMode ≤ _
  change liveDescriptorMagnitude p 0 repairLiveMode ≤
    p.G + p.K + p.n + p.wc + p.wy + 2 * p.wc + 0 + 1 at hm
  omega

/-- One logarithmic index width works for every canonical residue. -/
theorem canonicalRouterIndexBits_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).indexBits ≤
      Nat.clog 2 (4 * n + 2) + 1 := by
  change Nat.clog 2 (liveDescriptorMagnitude _ 0 repairLiveMode + 1) + 1 ≤ _
  apply Nat.add_le_add_right
  apply Nat.clog_mono_right
  have hm := canonicalRouterDescriptorMagnitude_le n hn r
  omega

/-- Affine coordinate and selector words use at most twice the common index budget. -/
theorem canonicalRouterCoordinateBits_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).coordinateBits ≤
      2 * (Nat.clog 2 (4 * n + 2) + 1) := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let L := Nat.clog 2 (liveDescriptorMagnitude p 0 repairLiveMode + 1)
  have hi := canonicalRouterIndexBits_le n hn r
  change L + 1 ≤ Nat.clog 2 (4 * n + 2) + 1 at hi
  change (L + 1) + L ≤ _
  omega

/-- Every numeric fit of a complete canonical input is now constructed for the
actual router residue parameters; no per-profile arithmetic package is assumed. -/
def canonicalRouterArithmetic (n : ℕ) (r : Fin (canonicalRouterStride n))
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    CanonicalStageArithmetic (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val) := by
  apply canonicalStageArithmetic _ (canonicalRouterGap_pos n) ?_ ?_ (n + 1) (by positivity) ?_ ?_ ?_ R B hR hB
  · change 0 < 64 * canonicalRouterGap n
    have := canonicalRouterGap_pos n
    omega
  · change canonicalRouterGap n + 1 < 64 * canonicalRouterGap n
    have := canonicalRouterGap_pos n
    omega
  · change (routerDigits n (canonicalRouterStride n) (canonicalRouterGap n) : ℝ) ≤ (n + 1 : ℕ)
    exact_mod_cast (routerDigits_le_width n (canonicalRouterStride n) (canonicalRouterGap n)).trans (Nat.le_succ n)
  · exact_mod_cast canonicalRouter_radix n
  · exact_mod_cast canonicalRouter_gap n

/-- The keyed payload header grows only logarithmically in its three operands. -/
theorem canonicalRouterBlockWidth_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    (canonicalRouterArithmetic n r R B hR hB).wb ≤
      canonicalScalarWidth n + canonicalScalarWidth (canonicalScalarWidth R) + canonicalScalarWidth B := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  change canonicalScalarWidth (fieldsLen (selectiveKeyLen p 0 (canonicalScalarWidth R)) + B) ≤ _
  have hf : fieldsLen (selectiveLen p 0) = n := by
    rw [selectiveFieldsLen]
    have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
    omega
  rw [selectiveKeyWidth, hf]
  exact (canonicalScalarWidth_add_le _ B).trans
    (Nat.add_le_add_right (canonicalScalarWidth_add_le n (canonicalScalarWidth R)) _)

/-- The complete address-key header has the same uniform logarithmic bound. -/
theorem canonicalRouterKeyWidth_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    (canonicalRouterArithmetic n r R B hR hB).wk ≤
      canonicalScalarWidth n + canonicalScalarWidth (canonicalScalarWidth R) := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  change canonicalScalarWidth (fieldsLen (selectiveKeyLen p 0 (canonicalScalarWidth R))) ≤ _
  have hf : fieldsLen (selectiveLen p 0) = n := by
    rw [selectiveFieldsLen]
    have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
    omega
  rw [selectiveKeyWidth, hf]
  exact canonicalScalarWidth_add_le _ _

/-- Geometry, classifier and placement dimension headers share the address-width budget. -/
theorem canonicalRouterDimensionWidths_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    let a := canonicalRouterArithmetic n r R B hR hB
    a.Lwidth ≤ canonicalScalarWidth n ∧ a.Lm ≤ canonicalScalarWidth n ∧
    a.LK ≤ canonicalScalarWidth n ∧ a.Ln ≤ canonicalScalarWidth n ∧
    a.Lo ≤ canonicalScalarWidth n ∧ a.Lt ≤ canonicalScalarWidth n ∧
    a.Lcp ≤ canonicalScalarWidth n := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
  have hwc : p.wc ≤ n := by omega
  have hwy : p.wy ≤ n := by omega
  have hk : p.K ≤ n := hn
  have hd : p.n ≤ n := routerDigits_le_width n _ _
  have ho : p.ρ + 1 ≤ n := by
    have hr := r.isLt
    change r.val + 1 ≤ n
    omega
  have hm : p.m ≤ n := by
    unfold Par.wy at hwy
    omega
  have hf : fieldsLen (selectiveLen p 0) = n := by rw [selectiveFieldsLen]; omega
  change canonicalScalarWidth p.wc ≤ _ ∧ canonicalScalarWidth p.wy ≤ _ ∧
    canonicalScalarWidth p.K ≤ _ ∧ canonicalScalarWidth p.n ≤ _ ∧
    canonicalScalarWidth (p.ρ + 1) ≤ _ ∧ canonicalScalarWidth p.m ≤ _ ∧
    canonicalScalarWidth (fieldsLen (selectiveLen p 0)) ≤ _
  exact ⟨canonicalScalarWidth_mono hwc, canonicalScalarWidth_mono hwy,
    canonicalScalarWidth_mono hk, canonicalScalarWidth_mono hd,
    canonicalScalarWidth_mono ho, canonicalScalarWidth_mono hm, by rw [hf]⟩

/-- Record-count and payload operands have the same widths in every residue. -/
theorem canonicalRouterRecordWidths (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    let a := canonicalRouterArithmetic n r R B hR hB
    a.wm = n + canonicalScalarWidth R ∧ a.Lrow = canonicalScalarWidth R ∧
    a.Lr = canonicalScalarWidth (canonicalScalarWidth R) ∧
    a.wp = canonicalScalarWidth B ∧ a.Lp = canonicalScalarWidth B ∧
    a.rowBits.length ≤ R.log2 + 1 := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have hf : fieldsLen (selectiveLen p 0) = n := by
    rw [selectiveFieldsLen]
    have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
    omega
  change fieldsLen (selectiveLen p 0) + canonicalScalarWidth R = _ ∧
    canonicalScalarWidth R = _ ∧ canonicalScalarWidth (canonicalScalarWidth R) = _ ∧
    canonicalScalarWidth B = _ ∧ canonicalScalarWidth B = _ ∧
    (GrowingCounterData.advance R []).length ≤ _
  exact ⟨by rw [hf], rfl, rfl, rfl, rfl, GrowingCounterData.empty_width R⟩

/-- All descriptor widths share a residue-independent logarithmic budget. -/
theorem canonicalRouterDescriptorWidths_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let w := canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    let D := Nat.clog 2 (4 * n + 2) + 1
    w.indexBits ≤ D ∧ w.strideBits ≤ D ∧ w.coordinateBits ≤ 2 * D ∧
    w.selectorBits ≤ 2 * D ∧ w.groupBits ≤ D ∧ w.widthBits ≤ canonicalScalarWidth (2 * D) := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let L := Nat.clog 2 (liveDescriptorMagnitude p 0 repairLiveMode + 1)
  have hi := canonicalRouterIndexBits_le n hn r
  have hc := canonicalRouterCoordinateBits_le n hn r
  change L + 1 ≤ Nat.clog 2 (4 * n + 2) + 1 at hi
  change (L + 1) + L ≤ 2 * (Nat.clog 2 (4 * n + 2) + 1) at hc
  dsimp only [canonicalStageWidths, liveDescriptorArithmeticWidths, liveDescriptorCanonicalWidths,
    LiveDescriptorWidths.coordinateBits]
  change L + 1 ≤ _ ∧ L ≤ _ ∧ (L + 1) + L ≤ _ ∧ (L + 1) + L ≤ _ ∧ L ≤ _ ∧
    canonicalScalarWidth ((L + 1) + L) ≤ _
  exact ⟨hi, by omega, hc, hc, by omega, canonicalScalarWidth_mono hc⟩

theorem canonicalRouterDescriptorBudget_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let w := canonicalStageWidths
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    let D := Nat.clog 2 (4 * n + 2) + 1
    LiveDescriptorMode.uniformBackendBudget n n w.indexBits w.groupBits w.strideBits
      w.selectorBits w.widthBits ≤
      LiveDescriptorMode.uniformBackendBudget n n D D D (2 * D) (canonicalScalarWidth (2 * D)) := by
  obtain ⟨hi, hk, _, hs, hg, hw⟩ := canonicalRouterDescriptorWidths_le n hn r
  exact LiveDescriptorMode.uniformBackendBudget_widths_mono n n hi hg hk hs hw

theorem canonicalRouterDescriptorCost_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let w := canonicalStageWidths p
    let D := Nat.clog 2 (4 * n + 2) + 1
    ∀ (hG : 0 < p.G) (hK : 0 < p.K) (_hGK : p.G < p.K)
      (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p 0),
    liveDescriptorBatchCost p 0 hG hK active s repairLiveMode w repairLiveJobs ≤
      11 * (28 * D + 16 + LiveDescriptorMode.uniformBackendBudget n n
        D D D (2 * D) (canonicalScalarWidth (2 * D))) + 1 := by
  dsimp only
  intro hG hK hGK active s
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let w := canonicalStageWidths p
  have hf : fieldsLen (selectiveLen p 0) = n := by
    rw [selectiveFieldsLen]
    have ht := routerProfileParameters_total n (canonicalRouterStride n) (canonicalRouterGap n) hn r
    change 3 * p.wc + p.wy = n at ht
    omega
  obtain ⟨hi, hg⟩ := canonicalRouterSlots_le n hn r
  have hc := repairLiveBankCost_le p 0 hG hK active s hGK w n n hf hi hg
    (canonicalStageWidths_bounds p)
  have hb := canonicalRouterDescriptorBudget_le n hn r
  change LiveDescriptorMode.uniformBackendBudget n n w.indexBits w.groupBits w.strideBits
    w.selectorBits w.widthBits ≤ _ at hb
  have hw := (canonicalRouterDescriptorWidths_le n hn r).2.2.1
  change w.coordinateBits ≤ _ at hw
  change liveDescriptorBatchCost p 0 hG hK active s repairLiveMode w repairLiveJobs ≤ _
  have hm := Nat.mul_le_mul_left 14 hw
  have hsum := Nat.add_le_add hm hb
  have ht := Nat.mul_le_mul_left 11 (Nat.add_le_add_right hsum 16)
  omega

theorem canonicalRouterRepairOverhead_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (width : ℕ) :
    let a := canonicalRouterArithmetic n r R B hR hB
    let rb := canonicalScalarWidth R
    let D := Nat.clog 2 (4 * n + 2) + 1
    liveRepairUniformOverhead n a.rb R B width a.wb a.wm a.wp a.wk a.w ≤
      liveRepairUniformOverhead n rb R B width
        (canonicalScalarWidth n + canonicalScalarWidth rb + canonicalScalarWidth B)
        (n + rb) (canonicalScalarWidth B) (canonicalScalarWidth n + canonicalScalarWidth rb)
        { indexBits := D, groupBits := D, strideBits := D, selectorBits := 2 * D,
          widthBits := canonicalScalarWidth (2 * D) } := by
  obtain ⟨hi, hs, _, hsel, hg, hw⟩ := canonicalRouterDescriptorWidths_le n hn r
  obtain ⟨hm, _, _, hp, _, _⟩ := canonicalRouterRecordWidths n hn r R B hR hB
  have hb := canonicalRouterBlockWidth_le n hn r R B hR hB
  have hk := canonicalRouterKeyWidth_le n hn r R B hR hB
  exact liveRepairUniformOverhead_mono n (canonicalScalarWidth R) R B
    (le_refl width) hb hm.le hp.le hk hi hg hs hsel hw

/-- Majorizing profile dimensions prices every residue with the same numerical formula. -/
theorem canonicalRouterProfileCost_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let D := Nat.clog 2 (4 * n + 2) + 1
    let q : Par := ⟨canonicalRouterStride n, 0, n, canonicalRouterGap n, 0⟩
    liveCoordinateProfilesCost p (canonicalStageWidths p) ≤
      liveCoordinateProfilesCost q
        { indexBits := D, groupBits := D, strideBits := D, selectorBits := 2 * D,
          widthBits := canonicalScalarWidth (2 * D) } := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let q : Par := ⟨canonicalRouterStride n, 0, n, canonicalRouterGap n, 0⟩
  have hslots : p.n ≤ q.n := routerDigits_le_width n _ _
  have hgroup : p.G ≤ q.G := le_refl _
  have hborrowed : p.wc ≤ q.wc := Nat.mul_le_mul hslots hgroup
  have hc := liveCoordinateProfilesCost_mono p q (canonicalStageWidths p) hslots hgroup hborrowed
  obtain ⟨hi, hk, _, hs, hg, hw⟩ := canonicalRouterDescriptorWidths_le n hn r
  exact hc.trans (liveCoordinateProfilesCost_widths_mono q _ _ hi hg hk hs hw)

theorem canonicalRouterClassifierCost_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let a := canonicalRouterArithmetic n r R B hR hB
    let L := canonicalScalarWidth n
    binaryTemporaryMaskCost p a.LK a.Ln a.Lo a.Lt + binaryPhaseMaskCost p a.LK a.Ln a.Lo a.Lt ≤
      binaryTemporaryMaskUniformCost n L L L L + binaryPhaseMaskUniformCost n L L L L := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let a := canonicalRouterArithmetic n r R B hR hB
  have hK : p.K ≤ n := hn
  have hG : p.G ≤ n := by
    change canonicalRouterGap n ≤ n
    unfold canonicalRouterStride at hn
    omega
  have hslots : p.n ≤ n := routerDigits_le_width n _ _
  have ho : p.ρ + 1 ≤ n := by
    have hr := r.isLt
    change r.val + 1 ≤ n
    omega
  have ht := routerProfileParameters_total n (canonicalRouterStride n) (canonicalRouterGap n) hn r
  change 3 * p.wc + p.wy = n at ht
  have hm : p.m ≤ n := by unfold Par.wy at ht; omega
  obtain ⟨_, _, hLK, hLn, hLo, hLt, _⟩ := canonicalRouterDimensionWidths_le n hn r R B hR hB
  have htemp := binaryTemporaryMaskCost_le p n a.LK a.Ln a.Lo a.Lt hK hG hslots ho hm
  have hphase := binaryPhaseMaskCost_le p n a.LK a.Ln a.Lo a.Lt hK hG hslots (by omega) hm
  exact Nat.add_le_add
    (htemp.trans (binaryTemporaryMaskUniformCost_widths_mono n hLK hLn hLo hLt))
    (hphase.trans (binaryPhaseMaskUniformCost_widths_mono n hLK hLn hLo hLt))

def canonicalRouterGeneratedOverhead (n R B width : ℕ) : ℕ :=
  let rb := canonicalScalarWidth R
  let L := canonicalScalarWidth n
  let D := Nat.clog 2 (4 * n + 2) + 1
  let wb := L + canonicalScalarWidth rb + canonicalScalarWidth B
  let w : LiveDescriptorWidths :=
    ⟨D, D, D, 2 * D, canonicalScalarWidth (2 * D)⟩
  let q : Par := ⟨canonicalRouterStride n, 0, n, canonicalRouterGap n, 0⟩
  binaryTemporaryMaskUniformCost n L L L L + binaryPhaseMaskUniformCost n L L L L +
    ((canonicalScalarWidth rb * (4 * rb + 11) + 8 * rb + 12) + (L * (4 * n + 11) + 2 * n + 6) + 1) +
    2 * (14 * n + 18 * rb + 24 * L + 52 * wb + 280) +
    liveCoordinateProfilesCost q w +
    liveRepairUniformOverhead n rb R B width wb (n + rb) (canonicalScalarWidth B)
      (L + canonicalScalarWidth rb) w +
    (11 * (2 * (n * (2 * D + 3)) + 2) + 1) +
    (10 * (2 * width + 2) + 1) + (2 * rb + 2 * n + 5) + (4 * (n + 1) + 5)

theorem canonicalRouterGeneratedOverhead_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (width : ℕ) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let a := canonicalRouterArithmetic n r R B hR hB
    allSourceGeneratedUniformOverhead p 0 a.rb n a.wb a.wm a.wp a.wk R B width
      a.Lrow a.Lwidth a.Lr a.Lm a.LK a.Ln a.Lo a.Lt a.w ≤
      canonicalRouterGeneratedOverhead n R B width := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let a := canonicalRouterArithmetic n r R B hR hB
  let rb := canonicalScalarWidth R
  let D := Nat.clog 2 (4 * n + 2) + 1
  have ht := routerProfileParameters_total n (canonicalRouterStride n) (canonicalRouterGap n) hn r
  change 3 * p.wc + p.wy = n at ht
  have hsize : p.wc + p.wy + 0 ≤ n := by omega
  have hslots : p.n ≤ n := routerDigits_le_width n _ _
  obtain ⟨_, _, _, hselector, _, _⟩ := canonicalRouterDescriptorWidths_le n hn r
  have hc := canonicalRouterClassifierCost_le n hn r R B hR hB
  have hp := canonicalRouterProfileCost_le n hn r
  change binaryTemporaryMaskCost p a.LK a.Ln a.Lo a.Lt +
    binaryPhaseMaskCost p a.LK a.Ln a.Lo a.Lt ≤ _ at hc
  change liveCoordinateProfilesCost p a.w ≤ _ at hp
  change a.w.selectorBits ≤ 2 * D at hselector
  have hb := allSourceGeneratedUniformOverhead_le p 0 rb n a.wb a.wm a.wp a.wk R B width
    a.Lrow a.Lwidth a.Lr a.Lm a.LK a.Ln a.Lo a.Lt _ _ (2 * D) a.w hsize hslots hselector hc hp
  have hrepair := canonicalRouterRepairOverhead_le n hn r R B hR hB width
  obtain ⟨hwidth, hmask, _, _, _, _, _⟩ := canonicalRouterDimensionWidths_le n hn r R B hR hB
  obtain ⟨_, hrow, hrowWidth, _, _, _⟩ := canonicalRouterRecordWidths n hn r R B hR hB
  have hblock := canonicalRouterBlockWidth_le n hn r R B hR hB
  change liveRepairUniformOverhead n rb R B width a.wb a.wm a.wp a.wk a.w ≤ _ at hrepair
  change a.Lwidth ≤ _ at hwidth
  change a.Lm ≤ _ at hmask
  change a.Lrow = rb at hrow
  change a.Lr = canonicalScalarWidth rb at hrowWidth
  have hrowLe := hrow.le
  have hrowWidthLe := hrowWidth.le
  change allSourceGeneratedUniformOverhead p 0 rb n a.wb a.wm a.wp a.wk R B width
    a.Lrow a.Lwidth a.Lr a.Lm a.LK a.Ln a.Lo a.Lt a.w ≤ _
  refine hb.trans ?_
  dsimp only [canonicalRouterGeneratedOverhead]
  gcongr

/-- A common metadata word budget, polynomial in address size and scalar widths. -/
def canonicalRouterUniformMetadataWidth (n R B : ℕ) : ℕ :=
  let D := Nat.clog 2 (4 * n + 2) + 1
  2 * n + n * (2 * D + 3) + 9 * canonicalScalarWidth n +
    3 * canonicalScalarWidth (canonicalScalarWidth R) + 3 * canonicalScalarWidth B +
    2 * canonicalScalarWidth R + 7 * D + canonicalScalarWidth (2 * D) + R.log2 + 1

theorem canonicalRouterMetadataWidth_uniform (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    canonicalGeneratedMetadataWidth
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
      (canonicalRouterArithmetic n r R B hR hB) ≤ canonicalRouterUniformMetadataWidth n R B := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let a := canonicalRouterArithmetic n r R B hR hB
  let D := Nat.clog 2 (4 * n + 2) + 1
  obtain ⟨hi, hs, hc, hsel, hg, hw⟩ := canonicalRouterDescriptorWidths_le n hn r
  obtain ⟨hlw, hlm, hlK, hln, hlo, hlt, hlcp⟩ := canonicalRouterDimensionWidths_le n hn r R B hR hB
  obtain ⟨hwm, hlrow, hlr, hwp, hlp, hrow⟩ := canonicalRouterRecordWidths n hn r R B hR hB
  have hwb := canonicalRouterBlockWidth_le n hn r R B hR hB
  have hwk := canonicalRouterKeyWidth_le n hn r R B hR hB
  have hnslots : p.n ≤ n := routerDigits_le_width n _ _
  have hf : fieldsLen (selectiveLen p 0) = n := by
    rw [selectiveFieldsLen]
    have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
    omega
  have hcoordinates : p.n * (a.w.indexBits + a.w.strideBits + 3) ≤ n * (2 * D + 3) :=
    Nat.mul_le_mul hnslots (by change a.w.indexBits ≤ D at hi; change a.w.strideBits ≤ D at hs; omega)
  change canonicalGeneratedMetadataWidth p a ≤ _
  unfold canonicalGeneratedMetadataWidth canonicalRouterUniformMetadataWidth
  rw [hf]
  have haw : a.w = canonicalStageWidths p := rfl
  rw [haw] at hcoordinates ⊢
  dsimp only [p, a, D] at *
  omega

/-- Every canonical residue has the same density-priced scan and sort budget. -/
theorem canonicalRouterDensityScanCost_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) :
    repairDensityScanCost
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
      0 (canonicalScalarWidth R) R B (n + 1 : ℕ) ≤
      repairUniformDensityScanCost n (canonicalScalarWidth R) R B (n + 1 : ℕ) := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
  apply repairDensityScanCost_le
  · rw [selectiveFieldsLen]
    change p.wc + (p.wy + 2 * p.wc + 0) = n
    omega
  · change p.wy ≤ n
    omega

/-- Canonical dimensions discharge every swap-header fit uniformly across residues. -/
theorem canonicalRouterHeaders_length_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) (c : Fin 2) (k : Fin 5) :
    (repairCanonicalHeaders
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
      0 (canonicalScalarWidth R) R B c k).length ≤
      n + canonicalScalarWidth R + canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)) +
        canonicalScalarWidth n + 1 := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
  have hf : fieldsLen (selectiveLen p 0) = n := by rw [selectiveFieldsLen]; omega
  have hb : 3 * (fieldsLen (selectiveKeyLen p 0 (canonicalScalarWidth R)) + B) <
      2 ^ canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)) := by
    rw [selectiveKeyWidth, hf]
    exact canonicalScalarWidth_fit _
  have hw : p.wc < 2 ^ canonicalScalarWidth n :=
    (show p.wc ≤ n by omega).trans_lt (canonicalScalarWidth_fit n)
  have hh := repairCanonicalHeaders_length_le p 0 (canonicalScalarWidth R) R B
    (canonicalScalarWidth R) (canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)))
    (canonicalScalarWidth n) hR (canonicalScalarWidth_fit R) hb hw c k
  simpa only [hf] using hh

theorem canonicalRouterHeaderEraseCost_le (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (R B : ℕ) (hR : 0 < R) :
    repairHeaderErasePrice
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
      0 (canonicalScalarWidth R) R B ≤
      10 * (2 * (n + canonicalScalarWidth R +
        canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)) + canonicalScalarWidth n + 1) + 2) + 1 :=
  repairHeaderErasePrice_le _ _ _ _ _ _ (canonicalRouterHeaders_length_le n hn r R B hR)

end
end IntegerMultBounds.MathlibTM2.Routing
