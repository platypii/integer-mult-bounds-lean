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

end
end IntegerMultBounds.MathlibTM2.Routing
