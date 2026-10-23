module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorData

/-! Logarithmic common widths for any finite family of live descriptor jobs.
No per-job width choices or fit hypotheses are needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

/-- A single numeric bound on every scalar used by the descriptor family. -/
def liveDescriptorMagnitude {J : ℕ} (p : Par) (X : ℕ) (mode : Fin J → LiveDescriptorMode) : ℕ :=
  max p.G (Finset.univ.sup fun j =>
    max ((mode j).stride p) (max (repairCompactRows p (mode j).key)
      (max ((mode j).slots p) (repairCompactSourceWidth p X (mode j).key + 1))))

/-- A polynomial bound on descriptor magnitudes, uniform over the mode family. -/
theorem liveDescriptorMagnitude_le {J : ℕ} (p : Par) (X : ℕ) (mode : Fin J → LiveDescriptorMode) :
    liveDescriptorMagnitude p X mode ≤ p.G + p.K + p.n + p.n * p.G + p.wy + 2 * p.wc + X + 1 := by
  unfold liveDescriptorMagnitude
  apply max_le
  · omega
  · apply Finset.sup_le
    intro j _
    cases hm : mode j with
    | grouped k =>
      simp only [LiveDescriptorMode.stride, LiveDescriptorMode.key, LiveDescriptorMode.slots,
        repairCompactRows, repairCompactSourceWidth, selectiveTargetWidth, selectiveSourceWidth, max_le_iff]
      omega
    | affine key hkey =>
      cases key with
      | none =>
        simp only [LiveDescriptorMode.stride, LiveDescriptorMode.key, LiveDescriptorMode.slots,
          repairAffineStride, repairCompactRows, repairCompactSourceWidth, max_le_iff]
        omega
      | some pair =>
        obtain ⟨off, k⟩ := pair
        cases off <;>
          simp only [LiveDescriptorMode.stride, LiveDescriptorMode.key, LiveDescriptorMode.slots,
            repairAffineStride, repairCompactRows, repairCompactSourceWidth,
            selectiveTargetWidth, selectiveSourceWidth, max_le_iff] <;> omega

def liveDescriptorCanonicalWidths {J : ℕ} (p : Par) (X : ℕ) (mode : Fin J → LiveDescriptorMode) : LiveDescriptorWidths :=
  let L := Nat.clog 2 (liveDescriptorMagnitude p X mode + 1)
  { indexBits := L, groupBits := L, strideBits := L, selectorBits := L,
    widthBits := Nat.clog 2 (L + 1) }

theorem liveDescriptorCanonicalWidths_indexBits_le {J : ℕ} (p : Par) (X : ℕ)
    (mode : Fin J → LiveDescriptorMode) :
    (liveDescriptorCanonicalWidths p X mode).indexBits ≤
      Nat.clog 2 (p.G + p.K + p.n + p.n * p.G + p.wy + 2 * p.wc + X + 2) := by
  change Nat.clog 2 (liveDescriptorMagnitude p X mode + 1) ≤ _
  apply Nat.clog_mono_right
  have h := liveDescriptorMagnitude_le p X mode
  omega

theorem liveDescriptorCanonicalWidths_bounds {J : ℕ} (p : Par) (X : ℕ)
    (mode : Fin J → LiveDescriptorMode) (j : Fin J) :
    LiveDescriptorBounds p X (liveDescriptorCanonicalWidths p X mode) (mode j) := by
  let M := liveDescriptorMagnitude p X mode
  let L := Nat.clog 2 (M + 1)
  have hM : M < 2 ^ L := lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_pow_clog (by decide) (M + 1))
  have hj : max ((mode j).stride p) (max (repairCompactRows p (mode j).key)
      (max ((mode j).slots p) (repairCompactSourceWidth p X (mode j).key + 1))) ≤ M :=
    le_trans (Finset.le_sup (f := fun i : Fin J => max ((mode i).stride p)
      (max (repairCompactRows p (mode i).key)
        (max ((mode i).slots p) (repairCompactSourceWidth p X (mode i).key + 1))))
      (Finset.mem_univ j)) (le_max_right _ _)
  have hg : p.G ≤ M := le_max_left _ _
  have hstride : (mode j).stride p ≤ M := (le_max_left _ _).trans hj
  have hrows : repairCompactRows p (mode j).key ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hslots : (mode j).slots p ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hj))
  have hsource : repairCompactSourceWidth p X (mode j).key + 1 ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hj))
  have hcoord : 2 ^ L ≤ 2 ^ (L + L) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hwidth : L < 2 ^ Nat.clog 2 (L + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self L) (Nat.le_pow_clog (by decide) (L + 1))
  refine ⟨hg.trans_lt hM, hstride.trans_lt hM, hrows.trans_lt (hM.trans_le hcoord), ?_,
    hslots.trans hM.le, hsource.trans_lt hM, hwidth⟩
  dsimp only [liveDescriptorCanonicalWidths, LiveDescriptorWidths.coordinateBits]
  exact Nat.le_add_right _ _

/-- Canonical widths establish readiness without a separate numeric fit oracle. -/
theorem liveDescriptorCanonicalBank_ready {N J A : ℕ} (p : Par) (X : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (mode : Fin J → LiveDescriptorMode)
    (core : Fin N → List (Fin (A + 4))) :
    LiveDescriptorReady p X hG hK active s mode (liveDescriptorCanonicalWidths p X mode)
      (liveDescriptorBank core (liveDescriptorData p X hG hK active s mode
        (liveDescriptorCanonicalWidths p X mode))) :=
  liveDescriptorBank_ready p X hG hK active s mode _ core
    (liveDescriptorCanonicalWidths_bounds p X mode)

end
end IntegerMultBounds.MathlibTM2.Routing
