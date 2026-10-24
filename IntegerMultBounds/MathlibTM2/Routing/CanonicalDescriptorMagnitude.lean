module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageWidths
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterArithmetic

/-! Collapse the fixed eleven-mode descriptor magnitude to four scalar bounds,
so runtime width generation need not reproduce a mode-table supremum. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem repairLiveDescriptorMagnitude_eq (p : Par) :
    liveDescriptorMagnitude p 0 repairLiveMode =
      max p.G (max p.K (max p.n (p.wy + 2 * p.wc + 1))) := by
  let M := max p.G (max p.K (max p.n (p.wy + 2 * p.wc + 1)))
  have hG : p.G ≤ M := by dsimp [M]; omega
  have hK : p.K ≤ M := by dsimp [M]; omega
  have hn : p.n ≤ M := by dsimp [M]; omega
  have hB : p.wy + 2 * p.wc + 1 ≤ M := by dsimp [M]; omega
  have hwc : p.n * p.G ≤ M := by change p.wc ≤ M; omega
  apply Nat.le_antisymm
  · change liveDescriptorMagnitude p 0 repairLiveMode ≤ M
    unfold liveDescriptorMagnitude
    apply max_le hG
    apply Finset.sup_le
    intro j _
    fin_cases j <;>
      simp [repairLiveMode, repairDescriptorKey, LiveDescriptorMode.ofKey, LiveDescriptorMode.stride,
        LiveDescriptorMode.key, LiveDescriptorMode.slots, repairAffineStride,
        repairCompactRows, repairCompactSourceWidth, selectiveTargetWidth, selectiveSourceWidth] <;> omega
  · have h0 : max p.K (max p.wy (max p.n (p.wy + 2 * p.wc + 1))) ≤
        liveDescriptorMagnitude p 0 repairLiveMode := by
      have h := Finset.le_sup (s := (Finset.univ : Finset (Fin 11)))
        (f := fun j => max ((repairLiveMode j).stride p) (max (repairCompactRows p (repairLiveMode j).key)
          (max ((repairLiveMode j).slots p) (repairCompactSourceWidth p 0 (repairLiveMode j).key + 1))))
        (by simp : (0 : Fin 11) ∈ Finset.univ)
      have hs : (Finset.univ.sup fun j => max ((repairLiveMode j).stride p)
          (max (repairCompactRows p (repairLiveMode j).key)
            (max ((repairLiveMode j).slots p) (repairCompactSourceWidth p 0 (repairLiveMode j).key + 1)))) ≤
          liveDescriptorMagnitude p 0 repairLiveMode := le_max_right _ _
      simpa [repairLiveMode, repairDescriptorKey, LiveDescriptorMode.ofKey, LiveDescriptorMode.stride,
        LiveDescriptorMode.key, LiveDescriptorMode.slots, repairAffineStride,
        repairCompactRows, repairCompactSourceWidth] using h.trans hs
    have hg : p.G ≤ liveDescriptorMagnitude p 0 repairLiveMode := le_max_left _ _
    omega

/-- In the routing geometry, the complete physical source width dominates. -/
theorem repairLiveDescriptorMagnitude_eq_source (p : Par)
    (hK : 0 < p.K) (hG : p.G ≤ p.K) (hwidth : p.K ≤ p.wy) :
    liveDescriptorMagnitude p 0 repairLiveMode = p.wy + 2 * p.wc + 1 := by
  have hn : p.n ≤ p.wy := by
    have hm := Nat.le_mul_of_pos_right p.n hK
    have hs : p.n * p.K ≤ p.wy := by unfold Par.wy; omega
    exact hm.trans hs
  rw [repairLiveDescriptorMagnitude_eq]
  rw [max_eq_right (by omega : p.n ≤ p.wy + 2 * p.wc + 1),
    max_eq_right (by omega : p.K ≤ p.wy + 2 * p.wc + 1),
    max_eq_right (by omega : p.G ≤ p.wy + 2 * p.wc + 1)]

theorem canonicalDescriptorMagnitude_eq (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    liveDescriptorMagnitude
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val) 0 repairLiveMode =
      n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 1 := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have hgap := canonicalRouterGap_pos n
  have hK : 0 < p.K := by change 0 < canonicalRouterStride n; unfold canonicalRouterStride; omega
  have hG : p.G ≤ p.K := by change canonicalRouterGap n ≤ canonicalRouterStride n; unfold canonicalRouterStride; omega
  have hwidth : p.K ≤ p.wy := by
    change canonicalRouterStride n ≤ (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val).wy
    rw [routerProfileParameters_width n _ _ hlarge r, routerTargetWidth_eq n _ _ hlarge]
    omega
  have ht := routerProfileParameters_total n (canonicalRouterStride n) (canonicalRouterGap n) hlarge r
  change 3 * p.wc + p.wy = n at ht
  have hwc : p.wc = routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) := rfl
  rw [repairLiveDescriptorMagnitude_eq_source p hK hG hwidth]
  rw [← hwc]
  omega

/-- Every residue uses the same exact descriptor widths. -/
theorem canonicalStageWidths_router (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2)
    (canonicalStageWidths p).indexBits = W + 1 ∧
      (canonicalStageWidths p).groupBits = W ∧ (canonicalStageWidths p).strideBits = W ∧
      (canonicalStageWidths p).selectorBits = 2 * W + 1 ∧
      (canonicalStageWidths p).widthBits = canonicalScalarWidth (2 * W + 1) := by
  dsimp only
  have hbase : Nat.clog 2
      (liveDescriptorMagnitude (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val) 0 repairLiveMode + 1) =
      Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2) := by
    rw [canonicalDescriptorMagnitude_eq n hlarge r]
  have hcoord : (Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2) + 1) +
      Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2) =
      2 * Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2) + 1 := by omega
  simp [canonicalStageWidths, liveDescriptorArithmeticWidths, liveDescriptorCanonicalWidths, hbase, hcoord]

/-- The canonical gap also bounds the numeric coordinate-width operand. -/
theorem canonicalDescriptorCoordinateWidth_le_gap (n : ℕ) :
    2 * Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2) + 1 ≤
      canonicalRouterGap n := by
  have hm := Nat.clog_mono_right 2 (Nat.add_le_add_right
    (Nat.sub_le n (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))) 2)
  change 2 * Nat.clog 2 (n - routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) + 2) + 1 ≤
    6 + 4 * Nat.clog 2 (n + 2)
  omega

end IntegerMultBounds.MathlibTM2.Routing
