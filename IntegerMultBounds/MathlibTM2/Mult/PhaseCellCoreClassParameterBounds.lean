module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedParameterBounds
public import IntegerMultBounds.NLogN.PhaseCellCoreSetupGroups

/-! Movement-class membership discharges every proper interval geometry premise. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {p u l targetOut s t width L : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

/-- Shared analytic facts are checked once; each core contributes only its
membership in the ordered fitting class. -/
theorem coreClassParameterBounds (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (k : ℕ) (hk : k ∈ coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L) :
    let key := coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)
    PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := targetOut+1) (rhsExp := 2)
      (a := key.1) (b := key.2)
      (V := packedHaloWorkspaceWidth p l s t u (targetOut+1) 2 key.1 key.2) α gap C := by
  let radius := localityDepth p targetOut*PhaseCellBand.width p u
  have hspec := coreGatherIndices_spec s width radius L k hk
  have hcore : k ∈ coreIndices s width := by
    exact List.mem_of_mem_filter hk
  have hstart := coreIndex_start_lt s width k hwidth hcore
  have hfit : radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s :=
    ⟨hspec.1,hspec.2.1⟩
  have hkey : coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut) =
      (coreStart width k-radius,coreStart width k+coreLength s width k+radius) := by
    simp only [coreHaloEndpoints,show localityDepth p targetOut*PhaseCellBand.width p u = radius from rfl,ite_eq_left hfit]
  have hab : coreStart width k-radius ≤ coreStart width k+coreLength s width k+radius := by omega
  have haLt : coreStart width k-radius < s := by omega
  have hlength : (coreStart width k+coreLength s width k+radius)-(coreStart width k-radius) = L := by
    have := hspec.2.2
    omega
  dsimp only
  rw [hkey]
  exact PackedHaloParameterBounds.ofAnalytic hp hpacket hα hst hu hαu hθ hgap hbudget hband hab hfit.2 haLt
    hpad (by simpa only [hlength] using hsep) (hC _ _ hab hfit.2 haLt) hdom
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
