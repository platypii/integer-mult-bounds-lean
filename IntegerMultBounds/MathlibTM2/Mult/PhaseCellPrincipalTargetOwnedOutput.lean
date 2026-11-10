module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalNormalizedOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetCoreLocalAccuracy

/-! The actual interval packet accepts the manuscript's floor-owned locality
comparison without changing its words or accumulating a window-count factor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

/-- A guarded floor-owned window has one nonwrapping principal interval. -/
theorem cyclicPrincipalVertices_owned {s t : ℕ} [NeZero s] (L k radius : ℕ)
    (ha : radius ≤ cut s t L k) (hb : cut s t L (k+1)+radius ≤ s) :
    cyclicPrincipalVertices s (cut s t L k-radius) (rows s t L k+2*radius) =
      haloVertices s (cut s t L k-radius) (cut s t L (k+1)+radius) := by
  have hrows : cut s t L k+rows s t L k = cut s t L (k+1) := by
    have hm := cut_mono s t L (show k ≤ k+1 by omega)
    unfold rows
    omega
  have hmin : min (rows s t L k+2*radius) (s-(cut s t L k-radius)) =
      rows s t L k+2*radius := min_eq_left (by omega)
  ext i
  simp only [cyclicPrincipalVertices,hmin,Nat.sub_self,Finset.mem_union,mem_haloVertices]
  omega

theorem PackedPrincipalOutput.target_owned {A s t p u l q qRef W target : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (hpq : p+1 ≤ q) (hpRef : p+1 ≤ qRef)
    (L k localityTarget : ℕ)
    (ha : localityDepth p localityTarget*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p localityTarget*PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      Finset.univ (Y F) (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re))
    {word : List (Fin (A+4))}
    (h : PackedPrincipalOutput (realMatrix s t p u)
      (cyclicPrincipalVertices s (cut s t L k-localityDepth p localityTarget*PhaseCellBand.width p u)
        (rows s t L k+2*(localityDepth p localityTarget*PhaseCellBand.width p u)))
      p q W target (cut s t L k) (rows s t L k) Fs word) :
    PackedIntervalOutput p W (cut s t L k) (rows s t L k)
      (Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution Y F i))
      ((2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)+
        (1/(2 : ℝ)^localityTarget+1/(2 : ℝ)^localityTarget)/(2 : ℝ)^inverseNormalizationShift p) word := by
  have hrows : cut s t L k+rows s t L k = cut s t L (k+1) := by
    have hm := cut_mono s t L (show k ≤ k+1 by omega)
    unfold rows
    omega
  have hprincipal := cyclicPrincipalVertices_owned L k
    (localityDepth p localityTarget*PhaseCellBand.width p u) ha hb
  rw [hprincipal] at h
  obtain ⟨y,hy,Ds,hDs,hword,haccuracy⟩ := h
  have hY' := complexComponentSolutions_changePrecision _ _ p q qRef hpq hpRef Fs hF Y hY
  have hunit := complexComponentFields_norm_le p Fs hF
  have hlocal : ∀ F ∈ complexComponentFields Fs,
      ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1))) (y F) (Y F)
        (1/(2 : ℝ)^localityTarget) := by
    intro F hmem
    have hrhs (i : ZMod s) : |(value q ((2 : GaussianInt)^(q-p-1)*F i)).re| ≤ 1 := by
      rw [(packedInputShift_value_fits p q hpq (F i) (hunit F hmem i)).1]
      calc
        _ ≤ ‖(1/2 : ℂ)*value p (F i)‖ := Complex.abs_re_le_norm _
        _ = (1/2 : ℝ)*‖value p (F i)‖ := by rw [norm_mul]; norm_num
        _ ≤ 1 := by have hh := hunit F hmem i; linarith
    have he := ErrorOn.target_owned_global axis.hst axis.hα p u localityTarget L k
      axis.hp axis.hpacket axis.hαu axis.hθ axis.hgap axis.hbudget ha hb
      (y F) (Y F) (y F) _ 0 (hY' F hmem) (hy F hmem) hrhs (by intro i hi; simp)
    simpa only [zero_add] using he
  have hglobal := normalizedPackedComponents_global_accuracy p W (cut s t L k) (rows s t L k)
    (inverseNormalizationShift p) (haloVertices s (cut s t L k) (cut s t L (k+1)))
    Fs y Y Ds [] _ (1/(2 : ℝ)^localityTarget) hlocal
    (by simpa only [hrows,List.map_map,Function.comp_def,List.append_nil] using haccuracy)
  refine ⟨Ds,by simpa only [List.length_map] using hDs,hword,?_⟩
  apply List.forall₂_map_left_iff.mpr
  simpa only [hrows,List.append_nil] using hglobal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
