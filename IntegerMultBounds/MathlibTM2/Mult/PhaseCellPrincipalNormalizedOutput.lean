module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentLocality
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry

/-! The existing manuscript locality theorem accepts computed principal-core
packets directly, yielding the established publication-output contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Exact input shifting makes component systems independent of working precision. -/
theorem complexComponentSolutions_changePrecision {s : ℕ}
    (M : Matrix (ZMod s) (ZMod s) ℝ) (principal : Finset (ZMod s))
    (p q qRef : ℕ) (hpq : p+1 ≤ q) (hpRef : p+1 ≤ qRef)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) :
    ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) := by
  intro F hmem i hi
  dsimp only
  have hunit := complexComponentFields_norm_le p Fs hF F hmem i
  rw [(packedInputShift_value_fits p q hpq (F i) hunit).1]
  have h := hY F hmem i hi
  dsimp only at h
  rw [(packedInputShift_value_fits p qRef hpRef (F i) hunit).1] at h
  exact h

theorem principalNormalizedOutput {A s t p u l q a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (hpq : p+1 ≤ q)
    (W target coreWidth k localityTarget qRef : ℕ) (hpRef : p+1 ≤ qRef)
    (hhalo : cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      (cyclicPrincipalVertices s a n) (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      Finset.univ (Y F) (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re))
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = Fs.length)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D))) z
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p))
      (Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i)) Ds) :
    PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y
      ((Ds.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten) := by
  refine ⟨Ds,hlen,rfl,?_⟩
  have hY' : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      Finset.univ (Y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) :=
    complexComponentSolutions_changePrecision _ _ p q qRef hpq hpRef Fs hF Y hY
  have hglobal := normalizedPackedComponents_generated_accuracy axis.hst axis.hα
    coreWidth p u localityTarget k q (inverseNormalizationShift p) W axis.hp hpq axis.hpacket
    axis.hαu axis.hθ axis.hgap axis.hbudget Fs hF y Y
    (by simpa only [←hhalo] using hy) hY' Ds []
    (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)
    (by simpa only [List.map_map,Function.comp_def,List.append_nil] using hgood)
  simpa only [List.append_nil] using hglobal


/-- Regular-core locality is a corollary of the generic principal packet. -/
theorem PackedPrincipalOutput.generated {A s t p u l q a n : ℕ} [NeZero s] {α d : ℝ}
    {W target coreWidth k localityTarget qRef : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {word : List (Fin (A+4))}
    (h : PackedPrincipalOutput (realMatrix s t p u) (cyclicPrincipalVertices s a n)
      p q W target (coreStart coreWidth k) (coreLength s coreWidth k) Fs word)
    (axis : RecoveryAxisBounds s t p u l α d) (hpq : p+1 ≤ q) (hpRef : p+1 ≤ qRef)
    (hhalo : cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      Finset.univ (Y F) (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) :
    PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word := by
  obtain ⟨y,hy,Ds,hDs,hword,haccuracy⟩ := h
  rw [hword]
  apply principalNormalizedOutput axis hpq W target coreWidth k localityTarget qRef hpRef
    hhalo Fs hF y Y hy hY Ds
  · simpa only [List.length_map] using hDs
  · simpa only [ownedCore,ownedCoreWords,packedInterval] using haccuracy

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
