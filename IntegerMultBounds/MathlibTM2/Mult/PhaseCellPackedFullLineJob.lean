module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob

/-! Full-line fallback jobs use the same packet, numerical solver and restoring
schedule as interior jobs. A zero-margin full core avoids asymmetric cropping;
its published line can supply every exceptional owned core. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

private theorem fullLine_vertices (s : ℕ) [NeZero s] : haloVertices s 0 s = Finset.univ := by
  ext i
  simp only [mem_haloVertices,Finset.mem_univ,iff_true]
  exact ⟨Nat.zero_le _,i.val_lt⟩

/-- A full owned core forces its generated halo to be the full principal system,
regardless of the requested locality depth. -/
theorem generatedWindow_fullLine_halo (s p u target : ℕ) [NeZero s] :
    (PhaseCellInterface.generatedWindow s s p u target 0).halo = haloVertices s 0 s := by
  apply Finset.Subset.antisymm
  · rw [fullLine_vertices]
    exact Finset.subset_univ _
  · have h := (PhaseCellInterface.generatedWindow s s p u target 0).core_subset_halo
    simpa only [PhaseCellInterface.generatedWindow,ownedCore,coreStart,coreLength,
      Nat.zero_mul,Nat.sub_zero,min_self,Nat.zero_add] using h

namespace PackedNormalizedJob

/-- All premises are ordinary numerical bounds for the full interval. The
constructor derives the crop geometry and generated-halo agreement itself. -/
noncomputable def fullLine {A s : ℕ} [NeZero s]
    (p u l targetOut t V Bcore q W localityTarget : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt) (Fs : List (ZMod s → GaussianInt))
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2) (a := 0) (b := s) (V := V) α gap C)
    (hsCore : s < 2^Bcore)
    (hqSizing : q = executionPrecision p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2)
    (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (hcoeff : ∀ j < s, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) j,
      Fits (2*q+8) z ∧ z.im = 0)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,targetOut,s,t,0,s] i < 2^Bcore)
    (hbandRoom : 64*(p+1)+u < 2^Bcore)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^Bcore)
    (hprecisionRoom : inversePrecisionRoom p l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) 0 s).card (PhaseCellBand.width p u) < 2^Bcore)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) : PackedNormalizedJob A s where
  p := p
  u := u
  l := l
  targetOut := targetOut
  t := t
  a := 0
  b := s
  V := V
  Bcore := Bcore
  q := q
  W := W
  coreWidth := s
  k := 0
  radius := 0
  localityTarget := localityTarget
  α := α
  gap := gap
  C := C
  Fs := Fs
  Y := Y
  bounds := bounds
  hsCore := hsCore
  hqSizing := hqSizing
  hpq := hpq
  hW := hW
  hF := hF
  haEq := by simp [coreStart]
  hbEq := by simp [coreStart,coreLength]
  hleft := Nat.zero_le _
  hright := by simp [coreStart,coreLength]
  hcoeff := by simpa only [Nat.sub_zero,Nat.zero_add] using hcoeff
  hvaluesFit := hvaluesFit
  hbandRoom := hbandRoom
  hgeometryRoom := hgeometryRoom
  hprecisionRoom := hprecisionRoom
  hhalo := (generatedWindow_fullLine_halo s p u localityTarget).symm
  hY := hY

/-- The ordinary output certificate of a full-line job certifies every ambient
coordinate. Thus one returned line supplies all exceptional cores. -/
theorem output_fullLine {A s : ℕ} [NeZero s] (r : PackedNormalizedJob A s)
    (hwidth : r.coreWidth = s) (hk : r.k = 0) {word : List (Fin (A+4))}
    (h : r.output word) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = r.Fs.length ∧
      word = (Gs.map (fun D => cstream A r.W (chirpLine s D))).flatten ∧
      word.length = r.Fs.length*s*r.W ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn Finset.univ
        (packedIntervalRead r.p r.W 0 (cstream A r.W (chirpLine s D)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*componentSolution r.Y F i)
        ((2/(2 : ℝ)^r.p+(1/(2 : ℝ)^r.targetOut)/(2 : ℝ)^inverseNormalizationShift r.p)+
          (1/(2 : ℝ)^r.localityTarget+1/(2 : ℝ)^r.localityTarget)/
            (2 : ℝ)^inverseNormalizationShift r.p)) r.Fs Gs := by
  have hvolume := output_length r h
  obtain ⟨Gs,hlen,hword,hgood⟩ := h
  have hwords (D : ZMod s → GaussianInt) : ownedCoreWords s 0 D = chirpLine s D := by
    simp only [ownedCoreWords,coreStart,coreLength,Nat.zero_mul,Nat.sub_zero,min_self,List.drop_zero]
    exact List.take_of_length_le (by simp)
  have hcore : ownedCore s s 0 = Finset.univ := by
    simpa [ownedCore,coreStart,coreLength] using fullLine_vertices s
  refine ⟨Gs,hlen,?_,?_,?_⟩
  · simpa only [hwidth,hk,hwords] using hword
  · simpa only [outputVolume,hwidth,hk,coreLength,coreStart,Nat.zero_mul,Nat.sub_zero,min_self]
      using hvolume
  · simpa only [hwidth,hk,hcore,hwords,coreStart,Nat.zero_mul] using hgood

end PackedNormalizedJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
