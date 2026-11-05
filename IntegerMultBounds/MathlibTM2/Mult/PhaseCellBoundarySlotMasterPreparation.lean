module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstBoundaryMasterPreparation

/-! Fixed boundary slots select only control preparation. Publication uses the
same prepared-state continuation for every slot. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

def boundarySlotMasterPreparation (slot : Fin 3) (cropCount : Fin 117) : Pr P 117 Q A U :=
  if slot = 0 then firstBoundaryMasterPreparation cropCount
  else standardBoundaryMasterPreparation (decide (slot = 2)) cropCount

def boundarySlotMasterPreparationCost (slot : Fin 3) (N narrowWidth D s width W : ℕ) : ℕ :=
  if slot = 0 then firstBoundaryMasterPreparationCost N narrowWidth D width W
  else
    let L := coreLength s width (boundaryCropIndex s width slot)
    (64*D+81)+(16*TableVM.tblC D 0+6*(s*W)+22*D+13)+(20*D+21)+
      ((6*(L*narrowWidth)+6)+(N*(4*(L*narrowWidth)+9)+4))

theorem boundarySlotMasterPreparation_native (slot : Fin 3) (cropCount : Fin 117) :
    mnNativePushBound 3
      (boundarySlotMasterPreparation (P := P) (Q := Q) (A := A) (U := U) slot cropCount) := by
  unfold boundarySlotMasterPreparation
  split
  · exact firstBoundaryMasterPreparation_native cropCount
  · exact standardBoundaryMasterPreparation_native _ cropCount

theorem boundarySlotMasterPreparation_exec (body : P → Pr P 117 Q A U)
    (slot : Fin 3) (cropCount : Fin 117) (hreg : [cropCount,15,54,19,27,28,24,26].Nodup)
    (N narrowWidth D s width W : ℕ)
    (hwidth : 0 < width) (hW : 0 < W) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidthRuler : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (seedValue (boundarySeedGlobals j)))
    (htableBlank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = [] ∧ S.R 54 = [] ∧ S.R 19 = [])
    (hwide : (S.R 17).length = W) (hN : (S.R 15).length = N)
    (hbits : (S.R cropCount).length = coreLength s width (boundaryCropIndex s width slot)*narrowWidth)
    (hsetupTmp : S.R 27 = []) (hsetupSaved : S.R 28 = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ boundarySlotMasterPreparationCost slot N narrowWidth D s width W ∧
      Exec body (boundarySlotMasterPreparation slot cropCount) (mk v S) n
        (mk v' (standardBoundaryMasterState cropCount N narrowWidth s width
          (boundaryCropIndex s width slot) W S)) := by
  have hprepareLast (last : Bool)
      (hindex : BoundaryCropMetadata.index last s width = boundaryCropIndex s width slot) :
      ∃ v' n, v'.user = v.user ∧
        n ≤ (64*D+81)+(16*TableVM.tblC D 0+6*(s*W)+22*D+13)+(20*D+21)+
          ((6*(coreLength s width (BoundaryCropMetadata.index last s width)*narrowWidth)+6)+
            (N*(4*(coreLength s width (BoundaryCropMetadata.index last s width)*narrowWidth)+9)+4)) ∧
        Exec body (standardBoundaryMasterPreparation last cropCount) (mk v S) n
          (mk v' (standardBoundaryMasterState cropCount N narrowWidth s width
            (BoundaryCropMetadata.index last s width) W S)) := by
    apply standardBoundaryMasterPreparation_exec body last cropCount hreg N narrowWidth D s width W
      hwidth hW hroom hvolumeFit seedValue hvalues hfit v S hwidthRuler hzero hwords htableBlank
      ⟨hmasters.1,hmasters.2.1⟩ hN
    · simpa only [hindex] using hbits
    · exact ⟨hmasters.2.2.1,hmasters.2.2.2,hsetupTmp,hsetupSaved⟩
    · exact depth
  fin_cases slot
  · have hbinary : S.R 56 = binSyms D width := by
      have h := hwords 1
      rw [hvalues 1] at h
      simpa [boundarySeedGlobals] using h
    have hwidthFit : width < 2^D := by
      have h := hfit 1
      rw [hvalues 1] at h
      exact h
    have hscratch : S.R 30 = [] ∧ S.R 31 = [] ∧ S.R 32 = [] := by
      exact ⟨htableBlank (.v 0),htableBlank (.v 1),htableBlank (.v 2)⟩
    obtain ⟨v',n,hu,hn,he⟩ := firstBoundaryMasterPreparation_exec body cropCount hreg N narrowWidth
      D s width W (by omega) hwidthFit v S hbinary hwide hN
      (by simpa [boundaryCropIndex,coreLength,coreStart,Nat.min_eq_left (show width ≤ s by omega)] using hbits)
      hmasters ⟨hscratch.1,hscratch.2.1,hscratch.2.2,hsetupTmp,hsetupSaved⟩
    refine ⟨v',n,hu,?_,?_⟩
    · exact hn
    · simpa [boundarySlotMasterPreparation,boundaryCropIndex] using he
  · have hindex := BoundaryCropMetadata.index_eq_boundary false s width hwidth hroom
    have h := hprepareLast false (by simpa using hindex)
    simpa [boundarySlotMasterPreparation,boundarySlotMasterPreparationCost,hindex] using h
  · have hindex := BoundaryCropMetadata.index_eq_boundary true s width hwidth hroom
    have h := hprepareLast true (by simpa using hindex)
    simpa [boundarySlotMasterPreparation,boundarySlotMasterPreparationCost,hindex] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
