module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryArchiveInitialization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamCost

/-! Complete proper-core accuracy with the actual three boundary publications.
Coverage discharges the initial numerical invariant; stage traces are concrete. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {Q A s : ℕ} [NeZero s] {P U : Type}

theorem boundaryCompletion_of_proper_exec (body : P → Pr P 117 Q A U)
    (p width W D band n : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (cropCount : Fin 3 → Fin 117)
    (hreg : ∀ slot, [cropCount slot,15,54,19,27,28,24,26].Nodup)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (proper : CorePublicationClass s width)
    (hr : 0 < n*band) (hrw : n*band ≤ width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks 117 A)
    (hready : BoundarySeamReady (s := s) p width W D r.inputs.length cropCount seedValue S)
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient)
    (hsrc : S.R 95 = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : S.R 96 = ambient.flatten++outputTail)
    (depth : ℕ) (v : HS 117 Q A U) :
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ n ≤ 3*boundarySeamBudget r.inputs.length D s W+1 ∧
      SeamArchiveNumericalState p width W r J (coreSingletonPublication s width) 95 96 sourceTail outputTail S [] F ∧
      F.R 95 = sourceTail ∧
      (∃ ambient : List (List (Fin (A+4))), F.R 96 = ambient.flatten++outputTail ∧
        List.Forall₂ (fun target line => line.length = s*W ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
          (seamPublicationTargets p r J) ambient) ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*boundarySeamBudget r.inputs.length D s W) depth
        (boundarySeamPublication cropCount)
        (mk v S) n (mk v' F) := by
  have hInv := boundaryArchiveNumericalState_of_proper p width W band n hwidth hr hrw hroom
    r J proper hproper sourceTail outputTail S banks hbanks ambient hgood hsrc hdst
  obtain ⟨v',F,m,hu,hm,hF,hsource,hgood,hstock,he⟩ := boundarySeamPublication_exec body p width W D hA hW hwidth hroom hvolumeFit
    cropCount hreg seedValue hvalues hfit r J (coreSingletonPublication s width)
    (boundaryCropIndex_mem width hwidth hroom)
    (fun slot => coreSingletonPublication_of_mem width _ (boundaryCropIndex_mem width hwidth hroom slot))
    sourceTail outputTail S hready depth v S hInv
  have hcost : boundarySeamCost r.inputs.length (2*p+13) D s width W ≤
      boundarySeamBudget r.inputs.length D s W :=
    boundarySeamCost_le r.inputs.length (2*p+13) D s width W (NeZero.pos s) (by omega) hW hwidth hroom
  refine ⟨v',F,m,hu,?_,hF,hsource,hgood,hstock,?_⟩
  · omega
  · exact he.mono (by
      intro d z hz
      have hworkspace := Nat.mul_le_mul_left 13 hcost
      omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
