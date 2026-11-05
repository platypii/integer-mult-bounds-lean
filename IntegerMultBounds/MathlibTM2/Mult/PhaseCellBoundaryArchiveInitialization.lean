module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamSequence

/-! Proper publication initializes the concrete boundary archive loop.
The singleton class is total; only its valid-core branch is ever executed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {A s : ℕ}

def coreSingletonPublication (s width k : ℕ) : CorePublicationClass s width :=
  if hk : k ∈ coreIndices s width then singletonCorePublication s width k hk
  else ⟨0,[],List.nil_sublist _⟩

theorem coreSingletonPublication_of_mem (width k : ℕ) (hk : k ∈ coreIndices s width) :
    coreSingletonPublication s width k = singletonCorePublication s width k hk := by
  simp only [coreSingletonPublication,dite_eq_left hk]

theorem boundaryCropIndex_mem (width : ℕ) (hw : 0 < width) (hroom : 3*width < s) (slot : Fin 3) :
    boundaryCropIndex s width slot ∈ coreIndices s width := by
  apply ((boundaryCropSchedule_spec s width hw hroom).2.2 _ ?_).1
  fin_cases slot <;> simp [boundaryCropIndex,boundaryCropSchedule]

theorem proper_coreSingletonPublication_cover (width band n : ℕ)
    (hw : 0 < width) (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band))) :
    ∀ k ∈ coreIndices s width, ∃ c ∈ proper::
      (boundaryCropSchedule s width).reverse.map (coreSingletonPublication s width), k ∈ c.indices := by
  intro k hk
  rcases fullGather_or_boundaryCropSchedule s width band n k hw hr hrw hroom hk with hp | hb
  · exact ⟨proper,by simp,by rwa [hproper]⟩
  · refine ⟨coreSingletonPublication s width k,List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨k,List.mem_reverse.mpr hb,rfl⟩),?_⟩
    rw [coreSingletonPublication_of_mem width k hk]
    exact List.mem_singleton.mpr rfl

variable [NeZero s]

theorem boundaryArchiveNumericalState_of_proper (p width W band n : ℕ)
    (hw : 0 < width) (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks 117 A)
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient)
    (hsrc : S.R 95 = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : S.R 96 = ambient.flatten++outputTail) :
    SeamArchiveNumericalState p width W r J (coreSingletonPublication s width) 95 96
      sourceTail outputTail S (boundaryCropSchedule s width).reverse S := by
  have h := SeamArchiveNumericalState.of_proper p width W r J (coreSingletonPublication s width)
    proper 95 96 sourceTail outputTail S _ banks hbanks ambient
    (proper_coreSingletonPublication_cover width band n hw hr hrw hroom proper hproper) hgood
  have hstate : ({S with R := (Function.update (Function.update S.R 95
      ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail))
      96 (ambient.flatten++outputTail))} : Stacks 117 A) = S := by
    rw [←hsrc,←hdst]
    simp
  rw [hstate] at h
  exact h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
