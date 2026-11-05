module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveSequence

/-! Execute physical boundary slots through the numerical archive invariant.
Persistent controls are transported by the restored frame at every stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {Q A s : ℕ} [NeZero s] {P U : Type}

theorem boundarySeamSequence_exec (body : P → Pr P 117 Q A U)
    (p width W D : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (cropCount : Fin 3 → Fin 117)
    (hreg : ∀ slot, [cropCount slot,15,54,19,27,28,24,26].Nodup)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (hk : ∀ slot, boundaryCropIndex s width slot ∈ coreIndices s width)
    (hclass : ∀ slot, classes (boundaryCropIndex s width slot) =
      singletonCorePublication s width (boundaryCropIndex s width slot) (hk slot))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks 117 A)
    (hready : BoundarySeamReady (s := s) p width W D r.inputs.length cropCount seedValue S)
    (cost : ℕ) (hcost : ∀ slot, boundarySlotSeamCost slot r.inputs.length (2*p+13) D s width W ≤ cost)
    (depth : ℕ) (slots : List (Fin 3)) (v : HS 117 Q A U) (M : Stacks 117 A)
    (hInv : SeamArchiveNumericalState p width W r J classes 95 96 sourceTail outputTail S
      (slots.map (boundaryCropIndex s width)) M) :
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ n ≤ slots.length*cost+1 ∧
      SeamArchiveNumericalState p width W r J classes 95 96 sourceTail outputTail S [] F ∧
      F.R 95 = sourceTail ∧
      (∃ ambient : List (List (Fin (A+4))), F.R 96 = ambient.flatten++outputTail ∧
        List.Forall₂ (fun target line => line.length = s*W ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
          (seamPublicationTargets p r J) ambient) ∧
      mnSize (mk v' F) ≤ mnSize (mk v M) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v M)+depth+13*cost) depth
        (restoringSequence (fun slot => boundarySlotSeamPublication slot (cropCount slot)) slots)
        (mk v M) n (mk v' F) := by
  let Inv : List (Fin 3) → Stacks 117 A → Prop := fun slots M => SeamArchiveNumericalState p width W r J classes 95 96
    sourceTail outputTail S (slots.map (boundaryCropIndex s width)) M
  have hstep (slot : Fin 3) (rest : List (Fin 3)) (u : HS 117 Q A U) (N : Stacks 117 A)
      (hI : Inv (slot::rest) N) :
      ∃ u' F, ∃ n : ℕ, u'.user = u.user ∧ n ≤ cost ∧ Inv rest F ∧
        mnSize (mk u' F) ≤ mnSize (mk u N) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk u N)+depth+13*cost) depth
          (boundarySlotSeamPublication slot (cropCount slot)) (mk u N) n (mk u' F) := by
    have hbytes := SeamArchiveNumericalState.forget p width W r J classes 95 96
      sourceTail outputTail S N _ hI
    have hreadyN := BoundarySeamReady.of_frame p width W D r.inputs.length cropCount seedValue S N hready
      (fun i hs hd => SeamArchiveState.off p width W r J 95 96 sourceTail outputTail S N _ hbytes i hs hd)
    obtain ⟨banks,ambient,hbanks,hpending,hN⟩ := hI
    have hlen : ambient.length = r.inputs.length := by
      simpa only [seamPublicationTargets,List.length_map,List.length_reverse] using hpending.length_eq.symm
    have hambient : ∀ line ∈ ambient, line.length = s*W := by
      exact (List.forall₂_and_left _ _).mp hpending.flip |>.1
    obtain ⟨rows,banks',hbanks',hrows,hrest,u',n,hu,hn,he,hstock,hw,hnum,hgood⟩ :=
      boundarySlotSeamPublication_exec body p width W hA hW slot (cropCount slot) (hreg slot)
        D hroom hvolumeFit seedValue hvalues hfit r J (rest.map (boundaryCropIndex s width)) banks
        hbanks hwidth (hk slot) ambient hlen hambient sourceTail outputTail u N
        hreadyN.widthRuler hreadyN.zero hreadyN.words hreadyN.tableBlank hreadyN.masters
        (hreadyN.bits slot) hreadyN.fresh hreadyN.setupTmp hreadyN.setupSaved hreadyN.retireTmp
        hreadyN.wide hreadyN.word
        (by rw [hN]; simp) (by rw [hN]; simp)
        hreadyN.clock hreadyN.line hreadyN.blank depth
    refine ⟨u',_,n,hu,hn.trans (hcost slot),?_,hstock,?_⟩
    · exact SeamArchiveNumericalState.rebase p width W r J classes 95 96 sourceTail outputTail
        S N _ _ _ ⟨banks,ambient,hbanks,hpending,hN⟩ (hnum classes (hclass slot) hpending)
    · exact hw.mono (by
        intro d z hz
        have hb := Nat.mul_le_mul_left 13 (hcost slot)
        omega)
  obtain ⟨v',F,n,hu,hn,hF,hstock,he⟩ := restoringSequence_exec_uniform body
    (fun slot => boundarySlotSeamPublication slot (cropCount slot)) Inv cost (13*cost) depth hstep slots v M hInv
  have hfinal : SeamArchiveNumericalState p width W r J classes 95 96 sourceTail outputTail S [] F := hF
  obtain ⟨hsource,hgood⟩ := hfinal.finish p width W hwidth r J classes 95 96 (by decide)
    sourceTail outputTail S F
  exact ⟨v',F,n,hu,by simpa [Nat.mul_comm] using hn,hfinal,hsource,hgood,hstock,he⟩

/-- Cropping prepends banks; publication consumes slots in increasing order. -/
def boundarySeamPublication (cropCount : Fin 3 → Fin 117) : Pr P 117 Q A U :=
  restoringSequence (fun slot => boundarySlotSeamPublication slot (cropCount slot)) [0,1,2]

def boundarySeamCost (N narrowWidth D s width W : ℕ) : ℕ :=
  max (boundarySlotSeamCost 0 N narrowWidth D s width W)
    (max (boundarySlotSeamCost 1 N narrowWidth D s width W)
      (boundarySlotSeamCost 2 N narrowWidth D s width W))

theorem boundarySeamPublication_exec (body : P → Pr P 117 Q A U)
    (p width W D : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (cropCount : Fin 3 → Fin 117)
    (hreg : ∀ slot, [cropCount slot,15,54,19,27,28,24,26].Nodup)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (hk : ∀ slot, boundaryCropIndex s width slot ∈ coreIndices s width)
    (hclass : ∀ slot, classes (boundaryCropIndex s width slot) =
      singletonCorePublication s width (boundaryCropIndex s width slot) (hk slot))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks 117 A)
    (hready : BoundarySeamReady (s := s) p width W D r.inputs.length cropCount seedValue S)
    (depth : ℕ) (v : HS 117 Q A U) (M : Stacks 117 A)
    (hInv : SeamArchiveNumericalState p width W r J classes 95 96 sourceTail outputTail S
      (boundaryCropSchedule s width).reverse M) :
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ n ≤ 3*boundarySeamCost r.inputs.length (2*p+13) D s width W+1 ∧
      SeamArchiveNumericalState p width W r J classes 95 96 sourceTail outputTail S [] F ∧
      F.R 95 = sourceTail ∧
      (∃ ambient : List (List (Fin (A+4))), F.R 96 = ambient.flatten++outputTail ∧
        List.Forall₂ (fun target line => line.length = s*W ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
          (seamPublicationTargets p r J) ambient) ∧
      mnSize (mk v' F) ≤ mnSize (mk v M) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v M)+depth+13*boundarySeamCost r.inputs.length (2*p+13) D s width W) depth
        (boundarySeamPublication cropCount)
        (mk v M) n (mk v' F) := by
  have hcost (slot : Fin 3) : boundarySlotSeamCost slot r.inputs.length (2*p+13) D s width W ≤
      boundarySeamCost r.inputs.length (2*p+13) D s width W := by
    unfold boundarySeamCost
    fin_cases slot
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have horder : ([(0:Fin 3),1,2].map (boundaryCropIndex s width)) =
      (boundaryCropSchedule s width).reverse := by
    simp [boundaryCropIndex,boundaryCropSchedule]
  have hrun := boundarySeamSequence_exec body p width W D hA hW hwidth hroom hvolumeFit
    cropCount hreg seedValue hvalues hfit r J classes hk hclass sourceTail outputTail S hready
    (boundarySeamCost r.inputs.length (2*p+13) D s width W) hcost depth [0,1,2] v M
    (by simpa only [horder] using hInv)
  simpa only [boundarySeamPublication,List.length_cons,List.length_nil] using hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
