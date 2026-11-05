module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmbeddedBoundaryCompletion
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopiedHeaderRetirement

/-! Load retained masters, execute boundary publication, and release the copied
masters. The caller frame is restored except for the two data ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

noncomputable section
open PackedTranspose

def boundarySeamCallerPublication (source destination : Fin T) (masters : Fin 11 → Fin T) :
    Pr P (T+tapeCount) Q A U :=
  .seq (boundarySeamMasterLoad source destination masters)
    (.seq (embProg (seamRegister source destination) (fun f : Empty => nomatch f)
      (boundarySeamPublication boundarySeamCropCount))
      (clearWords ((boundarySeamMasterCopies source destination masters).map Prod.snd)))

theorem boundarySeamCallerPublication_exec (body : P → Pr P (T+PackedTranspose.tapeCount) Q A U)
    (source destination : Fin T) (hne : source ≠ destination) (masters : Fin 11 → Fin T)
    (p width W D band n : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (proper : CorePublicationClass s width)
    (hr : 0 < n*band) (hrw : n*band ≤ width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (B : Stacks (T+PackedTranspose.tapeCount) A)
    (words : Fin 11 → List (Fin (A+4)))
    (hwords : BoundarySeamHeaderWords (s := s) p width W D r.inputs.length seedValue words)
    (hheaders : ∀ i, B.R (Fin.castAdd PackedTranspose.tapeCount (masters i)) = words i)
    (hblank : ∀ i, i ≠ 95 → i ≠ 96 → B.R (PackedTranspose.seamRegister source destination i) = [])
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient)
    (hsrc : B.R (PackedTranspose.seamRegister source destination 95) = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : B.R (PackedTranspose.seamRegister source destination 96) = ambient.flatten++outputTail)
    (depth : ℕ) (v : HS (T+PackedTranspose.tapeCount) Q A U) :
    let pairs := boundarySeamMasterCopies source destination masters
    let loadCost := (pairs.map (fun p => 6*(B.R p.1).length+6)).sum+1
    let retireCost := 2*(pairs.map (fun p => (B.R p.1).length)).sum+2*pairs.length+1
    ∃ output : List (List (Fin (A+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) output ∧
      let F : Stacks (T+tapeCount) A := {B with R := (Function.update
        (Function.update B.R (seamRegister source destination 95) sourceTail)
        (seamRegister source destination 96) (output.flatten++outputTail))}
      ∃ v' m, v'.user = v.user ∧
        m ≤ loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost ∧
        mnSize (mk v' F) ≤ mnSize (mk v B) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v B)+depth+
          (2*loadCost+13*boundarySeamBudget r.inputs.length D s W)) depth
          (boundarySeamCallerPublication source destination masters) (mk v B) m (mk v' F) := by
  dsimp only
  let e := seamRegister source destination
  let pairs := boundarySeamMasterCopies source destination masters
  let L : Stacks (T+tapeCount) A := {B with R := copyWordHeadersR B.R pairs B.R}
  have hinj := seamRegister_injective source destination hne
  have hrole (i : Fin 11) : boundarySeamMasterRole i ≠ 95 ∧ boundarySeamMasterRole i ≠ 96 := by
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact ⟨h.1,h.2.1⟩
  have hoff (k : Fin 117) (hk : ∀ i, boundarySeamMasterRole i ≠ k) : L.R (e k) = B.R (e k) := by
    apply copyWordHeadersR_off
    intro pair hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hinj.ne (hk i)
  obtain ⟨u,hu,hready,hl⟩ := boundarySeamMasterLoad_ready_exec body p width W D r.inputs.length
    seedValue words hwords source destination hne masters v B hheaders hblank depth
  obtain ⟨output,haccuracy,u',m,hu',hm,hstock,hpub⟩ := embeddedBoundaryCompletion_of_proper_exec body e hinj
    p width W D band n hA hW hwidth hroom hvolumeFit boundarySeamCropCount
    (by intro slot; fin_cases slot <;> decide +kernel) seedValue hvalues hfit r J proper hr hrw hproper
    sourceTail outputTail L hready banks hbanks ambient hgood
    (by rw [hoff 95 (fun i => (hrole i).1)]; exact hsrc)
    (by rw [hoff 96 (fun i => (hrole i).2)]; exact hdst) depth u
  have hnd : (pairs.map Prod.snd).Nodup := by
    dsimp only [pairs]
    rw [boundarySeamMasterCopies,List.map_ofFn]
    exact List.nodup_ofFn.mpr (hinj.comp boundarySeamMasterRole_injective)
  have hports (pair : Fin (T+tapeCount) × Fin (T+tapeCount)) (hp : pair ∈ pairs) :
      pair.2 ≠ e 95 ∧ pair.2 ≠ e 96 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨hinj.ne (hrole i).1,hinj.ne (hrole i).2⟩
  have hdestBlank (pair : Fin (T+tapeCount) × Fin (T+tapeCount)) (hp : pair ∈ pairs) : B.R pair.2 = [] := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hblank _ (hrole i).1 (hrole i).2
  obtain ⟨v',hv,hretire⟩ := retireCopiedHeaders_pair_exec body pairs hnd (e 95) (e 96)
    (fun pair hp => (hports pair hp).1) (fun pair hp => (hports pair hp).2)
    sourceTail (output.flatten++outputTail) u' B hdestBlank depth
  refine ⟨output,haccuracy,v',((pairs.map (fun p => 6*(B.R p.1).length+6)).sum+1)+
    (m+(2*(pairs.map (fun p => (B.R p.1).length)).sum+2*pairs.length+1)),hv.trans (hu'.trans hu),?_,?_,?_⟩
  · dsimp only [pairs]
    omega
  · apply mn_replace_input_output_size_le v v' B (e 95) (e 96) (hinj.ne (by decide))
      sourceTail (output.flatten++outputTail)
    · rw [hsrc]
      simp only [List.length_append]
      omega
    · have hrowCount : output.length = ambient.length := haccuracy.length_eq.symm.trans hgood.length_eq
      have houtputLength : ∀ line ∈ output, line.length = s*W :=
        (List.forall₂_and_left _ _).mp haccuracy.flip |>.1
      have hambientLength : ∀ line ∈ ambient, line.length = s*W :=
        (List.forall₂_and_left _ _).mp hgood.flip |>.1
      rw [hdst]
      simp only [List.length_append,length_flatten_const _ houtputLength,
        length_flatten_const _ hambientLength,hrowCount]
  · have hloadStock := hl.final
    have hpubStock := hpub.final
    apply ExecWithin.seq (hl.mono (by intro d z hz; omega))
    apply ExecWithin.seq (hpub.mono (by intro d z hz; dsimp only [L,pairs] at *; omega))
    exact hretire.mono (by intro d z hz; dsimp only [L,pairs] at *; omega)

end

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
