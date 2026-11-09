module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryHeaderBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHeaderInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedExactBoundaryArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Prepare the ordinary boundary controls, consume the certified crop archive
with the existing publisher, and release all eleven owned headers. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

def boundaryHeaderTrafficFactor (cD : ℕ) := 300+150*cD

def preparedBoundaryArchivePublication (e : Fin 117 → Fin T) (masters : Fin 11 → Fin 117) : Pr P T Q A U :=
  .seq (.seq (placedBoundaryHeaderLoad e (e ∘ masters))
    (embProg e Empty.elim (boundarySeamPublication (P := Empty) boundarySeamCropCount)))
    (clearWords (List.ofFn (fun i => e (boundarySeamMasterRole i))))

theorem preparedBoundaryArchivePublication_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (masters : Fin 11 → Fin 117)
    (hsep : ∀ i, ∀ k ∈ List.ofFn boundarySeamMasterRole++[27,28], masters i ≠ k)
    (p width W D cD : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D) (hD : D ≤ cD*p)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A) (hN : 1 ≤ r.inputs.length)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (band n : ℕ) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (hwords : BoundarySeamHeaderWords (s := s) p width W D r.inputs.length seedValue
      (fun i => S.R (e (masters i))))
    (hblank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R (e i) = [])
    (depth : ℕ) (v : HS T Q A U)
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p (2*p+13) width k
      r.inputs.reverse (J r) rows) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : CorePublicationClass.BankAccurate proper p W (seamPublicationTargets p r J) ambient (3/(2:ℝ)^p))
    (hsrc : (embStk e S).R 95 = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : (embStk e S).R 96 = ambient.flatten++outputTail) :
    ∃ lines : List (List (Fin (A+4))), ∃ v' : HS T Q A U, ∃ steps : ℕ,
      v'.user = v.user ∧ steps ≤ boundaryHeaderTrafficFactor cD*(r.inputs.length*(s*W))+
        (3*boundarySeamCost r.inputs.length (2*p+13) D s width W+1) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) lines ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (boundaryHeaderTrafficFactor cD*(r.inputs.length*(s*W))+
          13*boundarySeamCost r.inputs.length (2*p+13) D s width W)) depth
        (preparedBoundaryArchivePublication e masters) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
          (e 96) (lines.flatten++outputTail))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,ready,hframe,he₁⟩ := placedBoundaryHeaderLoad_exec_within_traffic body e he
    (e ∘ masters) (fun i k hk => he.ne (hsep i k hk)) p width W D r.inputs.length cD seedValue
    (Nat.pos_of_ne_zero (NeZero.ne s)) hN hW hD v S hwords hblank depth
  let M : Stacks T A := {S with R := copyWordHeadersR S.R (placedBoundaryHeaderPairs e (e ∘ masters)) S.R}
  let headers := List.ofFn (fun i => e (boundarySeamMasterRole i))
  have hsourceOff : e 95 ∉ headers := by
    intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.1 (he hi)
  have houtputOff : e 96 ∉ headers := by
    intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.2.1 (he hi)
  have hread (i : Fin T) (hi : i ∉ headers) : M.R i = S.R i := by
    exact hframe i (fun j hj => hi (List.mem_ofFn.mpr ⟨j,hj⟩))
  have hblankHeaders : ∀ i ∈ headers, S.R i = [] := by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    have hb : ∀ j, (boundarySeamMasterRole j).val < 63 := by decide +kernel
    have h := boundarySeamMasterRole_off j
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact hblank _ (hb j) h.1 h.2.1
  have hcropReg : ∀ slot, [boundarySeamCropCount slot,15,54,19,27,28,24,26].Nodup := by decide +kernel
  obtain ⟨lines,v₂,n₂,hu₂,hn₂,hall,he₂⟩ := placedExactBoundaryArchivePublication_exec body e he
    p width W D hA hW hwidth hroom hvolumeFit boundarySeamCropCount hcropReg seedValue hvalues hfit r J
    band n hr hrw proper hproper sourceTail outputTail M ready depth v₁ banks hbanks ambient hgood
    (by change M.R (e 95) = _; rw [hread _ hsourceOff]; exact hsrc)
    (by change M.R (e 96) = _; rw [hread _ houtputOff]; exact hdst)
  obtain ⟨v',hu₃,he₃⟩ := retireHeaderFrame_pair_exec body headers
    (List.nodup_ofFn.mpr (he.comp boundarySeamMasterRole_injective)) S M rfl rfl rfl hread hblankHeaders
    (e 95) (e 96) hsourceOff houtputOff sourceTail (lines.flatten++outputTail) v₂ depth
  have he₃' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₂ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))})+depth+0) depth (clearWords headers)
      (mk v₂ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))})
      (2*(headers.map (fun i => (M.R i).length)).sum+23)
      (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) := by
    simpa only [headers,List.length_ofFn,Nat.add_zero] using he₃
  have hn₁' : n₁+(2*(headers.map (fun i => (M.R i).length)).sum+23) ≤
      (300+150*cD)*(r.inputs.length*(s*W)) := hn₁
  refine ⟨lines,v',n₁+n₂+(2*(headers.map (fun i => (M.R i).length)).sum+23),hu₃.trans (hu₂.trans hu₁),?_,hall,?_⟩
  · dsimp only [boundaryHeaderTrafficFactor] at hn₁ ⊢
    omega
  · have hex := mn_seq_within_add (mn_seq_within_add he₁ he₂) he₃'
    exact hex.mono (by intro z state hz; dsimp only [boundaryHeaderTrafficFactor] at hz ⊢; omega)

end IntegerMultBounds.MathlibTM2.Cost
