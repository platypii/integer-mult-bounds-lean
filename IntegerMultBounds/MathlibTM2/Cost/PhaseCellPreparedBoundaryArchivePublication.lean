module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryHeaderBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHeaderInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryBinarySeeds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLastCropMaster
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedExactBoundaryArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOpsStock

/-! Prepare the ordinary boundary controls, consume the certified crop archive
with the existing publisher, and release all eleven owned headers. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

def boundaryHeaderLoadTrafficFactor (cD : ℕ) := 300+150*cD

def initializedBoundaryArchivePublication (e : Fin 117 → Fin T) (masters : Fin 11 → Fin 117) : Pr P T Q A U :=
  .seq (.seq (placedBoundaryHeaderLoad e (e ∘ masters))
    (embProg e Empty.elim (boundarySeamPublication (P := Empty) boundarySeamCropCount)))
    (clearWords (List.ofFn (fun i => e (boundarySeamMasterRole i))))

theorem initializedBoundaryArchivePublication_exec (body : P → Pr P T Q A U)
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
      v'.user = v.user ∧ steps ≤ boundaryHeaderLoadTrafficFactor cD*(r.inputs.length*(s*W))+
        (3*boundarySeamCost r.inputs.length (2*p+13) D s width W+1) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) lines ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (boundaryHeaderLoadTrafficFactor cD*(r.inputs.length*(s*W))+
          13*boundarySeamCost r.inputs.length (2*p+13) D s width W)) depth
        (initializedBoundaryArchivePublication e masters) (mk v S) steps
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
  · dsimp only [boundaryHeaderLoadTrafficFactor] at hn₁ ⊢
    omega
  · have hex := mn_seq_within_add (mn_seq_within_add he₁ he₂) he₃'
    exact hex.mono (by intro z state hz; dsimp only [boundaryHeaderLoadTrafficFactor] at hz ⊢; omega)

def boundaryHeaderFullTrafficFactor (cD : ℕ) := 340+150*cD

def fullBoundaryArchivePublication (e : Fin 117 → Fin T) (masters : Fin 11 → Fin 117) : Pr P T Q A U :=
  .seq (.seq (unaryProduct (e (masters 9)) (e (masters 3)) (e (masters 8)) (e 27) (e 28))
    (initializedBoundaryArchivePublication e (boundaryWorkingMasters masters))) (clearWords [e (masters 8)])

private theorem fullCropProductCosts_le (L w traffic : ℕ)
    (hvolume : L*w ≤ traffic) (hL : L ≤ traffic) (htraffic : 1 ≤ traffic) :
    (L*(4*w+9)+4)+(2*(L*w)+3) ≤ 40*traffic ∧ 2*(L*(4*w+9)+4) ≤ 40*traffic := by
  constructor <;> nlinarith only [hvolume,hL,htraffic]

theorem fullBoundaryArchivePublication_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (masters : Fin 11 → Fin 117)
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
    (input : BoundaryHeaderInput (s := s) p width W D r.inputs.length masters seedValue (embStk e S))
    (depth : ℕ) (v : HS T Q A U)
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p (2*p+13) width k
      r.inputs.reverse (J r) rows) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : CorePublicationClass.BankAccurate proper p W (seamPublicationTargets p r J) ambient (3/(2:ℝ)^p))
    (hsrc : (embStk e S).R 95 = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : (embStk e S).R 96 = ambient.flatten++outputTail) :
    ∃ lines : List (List (Fin (A+4))), ∃ v' : HS T Q A U, ∃ steps : ℕ,
      v'.user = v.user ∧ steps ≤ boundaryHeaderFullTrafficFactor cD*(r.inputs.length*(s*W))+
        (3*boundarySeamCost r.inputs.length (2*p+13) D s width W+1) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) lines ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (boundaryHeaderFullTrafficFactor cD*(r.inputs.length*(s*W))+
          13*boundarySeamCost r.inputs.length (2*p+13) D s width W)) depth
        (fullBoundaryArchivePublication e masters) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
          (e 96) (lines.flatten++outputTail))}) := by
  have hcore : (S.R (e (masters 9))).length = width := input.scalars.core
  have hnarrow : (S.R (e (masters 3))).length = 2*p+13 := input.scalars.word
  have hblank : S.R (e (masters 8)) = [] := input.fullBlank
  obtain ⟨v₀,n₀,hu₀,hn₀,hex₀⟩ := unaryProduct_exec (body := body)
    (by simpa only [List.map_cons,List.map_nil] using input.productReg.map he) v S
    (input.blank 27 (by decide) (by decide) (by decide)) (input.blank 28 (by decide) (by decide) (by decide))
  let M : Stacks T A := {S with R := Function.update S.R (e (masters 8)) (List.replicate (width*(2*p+13)) tick)}
  have he₀ : Exec body (unaryProduct (e (masters 9)) (e (masters 3)) (e (masters 8)) (e 27) (e 28))
      (mk v S) n₀ (mk v₀ M) := by
    simpa only [hcore,hnarrow,hblank,List.append_nil,M] using hex₀
  have hn₀' : n₀ ≤ width*(4*(2*p+13)+9)+4 := by simpa only [hcore,hnarrow] using hn₀
  have hw₀ := mn_native_exec_within he₀ 2 (unaryProduct_native ..) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn₀') _)
  have hframe (i : Fin T) (hi : i ≠ e (masters 8)) : M.R i = S.R i := Function.update_of_ne hi _ _
  have hlocal (i : Fin 117) (hi : i ≠ masters 8) : (embStk e M).R i = (embStk e S).R i := hframe _ (he.ne hi)
  have hfull : ((embStk e M).R (masters 8)).length = width*(2*p+13) := by
    simp only [embStk,Function.comp_apply,M,Function.update_self,List.length_replicate]
  obtain ⟨lines,v₁,n₁,hu₁,hn₁,hall,he₁⟩ := initializedBoundaryArchivePublication_exec body e he
    (boundaryWorkingMasters masters)
    (by intro i k hk; unfold boundaryWorkingMasters; split_ifs <;> exact input.separated _ k hk)
    p width W D cD hA hW hwidth hroom hvolumeFit hD seedValue hvalues hfit r hN J band n hr hrw proper hproper
    sourceTail outputTail M (input.words_of_full hwidth hroom hfull hlocal) (input.blank_of_full_frame hlocal)
    depth v₀ banks hbanks ambient hgood
    (by change M.R (e 95) = _; rw [hframe _ (he.ne (input.dataOff 8).1.symm)]; exact hsrc)
    (by change M.R (e 96) = _; rw [hframe _ (he.ne (input.dataOff 8).2.symm)]; exact hdst)
  obtain ⟨v',hu₂,he₂⟩ := retireHeaderFrame_pair_exec body [e (masters 8)] (by simp) S M rfl rfl rfl
    (by intro i hi; exact hframe i (by simpa only [List.mem_singleton] using hi))
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hblank)
    (e 95) (e 96) (by simpa only [List.mem_singleton] using he.ne (input.dataOff 8).1.symm)
    (by simpa only [List.mem_singleton] using he.ne (input.dataOff 8).2.symm)
    sourceTail (lines.flatten++outputTail) v₁ depth
  have he₂' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₁ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))})+depth+0) depth (clearWords [e (masters 8)])
      (mk v₁ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) (2*(width*(2*p+13))+3)
      (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) := by
    simpa only [M,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      Function.update_self,List.length_replicate,Nat.add_zero] using he₂
  have hline : s ≤ r.inputs.length*(s*W) :=
    (Nat.le_mul_of_pos_right s (show 1 ≤ W by omega)).trans (Nat.le_mul_of_pos_left _ hN)
  have hL : width ≤ r.inputs.length*(s*W) := (show width ≤ s by omega).trans hline
  have hv : width*(2*p+13) ≤ r.inputs.length*(s*W) :=
    (Nat.mul_le_mul (show width ≤ s by omega) hW).trans (Nat.le_mul_of_pos_left _ hN)
  have ht : 1 ≤ r.inputs.length*(s*W) := (show 1 ≤ s by omega).trans hline
  obtain ⟨htime,hspace⟩ := fullCropProductCosts_le width (2*p+13) _ hv hL ht
  refine ⟨lines,v',n₀+n₁+(2*(width*(2*p+13))+3),hu₂.trans (hu₁.trans hu₀),?_,hall,?_⟩
  · simp only [boundaryHeaderFullTrafficFactor,boundaryHeaderLoadTrafficFactor,Nat.add_mul,Nat.mul_assoc] at hn₁ ⊢
    omega
  · have hex := mn_seq_within_add (mn_seq_within_add hw₀ he₁) he₂'
    exact hex.mono (by
      intro z state hz
      simp only [boundaryHeaderFullTrafficFactor,boundaryHeaderLoadTrafficFactor,Nat.add_mul,Nat.mul_assoc] at hz ⊢
      omega)

def boundaryLastCropTrafficFactor (cD : ℕ) := 30000*(cD+1)^2

def boundaryHeaderCountedTrafficFactor (cD : ℕ) := boundaryHeaderFullTrafficFactor cD+boundaryLastCropTrafficFactor cD

def countedBoundaryArchivePublication (e : Fin 117 → Fin T) (masters : Fin 11 → Fin 117) : Pr P T Q A U :=
  .seq (.seq (embProg e Empty.elim (boundaryLastCropMaster (P := Empty) masters))
    (fullBoundaryArchivePublication e masters)) (clearWords [e (masters 10)])

private theorem lastCropMasterCosts_le (D s width w traffic cD : ℕ)
    (hvolume : coreLength s width (boundaryCropIndex s width 2)*w ≤ traffic)
    (hw : w ≤ traffic) (hD : D ≤ cD*traffic) (hDsq : D*D ≤ cD*cD*traffic) (ht : 1 ≤ traffic) :
    boundaryLastCropMasterCost D s width w+(2*(coreLength s width (boundaryCropIndex s width 2)*w)+3) ≤
        boundaryLastCropTrafficFactor cD*traffic ∧
      3*boundaryLastCropMasterCost D s width w ≤ boundaryLastCropTrafficFactor cD*traffic := by
  have hc₁ : 512*cD*cD+4229*cD+8390 ≤ boundaryLastCropTrafficFactor cD := by
    unfold boundaryLastCropTrafficFactor
    nlinarith only [Nat.zero_le cD,Nat.zero_le (cD*cD)]
  have hc₂ : 1536*cD*cD+12687*cD+25155 ≤ boundaryLastCropTrafficFactor cD := by
    unfold boundaryLastCropTrafficFactor
    nlinarith only [Nat.zero_le cD,Nat.zero_le (cD*cD)]
  constructor
  · apply le_trans _ (Nat.mul_le_mul_right traffic hc₁)
    simp only [boundaryLastCropMasterCost,BoundaryCropMetadata.preparedClippedCropCountCost,
      BoundaryCropMetadata.clippedCropCountCost,tblC,Nat.mul_zero,Nat.add_zero]
    nlinarith only [hvolume,hw,hD,hDsq,ht]
  · apply le_trans _ (Nat.mul_le_mul_right traffic hc₂)
    simp only [boundaryLastCropMasterCost,BoundaryCropMetadata.preparedClippedCropCountCost,
      BoundaryCropMetadata.clippedCropCountCost,tblC,Nat.mul_zero,Nat.add_zero]
    nlinarith only [hvolume,hw,hD,hDsq,ht]

theorem countedBoundaryArchivePublication_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (masters : Fin 11 → Fin 117)
    (p width W D cD : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D) (hD : D ≤ cD*p) (hps : p ≤ s)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A) (hN : 1 ≤ r.inputs.length)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (band n : ℕ) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (input : BoundaryHeaderSource (s := s) p width W D r.inputs.length masters seedValue (embStk e S))
    (depth : ℕ) (v : HS T Q A U)
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p (2*p+13) width k
      r.inputs.reverse (J r) rows) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : CorePublicationClass.BankAccurate proper p W (seamPublicationTargets p r J) ambient (3/(2:ℝ)^p))
    (hsrc : (embStk e S).R 95 = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : (embStk e S).R 96 = ambient.flatten++outputTail) :
    ∃ lines : List (List (Fin (A+4))), ∃ v' : HS T Q A U, ∃ steps : ℕ,
      v'.user = v.user ∧ steps ≤ boundaryHeaderCountedTrafficFactor cD*(r.inputs.length*(s*W))+
        (3*boundarySeamCost r.inputs.length (2*p+13) D s width W+1) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) lines ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (boundaryHeaderCountedTrafficFactor cD*(r.inputs.length*(s*W))+
          13*boundarySeamCost r.inputs.length (2*p+13) D s width W)) depth
        (countedBoundaryArchivePublication e masters) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
          (e 96) (lines.flatten++outputTail))}) := by
  let countWord := List.replicate (coreLength s width (boundaryCropIndex s width 2)*(2*p+13)) (tick : Fin (A+4))
  have hs : (embStk e S).R (masters 4) = binSyms D s := by
    have h := input.scalars.seeds 0
    rw [hvalues 0] at h
    exact h
  have hw : (embStk e S).R (masters 5) = binSyms D width := by
    have h := input.scalars.seeds 1
    rw [hvalues 1] at h
    exact h
  have hnarrow : 0 < 2*p+13 := by omega
  have hfitNarrow : s*(2*p+13) < 2^D := (Nat.mul_le_mul_left s hW).trans_lt hvolumeFit
  obtain ⟨u,n₀,hu₀,hn₀,heLocal⟩ := boundaryLastCropMaster_exec_within
    (fun f : Empty => nomatch f) masters input.mastersPrivate D s width (2*p+13) hwidth hnarrow hroom hfitNarrow
    (embDn e v) (embStk e S) hs hw input.scalars.ruler input.scalars.word input.lastBlank
    (by intro i hi; apply input.blank i hi <;> intro heq <;> subst i <;> omega) depth
  obtain ⟨v₀,_,hu₀',he₀⟩ := exec_emb_ovr_within_stock (e := e) (ι := Empty.elim)
    (body' := body) he (by intro f; cases f) heLocal v rfl S rfl
  let M : Stacks T A := {S with R := Function.update S.R (e (masters 10)) countWord}
  have hend : embOvr e ({(embStk e S) with R := Function.update (embStk e S).R (masters 10) countWord}).get S = M := by
    change embOvr e (rightUpdates [(masters 10,countWord)] (embStk e S)).get S = M
    rw [embOvr_rightUpdates he,embOvr_stk]
    rfl
  rw [hend] at he₀
  have hframe (i : Fin T) (hi : i ≠ e (masters 10)) : M.R i = S.R i := Function.update_of_ne hi _ _
  have hlocal (i : Fin 117) (hi : i ≠ masters 10) : (embStk e M).R i = (embStk e S).R i := hframe _ (he.ne hi)
  have hlast : ((embStk e M).R (masters 10)).length = coreLength s width (boundaryCropIndex s width 2)*(2*p+13) := by
    simp only [embStk,Function.comp_apply,M,Function.update_self,countWord,List.length_replicate]
  have ready := input.with_last hlast hlocal
  obtain ⟨lines,v₁,n₁,hu₁,hn₁,hall,he₁⟩ := fullBoundaryArchivePublication_exec body e he masters
    p width W D cD hA hW hwidth hroom hvolumeFit hD seedValue hvalues hfit r hN J band n hr hrw proper hproper
    sourceTail outputTail M ready depth v₀ banks hbanks ambient hgood
    (by change M.R (e 95) = _; rw [hframe _ (he.ne (input.dataOff 10).1.symm)]; exact hsrc)
    (by change M.R (e 96) = _; rw [hframe _ (he.ne (input.dataOff 10).2.symm)]; exact hdst)
  obtain ⟨v',hu₂,he₂⟩ := retireHeaderFrame_pair_exec body [e (masters 10)] (by simp) S M rfl rfl rfl
    (by intro i hi; exact hframe i (by simpa only [List.mem_singleton] using hi))
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact input.lastBlank)
    (e 95) (e 96) (by simpa only [List.mem_singleton] using he.ne (input.dataOff 10).1.symm)
    (by simpa only [List.mem_singleton] using he.ne (input.dataOff 10).2.symm)
    sourceTail (lines.flatten++outputTail) v₁ depth
  have he₂' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₁ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))})+depth+0) depth (clearWords [e (masters 10)])
      (mk v₁ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) (2*(coreLength s width (boundaryCropIndex s width 2)*(2*p+13))+3)
      (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) := by
    simpa only [M,countWord,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      Function.update_self,List.length_replicate,Nat.add_zero] using he₂
  let traffic := r.inputs.length*(s*W)
  have hline : s ≤ traffic := (Nat.le_mul_of_pos_right s (show 1 ≤ W by omega)).trans (Nat.le_mul_of_pos_left _ hN)
  have hwide : W ≤ traffic := (Nat.le_mul_of_pos_left W (show 1 ≤ s by omega)).trans (Nat.le_mul_of_pos_left _ hN)
  have hnarrowTraffic : 2*p+13 ≤ traffic := hW.trans hwide
  have hpTraffic : p ≤ traffic := by omega
  have hpSquare : p*p ≤ traffic := (Nat.mul_le_mul hps (show p ≤ W by omega)).trans (Nat.le_mul_of_pos_left _ hN)
  have hDcap : D ≤ cD*traffic := hD.trans (Nat.mul_le_mul_left cD hpTraffic)
  have hDsq : D*D ≤ cD*cD*traffic := (Nat.mul_le_mul hD hD).trans (by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (cD*cD) hpSquare)
  have hvolume : coreLength s width (boundaryCropIndex s width 2)*(2*p+13) ≤ traffic :=
    (Nat.mul_le_mul ((Nat.min_le_right _ _).trans (Nat.sub_le _ _)) hW).trans (Nat.le_mul_of_pos_left _ hN)
  obtain ⟨htime,hspace⟩ := lastCropMasterCosts_le D s width (2*p+13) traffic cD
    hvolume hnarrowTraffic hDcap hDsq ((show 1 ≤ s by omega).trans hline)
  dsimp only [traffic] at htime hspace
  refine ⟨lines,v',n₀+n₁+(2*(coreLength s width (boundaryCropIndex s width 2)*(2*p+13))+3),
    hu₂.trans (hu₁.trans (hu₀'.trans hu₀)),?_,hall,?_⟩
  · simp only [boundaryHeaderCountedTrafficFactor,Nat.add_mul]
    omega
  · have hex := mn_seq_within_add (mn_seq_within_add he₀ he₁) he₂'
    exact hex.mono (by
      intro z state hz
      simp only [boundaryHeaderCountedTrafficFactor,Nat.add_mul]
      omega)


def boundarySeedTrafficFactor (cD : ℕ) := 400+100*cD

def boundaryHeaderTrafficFactor (cD : ℕ) :=
  boundaryHeaderCountedTrafficFactor cD+boundarySeedTrafficFactor cD

def preparedBoundaryArchivePublication (e : Fin 117 → Fin T) (masters : Fin 11 → Fin 117) : Pr P T Q A U :=
  .seq (.seq (embProg e Empty.elim (boundaryBinarySeeds (P := Empty) masters))
    (countedBoundaryArchivePublication e masters))
    (clearWords ((boundaryBinarySeedHeaders masters).map e))

theorem preparedBoundaryArchivePublication_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (masters : Fin 11 → Fin 117)
    (p width W D cD : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D) (hD : D ≤ cD*p) (hps : p ≤ s)
    (r : FamilyDispatchInput s A) (hN : 1 ≤ r.inputs.length)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (band n : ℕ) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (input : BoundaryUnarySource (s := s) p width W D r.inputs.length masters (embStk e S))
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
  let seedValue := fun i : Fin 117 => if i = 55 then s else if i = 56 then width else W
  have hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j := by
    intro j
    fin_cases j <;> simp [seedValue,boundarySeedGlobals]
  have hsFit : s < 2^D :=
    (Nat.le_mul_of_pos_right s (show 1 ≤ W by omega)).trans_lt hvolumeFit
  have hwFit : width < 2^D := (show width ≤ s by omega).trans_lt hsFit
  have hWFit : W < 2^D :=
    (Nat.le_mul_of_pos_left W (show 1 ≤ s by omega)).trans_lt hvolumeFit
  have hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D := by
    intro j
    rw [hvalues j]
    fin_cases j
    · exact hsFit
    · exact hwFit
    · exact hWFit
  let headers := (boundaryBinarySeedHeaders masters).map e
  have hoff (k : Fin 117) (hk : ∀ j, masters (boundarySeamSeedMaster j) ≠ k) : e k ∉ headers := by
    intro h
    obtain ⟨i,hi,hei⟩ := List.mem_map.mp h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact hk j (he hei)
  have hsrcOff : e 95 ∉ headers := hoff 95 (fun j => (input.dataOff _).1)
  have hdstOff : e 96 ∉ headers := hoff 96 (fun j => (input.dataOff _).2)
  have hnd : headers.Nodup := by
    apply List.Nodup.map he
    have hr := input.seedReg
    regs_ne hr
    simp only [boundaryBinarySeedHeaders,List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil,
      boundarySeamSeedMaster,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    regs_nodup
  obtain ⟨v₀,n₀,M,hu₀,hn₀,ready,hin,hout,hleft,hframe,he₀⟩ := placedBoundaryBinarySeeds_exec_within
    body e he masters p width W D r.inputs.length seedValue hvalues
    (by intro j; rw [← hvalues j]; exact hfit j) v S input depth
  obtain ⟨lines,v₁,n₁,hu₁,hn₁,hall,he₁⟩ := countedBoundaryArchivePublication_exec body e he masters
    p width W D cD hA hW hwidth hroom hvolumeFit hD hps seedValue hvalues hfit
    r hN J band n hr hrw proper hproper sourceTail outputTail M ready depth v₀ banks hbanks ambient hgood
    (by change M.R (e 95) = _; rw [hframe _ hsrcOff]; exact hsrc)
    (by change M.R (e 96) = _; rw [hframe _ hdstOff]; exact hdst)
  obtain ⟨v',hu₂,he₂⟩ := retireHeaderFrame_pair_exec body headers hnd S M hin hout hleft hframe
    (by intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact input.seedsBlank j hj)
    (e 95) (e 96) hsrcOff hdstOff sourceTail (lines.flatten++outputTail) v₁ depth
  have hlength : (headers.map (fun i => (M.R i).length)).sum = 3*D := by
    have hseed (j : Fin 3) : (M.R (e (masters (boundarySeamSeedMaster j)))).length = D := by
      rw [show M.R (e (masters (boundarySeamSeedMaster j))) =
        binSyms D (seedValue (boundarySeedGlobals j)) from ready.scalars.seeds j]
      exact length_binSyms ..
    change ((List.ofFn (fun j : Fin 3 => e (masters (boundarySeamSeedMaster j)))).map
      (fun i => (M.R i).length)).sum = _
    rw [List.map_ofFn]
    simp only [Function.comp_apply,hseed,List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil]
    omega
  have hcount : headers.length = 3 := by simp [headers,boundaryBinarySeedHeaders]
  rw [hlength,hcount] at he₂
  have he₂' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₁ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))})+depth+0) depth (clearWords headers)
      (mk v₁ {M with R := (Function.update (Function.update M.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) (6*D+7)
      (mk v' {S with R := (Function.update (Function.update S.R (e 95) sourceTail)
        (e 96) (lines.flatten++outputTail))}) := by
    simpa only [Nat.add_zero,show 2*(3*D)+2*3+1 = 6*D+7 by omega] using he₂
  let traffic := r.inputs.length*(s*W)
  have hs : s ≤ traffic := (Nat.le_mul_of_pos_right s (show 1 ≤ W by omega)).trans (Nat.le_mul_of_pos_left _ hN)
  have hw : width ≤ traffic := (show width ≤ s by omega).trans hs
  have hwide : W ≤ traffic := (Nat.le_mul_of_pos_left W (show 1 ≤ s by omega)).trans (Nat.le_mul_of_pos_left _ hN)
  have hdc : D ≤ cD*traffic := hD.trans (Nat.mul_le_mul_left cD (hps.trans hs))
  have ht : 1 ≤ traffic := (show 1 ≤ s by omega).trans hs
  have htime : boundaryBinarySeedsCost D s width W+(6*D+7) ≤ boundarySeedTrafficFactor cD*traffic := by
    unfold boundaryBinarySeedsCost boundarySeedTrafficFactor
    nlinarith only [hs,hw,hwide,hdc,ht]
  have hspace : 2*boundaryBinarySeedsCost D s width W ≤ boundarySeedTrafficFactor cD*traffic := by
    unfold boundaryBinarySeedsCost boundarySeedTrafficFactor
    nlinarith only [hs,hw,hwide,hdc,ht]
  dsimp only [traffic] at htime hspace
  refine ⟨lines,v',n₀+n₁+(6*D+7),hu₂.trans (hu₁.trans hu₀),?_,hall,?_⟩
  · simp only [boundaryHeaderTrafficFactor,Nat.add_mul]
    omega
  · have hex := mn_seq_within_add (mn_seq_within_add he₀ he₁) he₂'
    exact hex.mono (by
      intro z state hz
      simp only [boundaryHeaderTrafficFactor,Nat.add_mul]
      omega)

end IntegerMultBounds.MathlibTM2.Cost
