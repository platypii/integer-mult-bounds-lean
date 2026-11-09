module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactBoundaryArchivePublication
public import IntegerMultBounds.MathlibTM2.Host.EmbedRightUpdatesStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveSequence

/-! Execute physical boundary slots through the numerical archive invariant.
Persistent controls are transported by the restored frame at every stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

theorem placedExactBoundaryArchivePublication_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e)
    (p width W D : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (cropCount : Fin 3 → Fin 117)
    (hreg : ∀ slot, [cropCount slot,15,54,19,27,28,24,26].Nodup)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (band n : ℕ) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (hready : BoundarySeamReady (s := s) p width W D r.inputs.length cropCount seedValue (embStk e S))
    (depth : ℕ) (v : HS T Q A U)
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p (2*p+13) width k
      r.inputs.reverse (J r) rows) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : CorePublicationClass.BankAccurate proper p W (seamPublicationTargets p r J) ambient (3/(2:ℝ)^p))
    (hsrc : (embStk e S).R 95 = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : (embStk e S).R 96 = ambient.flatten++outputTail) :
    ∃ lines : List (List (Fin (A+4))), ∃ v' : HS T Q A U, ∃ steps : ℕ,
      v'.user = v.user ∧ steps ≤ 3*boundarySeamCost r.inputs.length (2*p+13) D s width W+1 ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) lines ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        13*boundarySeamCost r.inputs.length (2*p+13) D s width W) depth
        (embProg e Empty.elim (boundarySeamPublication (P := Empty) cropCount))
        (mk v S) steps (mk v' {S with R := (Function.update
          (Function.update S.R (e 95) sourceTail) (e 96) (lines.flatten++outputTail))}) := by
  obtain ⟨vm,F,steps,huser,htime,hnum,hsource,hfull,hstock,hwithin⟩ :=
    exactBoundaryArchivePublication_exec (fun f : Empty => nomatch f)
      p width W D hA hW hwidth hroom hvolumeFit cropCount hreg seedValue hvalues hfit r J
      band n hr hrw proper hproper sourceTail outputTail (embStk e S) hready depth
      (embDn e v) banks hbanks ambient hgood hsrc hdst
  obtain ⟨lines,houtput,hall⟩ := hfull
  have hframe : F = {(embStk e S) with R := (Function.update
      (Function.update (embStk e S).R 95 (F.R 95)) 96 (F.R 96))} := by
    obtain ⟨bs,as,hbs,hpending,hF⟩ := hnum
    rw [hF]
    simp only [Function.update_self,Function.update_of_ne (by decide : (95 : Fin 117) ≠ 96)]
  have hfinal : F = {(embStk e S) with R := (Function.update
      (Function.update (embStk e S).R 95 sourceTail) 96 (lines.flatten++outputTail))} := by
    simpa only [hsource,houtput] using hframe
  have hlocal := hwithin.cast rfl (congrArg (mk vm) hfinal)
  obtain ⟨v',hprojection,huser',hplaced⟩ := exec_emb_ovr_within_stock (e := e) (ι := Empty.elim)
    (body' := body) he (by intro f; cases f) hlocal v rfl S rfl
  have hend : embOvr e ({(embStk e S) with R := (Function.update
      (Function.update (embStk e S).R 95 sourceTail) 96 (lines.flatten++outputTail))}).get S =
      {S with R := (Function.update (Function.update S.R (e 95) sourceTail) (e 96) (lines.flatten++outputTail))} := by
    change embOvr e (rightUpdates [(95,sourceTail),(96,lines.flatten++outputTail)] (embStk e S)).get S = _
    rw [embOvr_rightUpdates he,embOvr_stk]
    rfl
  rw [hend] at hplaced
  exact ⟨lines,v',steps,huser'.trans huser,htime,hall,hplaced⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
