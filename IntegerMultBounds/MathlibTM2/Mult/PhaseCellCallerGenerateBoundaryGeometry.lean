module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryState
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateBoundaryGeometry
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Generate three crop counts and their skips in actual caller headers. Only retained dimension
words, a unary narrow ruler and blank private routing storage are inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def callerBoundaryGeometryProgram (widthSource : Fin T) : Pr P (MachineTapes T) Q A U :=
  embProg (boundaryGeometryRegister T widthSource) (fun f : Empty => nomatch f) generateBoundaryGeometry

theorem callerBoundaryGeometry_exec (body : P → Pr P (MachineTapes T) Q A U)
    (widthSource : Fin T) (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w)
    (hroom : 3*width < s) (hvolumeFit : s*w < 2^D)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hs : S.R (globals T 4) = binSyms D s) (hwidth : S.R (globals T 10) = binSyms D width)
    (hwordLength : (S.R (fullHeader T (.publication 3))).length = w)
    (hzero : S.R (fullHeader T .zero) = [])
    (hskip : ∀ j : Fin 2, S.R (fullHeader T (.publication ⟨4+j.val,by omega⟩)) = [])
    (hblank : ∀ slot : Fin 3, S.R (fullHeader T (.publication (Fin.castAdd 4 slot))) = [])
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd ((T+headerCount)+175) i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (w*(4*D+10)+4*D+8)+boundaryCountExportCost D s width w+(2*D+2) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(4*D+4)+3*boundaryCountExportCost D s width w)) depth
        (callerBoundaryGeometryProgram widthSource) (mk v S) n
        (mk v' (callerBoundaryGeometryState widthSource s width w S)) := by
  let e := boundaryGeometryRegister T widthSource
  let value := fun i : Fin 117 => if i = 55 then s else if i = 56 then width else w
  have hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j := by
    intro j; fin_cases j <;> simp [value,boundarySeedGlobals]
  have hsW : s ≤ s*w := by nlinarith
  have hwW : w ≤ s*w := by nlinarith
  have hfit : ∀ j, value (boundarySeedGlobals j) < 2^D := by
    intro j
    rw [hvalues j]
    fin_cases j
    · change s < 2^D; omega
    · change width < 2^D; omega
    · change w < 2^D; omega
  have hblankLocal (i : Fin 117) (hi : i ∉ List.ofFn boundaryCountKeys)
      (hskip : ∀ j, boundarySkipKeys j ≠ i) : (embStk e S).R i = [] := by
    change S.R (e i) = []
    dsimp only [e]
    rw [boundaryGeometryRegister_existing T widthSource i hskip]
    rw [boundaryCountRegister_private T widthSource i (by
      intro j he; exact hi (List.mem_ofFn.mpr ⟨j,he⟩))]
    exact hprivate _
  have hsmall (i : Fin 117) (hi : i ∈ [(59:Fin 117),26,24,27,28,57]) : (embStk e S).R i = [] := by
    have hcheck : ∀ i ∈ [(59:Fin 117),26,24,27,28,57], i ∉ List.ofFn boundaryCountKeys := by decide +kernel
    exact hblankLocal i (hcheck i hi) (by
      have hcheckSkip : ∀ i ∈ [(59:Fin 117),26,24,27,28,57], ∀ j, boundarySkipKeys j ≠ i := by decide +kernel
      exact hcheckSkip i hi)
  have htable : ∀ r, (embStk e S).R (boundaryCounterRegister r) = [] := by
    intro r
    have hcheck : ∀ i : Fin 117, 30 ≤ i.val → i.val < 54 → i ∉ List.ofFn boundaryCountKeys := by decide +kernel
    exact hblankLocal _ (hcheck _ (boundaryCounterRegister_bounds r).1 (boundaryCounterRegister_bounds r).2) (by
      have hcheckSkip : ∀ i : Fin 117, 30 ≤ i.val → i.val < 54 → ∀ j, boundarySkipKeys j ≠ i := by decide +kernel
      exact hcheckSkip _ (boundaryCounterRegister_bounds r).1 (boundaryCounterRegister_bounds r).2)
  have hwords : ∀ j : Fin 3, j ≠ 2 →
      (embStk e S).R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)) := by
    intro j hj
    rw [hvalues j]
    fin_cases j
    · change S.R (e 55) = binSyms D s
      simpa only [e,boundaryGeometryRegister_line] using hs
    · change S.R (e 56) = binSyms D width
      simpa only [e,boundaryGeometryRegister_width] using hwidth
    · exact (hj rfl).elim
  obtain ⟨u,n,hu,hn,he⟩ := generateBoundaryGeometry_exec (fun f : Empty => nomatch f)
    D s width w hw hword hroom hvolumeFit value hvalues hfit (embDn e v) (embStk e S)
    (by simpa only [embStk,Function.comp_apply,e,boundaryGeometryRegister_ruler] using hD)
    (hsmall 59 (by simp)) hwords htable ⟨hsmall 26 (by simp),hsmall 24 (by simp)⟩
    (by simpa only [embStk,Function.comp_apply,e,boundaryGeometryRegister_word] using hwordLength)
    (hsmall 27 (by simp)) (hsmall 28 (by simp)) (hsmall 57 (by simp))
    (by
      intro slot
      constructor
      · fin_cases slot
        · change S.R (boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0)) = []
          rw [boundaryGeometryRegister_zero]; exact hzero
        · change S.R (boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1)) = []
          rw [boundaryGeometryRegister_skip_one]; exact hskip 0
        · change S.R (boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2)) = []
          rw [boundaryGeometryRegister_skip_two]; exact hskip 1
      · simpa only [embStk,Function.comp_apply,e,boundaryGeometryRegister_count] using hblank slot) depth
  obtain ⟨v',hdn,huser,htrace⟩ := exec_emb_ovr_within_stock e (boundaryGeometryRegister_injective T widthSource)
    (ι := fun f : Empty => nomatch f) (body' := body) (by intro f; exact nomatch f) he v rfl S rfl
  have hend := callerBoundaryGeometryState_eq widthSource s width w S
  rw [hend] at htrace
  exact ⟨v',n,huser.trans hu,hn,htrace⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
