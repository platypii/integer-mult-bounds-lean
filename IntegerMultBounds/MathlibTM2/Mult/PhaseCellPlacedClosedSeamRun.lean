module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedFullLineSeamRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchPush
public import IntegerMultBounds.MathlibTM2.Host.EmbedOwnedUpdateStock

/-! Generate ordinary full-line input, solve once, archive all seam crops and
retire the full-line result. Only the crop archive differs from the baseline. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T T' Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T' Q A U}

-- Producer-specific push coefficients can be restored from commit 2fbab5fe.
noncomputable def placedSeamProgram (e : Fin T → Fin T') (input : FullLineInputPlan T)
    (producer : PackedProducerPlan T Q) (crops : SeamCropPlan T producer.result)
    (recovery : Bool) (ks : List ℕ) : Pr P T' Q A U :=
  embProg e Empty.elim (input.runSeamCrops producer crops (P := Empty) (U := U) (A := A) recovery ks)

theorem placedSeamProgram_exec (e : Fin T → Fin T') (he : Function.Injective e) (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (hcompat : input.Compatible producer)
    (crops : SeamCropPlan T producer.result) (coreWidth : ℕ) (ks : List ℕ) (recovery : Bool) (hA : 96 ≤ A)
    {p u l target t : ℕ} [NeZero t] {d : ℝ}
    (hp : 4 ≤ p) (hst : s < t) (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : (u : ℝ)*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (htarget : p+2 ≤ target)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (v : HS T' Q A U) (S : Stacks T' A) (hready : input.Ready p u l target t Fs (embStk e S))
    (hblank : ∀ i, (embStk e S).R (producer.gridWork i) = [])
    (hleft : ∀ i, (embStk e S).L (producer.gridWork (familyInverseCoreReg i)) = [])
    (hcontrols : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock], (embStk e S).R k = [])
    (cropReady : crops.Ready p s coreWidth Fs.length ks (embStk e S))
    (hstart : ∀ k ∈ ks, coreStart coreWidth k ≤ s) (hcount : ks.length ≤ 3)
    (hresult : (embStk e S).R producer.result = [])
    (depth : ℕ) :
    let C := gridDispatchPush (U := U) (A := A) producer.hR producer.hQ
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    ∃ v' : HS T' Q A U, ∃ n : ℕ, ∃ output : List (Fin (A+4)), ∃ rss : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ solveTime+(242*volume+45) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) ks.reverse rss ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(solveStock+(480*volume+86))) depth
        (placedSeamProgram e input producer crops recovery ks) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e crops.dst)
          ((rss.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++(embStk e S).R crops.dst))}) := by
  dsimp only
  let C := gridDispatchPush (U := U) (A := A) producer.hR producer.hQ
  obtain ⟨vm,n,output,rss,hu,ht,hproduced,hcrops,heRun⟩ := input.runSeamCrops_exec
    (body := fun f : Empty => nomatch f) producer hcompat crops coreWidth ks recovery hA
    hp hst hu hwidth hθ hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ
    (embDn e v) (embStk e S) hready hblank hleft hcontrols cropReady hstart hcount hresult C
    (by
      exact gridFamilyDispatch_push_le producer.gridWork producer.src producer.saved producer.count producer.tmp
        producer.spare producer.result producer.clock producer.savedClock recovery producer.hR producer.hQ)
    (by intro f; cases f) depth
  obtain ⟨v',hu',hePlaced⟩ := exec_emb_owned_update_within e he
    (body' := body) (ι := Empty.elim) (by intro f; cases f) crops.dst
    ((rss.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++(embStk e S).R crops.dst)
    v S heRun
  exact ⟨v',n,output,rss,hu'.trans hu,ht,hproduced,hcrops,hePlaced⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
