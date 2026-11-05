module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedFullLineRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamCropPlan

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
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def runSeamCrops (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (crops : SeamCropPlan T producer.result) (recovery : Bool) (ks : List ℕ) : Pr P T Q A U :=
  .seq (input.run producer recovery) (.seq (crops.program ks) (uclear producer.result))

theorem runSeamCrops_exec (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
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
    (v : HS T Q A U) (S : Stacks T A) (hready : input.Ready p u l target t Fs S)
    (hblank : ∀ i, S.R (producer.gridWork i) = [])
    (hleft : ∀ i, S.L (producer.gridWork (familyInverseCoreReg i)) = [])
    (hcontrols : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock], S.R k = [])
    (cropReady : crops.Ready p s coreWidth Fs.length ks S)
    (hstart : ∀ k ∈ ks, coreStart coreWidth k ≤ s) (hcount : ks.length ≤ 3)
    (hresult : S.R producer.result = [])
    (C : ℕ) (hpush : mnProgPush (producer.gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    ∃ v' : HS T Q A U, ∃ n : ℕ, ∃ output : List (Fin (A+4)), ∃ rss : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ solveTime+(242*volume+45) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) ks rss ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(solveStock+(480*volume+86))) depth
        (input.runSeamCrops producer crops recovery ks) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R crops.dst
          ((rss.reverse.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++S.R crops.dst))}) := by
  dsimp only
  let r := fullLineGridRecord (A := A) p u l target t Fs
  let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
  obtain ⟨v₁,n₁,output,hu₁,hn₁,hproduced,he₁⟩ := input.run_exec producer hcompat recovery hA
    hp hst hu hwidth hθ hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ v S hready hblank hleft hcontrols C hpush hbody depth
  rw [hresult,List.append_nil] at he₁
  obtain ⟨rss,v₂,n₂,hu₂,hn₂,hgood,he₂⟩ := crops.archiveRetire_exec_within p coreWidth r (fun _ => J) ks output
    hproduced hstart v₁ S cropReady hresult depth
  dsimp only [r] at he₂
  have hextra := SeamCropPlan.archiveRetire_three_cost ks hcount (r.inputs.length*s*(2*p+13))
  have hcropTime := hn₂.trans hextra.1
  dsimp only [r] at hextra
  have hpoint := he₁.final
  refine ⟨v₂,n₁+n₂,output,rss,hu₂.trans hu₁,Nat.add_le_add hn₁ hcropTime,hproduced,hgood,?_⟩
  apply ExecWithin.seq
  · exact he₁.mono (by intro d z hz; omega)
  · exact he₂.mono (by intro d z hz; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
