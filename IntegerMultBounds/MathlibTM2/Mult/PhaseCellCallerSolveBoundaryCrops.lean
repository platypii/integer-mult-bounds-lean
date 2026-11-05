module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedFullLineRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGeneratedBoundaryCropRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
  ScalarPlacement ScalarPlacement.FullLineInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P (MachineTapes T) Q A U}
noncomputable section

/-- One actual full-line solve followed by the fixed caller crop program. -/
def callerSolveBoundaryCrops (input : FullLineInputPlan (MachineTapes T))
    (producer : PackedProducerPlan (MachineTapes T) Q) (src : Fin 2 → Fin T)
    (recovery : Bool) : Pr P (MachineTapes T) Q A U :=
  .seq (input.run producer recovery)
    (embProg (boundaryCropRegister T src) (fun f : Empty => nomatch f) generatedBoundaryCropProgram)

theorem callerSolveBoundaryCrops_exec
    (input : FullLineInputPlan (MachineTapes T)) (producer : PackedProducerPlan (MachineTapes T) Q)
    (hcompat : input.Compatible producer) (src : Fin 2 → Fin T) (hsrc : Function.Injective src)
    (widthSource : Fin T) (coreWidth : ℕ) (hw : 0 < coreWidth) (hroom : 3*coreWidth < s)
    (hresult : producer.result = boundaryCropRegister T src 94) (recovery : Bool) (hA : 96 ≤ A)
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
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hready : input.Ready p u l target t Fs S)
    (hsep : ∀ slot : Fin 3,
      boundaryGeometryRegister T widthSource (boundarySeamCropSkip slot) ∉ input.support++producer.support ∧
      boundaryGeometryRegister T widthSource (boundarySeamCropCount slot) ∉ input.support++producer.support)
    (hblank : ∀ i, S.R (producer.gridWork i) = [])
    (hleft : ∀ i, S.L (producer.gridWork (familyInverseCoreReg i)) = [])
    (hcontrols : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      S.R k = [])
    (hclock : (S.R (unarySource T (src 0))).length = Fs.length)
    (hrows : (S.R (unarySource T (src 1))).length = s)
    (hword : (S.R (fullHeader T (.publication 3))).length = 2*p+13)
    (hprivate : ∀ i : Fin PackedTranspose.tapeCount, S.R (Fin.natAdd ((T+headerCount)+175) i) = [])
    (C : ℕ) (hpush : mnProgPush (producer.gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) S
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    ∃ v' n output, ∃ banks : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ solveTime+(242*volume+45) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) (boundaryCropSchedule s coreWidth).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v F)+depth+(solveStock+(480*volume+86))) depth
        (callerSolveBoundaryCrops input producer src recovery) (Host.mk v F) n
        (Host.mk v' {F with R := (Function.update F.R (boundaryCropRegister T src 95)
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (boundaryCropRegister T src 95)))}) := by
  dsimp only
  let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) S
  let r := fullLineGridRecord (A := A) p u l target t Fs
  have hread (k : Fin (MachineTapes T)) (hk : k ∈ input.support++producer.support) : F.R k = S.R k := by
    apply callerBoundaryGeometryState_off
    · intro slot he; exact (hsep slot).1 (he.symm ▸ hk)
    · intro slot he; exact (hsep slot).2 (he.symm ▸ hk)
  have hreadyF := hready.of_frame (F := F)
    (fun k hk => hread k (List.mem_append_left _ hk)) (fun _ => rfl)
  have hblankF : ∀ i, F.R (producer.gridWork i) = [] := by
    intro i
    apply (hread _ ?_).trans (hblank i)
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨Fin.castLE (by decide : 303 ≤ 325) i,rfl⟩
  have hcontrolsF : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      F.R k = [] := by
    intro k hk
    apply (hread k ?_).trans (hcontrols k hk)
    apply List.mem_append_right
    apply List.mem_append_right
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    tauto
  have hsource : F.R producer.result = [] := by
    rw [hresult,boundaryCropRegister_private T src 94 (by decide +kernel)]
    exact (callerBoundaryGeometryState_private widthSource s coreWidth (2*p+13) S _).trans (hprivate _)
  obtain ⟨v₁,n₁,output,hu₁,hn₁,hproduced,he₁⟩ := input.run_exec producer hcompat recovery hA
    hp hst hu hwidth hθ hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ v F
    hreadyF hblankF hleft hcontrolsF C hpush hbody depth
  rw [hsource,List.append_nil,hresult] at he₁
  obtain ⟨banks,v₂,n₂,hu₂,hn₂,hbanks,he₂⟩ := callerGeneratedBoundaryCropRun_exec body src hsrc widthSource
    p coreWidth hw hroom r (fun _ => J) output hproduced v₁ S hclock hrows hword hprivate depth
  refine ⟨v₂,n₁+n₂,output,banks,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hproduced,hbanks,?_⟩
  exact mn_seq_within_add he₁ he₂

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
