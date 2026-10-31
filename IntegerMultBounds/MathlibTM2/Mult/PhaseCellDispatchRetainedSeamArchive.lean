module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeamArchive

/-! Execute one full-line descriptor batch and a certified seam crop.
The returned full output and its certificate remain available for subsequent
crops, while the replica clock and every crop control are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem dispatchRetainedSeamArchive_exec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (archiveClock archiveClockSave sourceSave skip rowSymbols dst savedSkip savedRow cropTmp rows wordWidth retireCount trash retireTmp : Fin T)
    (harchive : [archiveClock,archiveClockSave,sourceSave,skip,rowSymbols,result,dst,savedSkip,savedRow,cropTmp,rows,wordWidth,retireCount,trash,retireTmp].Nodup)
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} [NeZero t] {d : ℝ} (hp : 4 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (r : FamilyDispatchInput s A) (hr : GridDispatchReady p l t d r) (htarget : p+2 ≤ r.target)
    (coreWidth k : ℕ) (hstart : coreStart coreWidth k ≤ s)
    (ha : r.a = 0) (hb : r.b = s)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ i ∈ [count,tmp,spare], S.R i = [])
    (hsource : S.R src = descriptorScheduleTape work FamilyDispatchInput.words [r]++rest)
    (hclock : (S.R clock).length = 1) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) (hresult : S.R result = [])
    (harchiveClock : (S.R archiveClock).length = r.inputs.length)
    (hskip : (S.R skip).length = coreStart coreWidth k*(2*p+13))
    (hrowSymbols : (S.R rowSymbols).length = coreLength s coreWidth k*(2*p+13))
    (hrows : (S.R rows).length = s) (hwordWidth : (S.R wordWidth).length = 2*p+13)
    (hclean : ∀ i ∈ [archiveClockSave,sourceSave,savedSkip,savedRow,cropTmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ output : List (Fin (A+4)), ∃ coreRows : List (List GaussianInt), ∃ v' F n, v'.user = v.user ∧
      n ≤ r.gridCost p l t work+2*(descriptorScheduleTape work FamilyDispatchInput.words [r]).length+19+
        (r.inputs.length*(packedCoreArchiveStepCost (coreStart coreWidth k) (coreLength s coreWidth k) s (2*p+13)+3)+2+6*output.length+6*r.inputs.length+12) ∧
      Exec body (.seq (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (retainedSeamArchive archiveClock archiveClockSave sourceSave skip rowSymbols result dst savedSkip savedRow cropTmp rows wordWidth retireCount trash retireTmp))
        (mk v S) n (mk v' F) ∧
      F.R result = output ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      F.R dst = cstream A (2*p+13) coreRows.flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ result → i ≠ dst → F.R i = S.R i) ∧
      (∀ row ∈ coreRows, row.length = coreLength s coreWidth k) ∧
      List.Forall₂ (fun input row =>
        let out := packedIntervalRead p (2*p+13) (coreStart coreWidth k)
          (cstream A (2*p+13) row)
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun i => value p (input i)))
          (3/(2 : ℝ)^p)) r.inputs.reverse coreRows := by
  obtain ⟨v₁,n₁,outputs,hu₁,hn₁,he₁,ha,_⟩ := gridFamilyDispatch_exact_core_exec_trace (body := body)
    work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA
    hp hst hθ hgap [r] (by simpa using hr) (fun _ => X) (fun _ => Y)
    (by
      intro r' hr'
      have heq := List.mem_singleton.mp hr'
      subst r'
      simpa only [ha,hb,fullLine_generated_halo p r.u r.target,generatedWindow_entire] using hX)
    (by
      intro r' hr'
      have heq := List.mem_singleton.mp hr'
      subst r'
      simpa only [ha,hb,fullLine_generated_halo p r.u r.target,generatedWindow_entire] using hY) s r.target (fun _ => 0)
    (by simpa [ha,hb] using fullLine_generated_halo (s := s) p r.u r.target) (fun _ => X) (fun _ => Y) (by simpa using hX) (by simpa using hY)
    htarget (by simp) (fun _ => J) (by simpa using hJ) v S rest hblank hleft hscratch hsource
    (by simpa using hclock) hsaved hsavedClock
  obtain ⟨output,houtputs,hproduced⟩ : ∃ output, outputs = [output] ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output := by
    cases ha with
    | cons hprod hrest => cases hrest; exact ⟨_,rfl,hprod⟩
  subst outputs
  let S₁ : Stacks T A := {S with R := Function.update S.R result (output++S.R result)}
  have he₁' : Exec body (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
      (mk v S) n₁ (mk v₁ S₁) := by simpa [S₁] using he₁
  have hn₁' : n₁ ≤ r.gridCost p l t work+2*(descriptorScheduleTape work FamilyDispatchInput.words [r]).length+19 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_singleton] at hn₁
    omega
  have hr' := harchive
  regs_ne hr'
  have hstable (i : Fin T) (hi : i ≠ result) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨coreRows,v₂,F,n₂,hu₂,hn₂,he₂,hd,hi,ho,hl,hframe,hrowLength,haccuracy⟩ := retainedSeamArchive_exec (body := body)
    archiveClock archiveClockSave sourceSave skip rowSymbols result dst savedSkip savedRow cropTmp rows wordWidth retireCount trash retireTmp harchive
    v₁ S₁ p coreWidth k r (fun _ => J) output hproduced hstart (by simp [S₁,hresult])
    (by rw [hstable _ ‹archiveClock ≠ result›]; exact harchiveClock)
    (by rw [hstable _ ‹skip ≠ result›]; exact hskip)
    (by rw [hstable _ ‹rowSymbols ≠ result›]; exact hrowSymbols)
    (by rw [hstable _ ‹result ≠ rows›.symm]; exact hrows)
    (by rw [hstable _ ‹result ≠ wordWidth›.symm]; exact hwordWidth)
    (by
      intro i hi
      have hne : i ≠ result := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable i hne]
      exact hclean i hi)
  refine ⟨output,coreRows,v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁' hn₂,Exec.seq he₁' he₂,?_,hproduced,?_,hi,ho,hl,?_,hrowLength,haccuracy⟩
  · rw [hframe result ‹result ≠ dst›]
    simp [S₁,hresult]
  · simpa only [hstable _ ‹result ≠ dst›.symm] using hd
  · intro i hir hid
    exact (hframe i hid).trans (hstable i hir)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
