module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPlan
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeamArchive
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalGridInput

/-! One retained full-period solve uses the existing supplier wiring. Its
borrowed bank, descriptor suffix and generated clock restore on return. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem control_mem (plan : PackedProducerPlan T Q) (k : Fin T)
    (hk : k ∈ [plan.src,plan.saved,plan.count,plan.tmp,plan.spare,plan.clock,plan.savedClock,plan.result]) :
    k ∈ plan.support++[plan.result] := by
  have hm : k ∈ [plan.src,plan.saved,plan.count,plan.tmp,plan.spare,plan.clock,plan.savedClock]++[plan.result] := by
    simpa only [List.cons_append,List.nil_append] using hk
  have hh := List.mem_append_right (List.ofFn plan.work) hm
  rw [← List.append_assoc] at hh
  exact hh

/-- The existing 325-port supplier wiring contains the 303-port S3 dispatcher. -/
def gridWork (plan : PackedProducerPlan T Q) (i : Fin 303) : Fin T := plan.work (Fin.castLE (by decide) i)

theorem gridWork_injective (plan : PackedProducerPlan T Q) : Function.Injective plan.gridWork := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 325 => k.val) (plan.hwork h))

noncomputable def gridProgram (plan : PackedProducerPlan T Q) (recovery : Bool) : Pr P T Q A U :=
  gridFamilyDispatch plan.gridWork plan.src plan.saved plan.count plan.tmp plan.spare plan.result
    plan.clock plan.savedClock recovery plan.hR plan.hQ

noncomputable def gridStock (plan : PackedProducerPlan T Q) (p l t : ℕ) (r : FamilyDispatchInput s A) : ℕ :=
  ([r].map (fun r => r.gridStock p l t plan.gridWork)).sum+6*[r].length+
    2*(descriptorScheduleTape plan.gridWork FamilyDispatchInput.words [r]).length+8

noncomputable def fullLineFromLiveBank (plan : PackedProducerPlan T Q) (source : Fin 303 → Fin T)
    (recovery : Bool) : Pr P T Q A U :=
  .seq (prepareDescriptorBank source plan.src plan.tmp plan.saved plan.clock)
    (.seq (plan.gridProgram recovery) (releaseDescriptorBank plan.src plan.count plan.tmp plan.clock 303))

private theorem total_time (prep run retire cost tape : ℕ)
    (hp : prep ≤ 11*tape+2) (hr : run ≤ cost+2*tape+19) (he : retire ≤ 9*tape+5) :
    prep+(run+retire) ≤ cost+22*tape+26 := by omega

private theorem singleton_time {β : Type} (cost : β → ℕ) (tape : List β → ℕ) (r : β) (n : ℕ)
    (h : n ≤ ([r].map (fun r => cost r+3)).sum+6*[r].length+2*tape [r]+10) :
    n ≤ cost r+2*tape [r]+19 := by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at h
  omega

private theorem stock_regroup (base depth tape stock x : ℕ)
    (h : x ≤ base+depth+((22*tape+4)+(stock+(9*tape+5)))) :
    x ≤ base+depth+(31*tape+9+stock) := by omega

theorem fullLineFromLiveBank_exec (plan : PackedProducerPlan T Q) (source : Fin 303 → Fin T)
    (hsourceReg : ∀ i, [source i,plan.src,plan.tmp,plan.saved].Nodup)
    (recovery : Bool) (hA : 96 ≤ A) {p l t : ℕ} [NeZero t] {d : ℝ}
    (hp : 4 ≤ p) (hst : s < t) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (r : FamilyDispatchInput s A) (hr : GridDispatchReady p l t d r)
    (ha : r.a = 0) (hb : r.b = s) (htarget : p+2 ≤ r.target)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
    (v : HS T Q A U) (S : Stacks T A) (hwords : ∀ i, S.R (source i) = r.words i)
    (hblank : ∀ i, S.R (plan.gridWork i) = [])
    (hleft : ∀ i, S.L (plan.gridWork (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (C : ℕ) (hpush : mnProgPush (plan.gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let tape := descriptorScheduleTape plan.gridWork FamilyDispatchInput.words [r]
    ∃ v' n output, v'.user = v.user ∧ n ≤ r.gridCost p l t plan.gridWork+22*tape.length+26 ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (31*tape.length+9+(C+1)*plan.gridStock p l t r)) depth
        (plan.fullLineFromLiveBank source recovery) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R plan.result (output++S.R plan.result)}) := by
  dsimp only
  have hregs := plan.hreg
  regs_ne hregs
  have hsep : ∀ i, plan.gridWork i ∉ [plan.src,plan.saved,plan.count,plan.tmp,plan.spare,plan.result,plan.clock,plan.savedClock] :=
    fun i => plan.hsep _
  have hoff (i : Fin T) (hi : i ∈ [plan.count,plan.tmp,plan.spare,plan.saved,plan.savedClock,plan.result]) :
      i ≠ plan.src ∧ i ≠ plan.clock := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)
  let tape := descriptorScheduleTape plan.gridWork FamilyDispatchInput.words [r]
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R plan.src (tape++S.R plan.src)) plan.clock [tick])}
  have htape : descriptorBankTape ((List.ofFn source).map (fun i => (i,S.R i))) = tape := by
    have h := descriptorBankTape_sources_eq source plan.gridWork r.words S.R hwords
    simpa only [tape,descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil] using h
  obtain ⟨v₁,hu₁,he₁⟩ := prepareDescriptorBank_exec (body := body) source plan.src plan.tmp plan.saved plan.clock
    hsourceReg ‹plan.src ≠ plan.clock›.symm v S (hscratch _ (by simp)) hsaved hclock depth
  rw [htape] at he₁
  have hM (i : Fin T) (his : i ≠ plan.src) (hic : i ≠ plan.clock) : M.R i = S.R i := by
    simp only [M,Function.update_of_ne his,Function.update_of_ne hic]
  have hfull : haloVertices s r.a r.b = Finset.univ := by rw [ha,hb,haloVertices_full]
  have hscratchM : ∀ i ∈ [plan.count,plan.tmp,plan.spare], M.R i = [] := by
    intro i hi
    have hh := hscratch i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact (hM plan.count ‹plan.src ≠ plan.count›.symm ‹plan.count ≠ plan.clock›).trans hh
    · exact (hM plan.tmp ‹plan.src ≠ plan.tmp›.symm ‹plan.tmp ≠ plan.clock›).trans hh
    · exact (hM plan.spare ‹plan.src ≠ plan.spare›.symm ‹plan.spare ≠ plan.clock›).trans hh
  have hsavedM := (hM plan.saved ‹plan.src ≠ plan.saved›.symm ‹plan.saved ≠ plan.clock›).trans hsaved
  have hsavedClockM := (hM plan.savedClock ‹plan.src ≠ plan.savedClock›.symm
    ‹plan.clock ≠ plan.savedClock›.symm).trans hsavedClock
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,he₂,hcert,hstock⟩ := gridFamilyDispatch_exact_core_exec_trace (body := body)
    plan.gridWork plan.gridWork_injective plan.src plan.saved plan.count plan.tmp plan.spare plan.result plan.clock plan.savedClock
    plan.hreg hsep recovery plan.hR plan.hQ hA hp hst hθ hgap [r] (by simpa using hr)
    (fun _ => X) (fun _ => Y) (by
      intro r' hr' F hF
      have heq := List.mem_singleton.mp hr'
      subst r'
      simpa only [hfull] using hX F hF)
    (by
      intro r' hr' F hF
      have heq := List.mem_singleton.mp hr'
      subst r'
      simpa only [hfull] using hY F hF) s r.target (fun _ => 0)
    (by simpa [ha,hb] using fullLine_generated_halo (s := s) p r.u r.target)
    (fun _ => X) (fun _ => Y) (by simpa using hX) (by simpa using hY)
    htarget (by simp) (fun _ => J) (by simpa using hJ) v₁ M (S.R plan.src)
    (by
      intro i
      have hi := hsep i
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
      rw [hM _ hi.1 hi.2.2.2.2.2.2.1]
      exact hblank i)
    hleft
    hscratchM
    (by simp only [M,Function.update_of_ne ‹plan.src ≠ plan.clock›,Function.update_self]; rfl)
    (by simp [M]) hsavedM hsavedClockM
  obtain ⟨output,houtputs,hproduced⟩ : ∃ output, outputs = [output] ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output := by
    cases hcert with
    | cons hprod hrest => cases hrest; exact ⟨_,rfl,hprod⟩
  subst outputs
  have hout : [output].reverse.flatten = output := by simp
  rw [hout] at he₂ hstock
  let F : Stacks T A := {M with R := Function.update M.R plan.result (output++M.R plan.result)}
  have hMF (i : Fin T) (hir : i ≠ plan.result) : F.R i = M.R i := Function.update_of_ne hir _ _
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseDescriptorBank_exec (body := body) plan.gridWork r.words
    plan.src plan.count plan.tmp plan.clock (by regs_nodup) (S.R plan.src) v₂ F
    (by simpa only [hMF _ ‹plan.src ≠ plan.result›,M,Function.update_of_ne ‹plan.src ≠ plan.clock›,Function.update_self,
      tape,descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil])
    (by rw [hMF _ ‹plan.count ≠ plan.result›,hM plan.count (hoff plan.count (by simp)).1 (hoff plan.count (by simp)).2]; exact hscratch _ (by simp))
    (by rw [hMF _ ‹plan.tmp ≠ plan.result›,hM plan.tmp (hoff plan.tmp (by simp)).1 (hoff plan.tmp (by simp)).2]; exact hscratch _ (by simp))
    (by simp [F,M,‹plan.result ≠ plan.clock›.symm]) depth
  have htapePlaced : descriptorBankTape (placedDescriptorFields plan.gridWork r.words) = tape := by
    simp only [tape,descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [htapePlaced] at hn₃ he₃
  have hprep := emitDescriptorBankCost_le S.R (List.ofFn source)
  rw [htape] at hprep
  have hprepTime : emitDescriptorBankCost S.R (List.ofFn source)+1 ≤ 11*tape.length+2 := by omega
  have hrunTime := singleton_time (fun r : FamilyDispatchInput s A => r.gridCost p l t plan.gridWork)
    (fun records => (descriptorScheduleTape plan.gridWork FamilyDispatchInput.words records).length) r n₂ hn₂
  have htime := total_time _ _ _ _ _ hprepTime hrunTime hn₃
  have hw₂ := hstock C hpush hbody depth
  change ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v₁ M)+depth+(C+1)*plan.gridStock p l t r)
    depth (plan.gridProgram recovery) (Host.mk v₁ M) n₂ (Host.mk v₂ F) at hw₂
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add hw₂ he₃)
  have hfinal : {F with R := (Function.update (Function.update F.R plan.src (S.R plan.src)) plan.clock [])} =
      {S with R := Function.update S.R plan.result (output++S.R plan.result)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = plan.clock
    · subst i; simp [F,M,hclock,‹plan.result ≠ plan.clock›.symm]
    by_cases his : i = plan.src
    · subst i; simp [F,M,hic,‹plan.src ≠ plan.result›]
    by_cases hir : i = plan.result
    · subst i; simp [F,M,hic,his]
    · simp [F,M,hic,his,hir]
  rw [hfinal] at hwhole
  refine ⟨v₃,_,output,hu₃.trans (hu₂.trans hu₁),htime,hproduced,?_⟩
  exact hwhole.mono (by intro d z hz; exact stock_regroup _ _ _ _ _ hz)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
