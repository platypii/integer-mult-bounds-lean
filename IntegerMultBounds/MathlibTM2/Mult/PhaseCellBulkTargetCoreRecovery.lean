module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedBulkLocalRowSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedTargetCoreRecovery

/-! Execute ordinary-header bulk C-selection, generated handoff, the existing
computed principal solve and the manuscript's exact owned-row crop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  ComputedRecoveryPlan
noncomputable section
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def bulkTargetCoreProgram (b : RawRecoveryProgramBounds Q A U) : Pr P tapes Q A U :=
  .seq countedBulkSelection
    (plan.generatedRoutedTargetCoreProgram b crop rowCount (scratch 0) (scratch 1) source (scratch 2) (scratch 3))

def bulkTargetCoreTime (W V targetSpan : ℕ) (b : RawRecoveryProgramBounds Q A U)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (L k radius N : ℕ) : ℕ :=
  countedBulkSelectionCost W V targetSpan r.W r.problem.span N+
    (generatedTakePrefixCost N r.problem.span r.W+plan.croppedTime b d r radius (rows s r.problem.t L k) N)

def bulkTargetCoreReserve (W V targetSpan : ℕ) (b : RawRecoveryProgramBounds Q A U)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (L k radius N Cprog : ℕ) : ℕ :=
  3*countedBulkSelectionCost W V targetSpan r.W r.problem.span N+
    (2*generatedTakePrefixCost N r.problem.span r.W+plan.croppedReserve b d r radius (rows s r.problem.t L k) N Cprog)

/-- The reusable execution, numerical and resource contract of one owned core. -/
def bulkTargetCoreSpec (b : RawRecoveryProgramBounds Q A U) (d : InverseMasterInput s)
    (r : RawRecoveryJob s) (W V L k radius targetSpan : ℕ)
    (Fs : List (ZMod r.problem.t → GaussianInt)) (Zs : List (ZMod s → ℂ))
    (v : HS tapes Q A U) (S : Stacks tapes A) (error : ℝ) : Prop :=
    ∃ (F : Stacks tapes A) (Gs : List (ZMod s → GaussianInt)), Gs.length = Fs.length ∧
      F.R (batch 2) = S.R (batch 2) ∧ (∀ i, F.R (recovery i) = S.R (recovery i)) ∧
    ∃ v' m, v'.user = v.user ∧ m ≤ bulkTargetCoreTime W V targetSpan b d r L k radius Fs.length ∧
      Exec body (bulkTargetCoreProgram b) (Host.mk v S) m
        (Host.mk v' {F with R := (Function.update (Function.update F.R source []) (crop.reg 12)
          ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
            (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten++F.R (crop.reg 12)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (cut s r.problem.t L k) (cut s r.problem.t L (k+1)))
        (packedIntervalRead r.problem.precision r.problem.wordWidth (cut s r.problem.t L k)
          (cstream A r.problem.wordWidth (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D)++S.R (crop.reg 12)))
        z error) Zs.reverse Gs.reverse ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          bulkTargetCoreReserve W V targetSpan b d r L k radius Fs.length Cprog) depth
          (bulkTargetCoreProgram b) (Host.mk v S) m
          (Host.mk v' {F with R := (Function.update (Function.update F.R source []) (crop.reg 12)
            ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
              (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten++F.R (crop.reg 12)))})

theorem bulk_target_owned_exec (b : RawRecoveryProgramBounds Q A U)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (hmastersEq : recoveryMasterValues r.problem = d.masters)
    (W V L k radius targetOrigin targetSpan : ℕ)
    (hcore : r.problem.origin+radius = cut s r.problem.t L k)
    (hspan : r.problem.span = rows s r.problem.t L k+2*radius) (hn : 0 < r.problem.span)
    (hwide : r.problem.origin+r.problem.span+2*r.problem.t*(r.problem.origin+r.problem.span)+3*s < 2^W)
    (hwindow : ∀ j < r.problem.span, targetOrigin ≤ nearestNatural s r.problem.t (r.problem.origin+j) ∧
      nearestNatural s r.problem.t (r.problem.origin+j) < targetOrigin+targetSpan)
    (hwV : r.W < 2^V) (hspanV : targetSpan < 2^V) (hvol : targetSpan*r.W < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (Fs : List (ZMod r.problem.t → GaussianInt))
    (hfields : r.inputFields = complexComponentFields (selectedRhsFields s Fs))
    (Zs : List (ZMod s → ℂ)) (hlen : Zs.length = Fs.length)
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) = complexComponentTargets Zs)
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hready : plan.CroppedReady crop d r Fs.length radius (rows s r.problem.t L k) wl S)
    (hheaders : LocalSelectionHeaders A W V s r.problem.t r.problem.origin targetOrigin r.W r.problem.span (embStk geometry S))
    (hspanRuler : (S.R (batch 5)).length = targetSpan)
    (tail : List (Fin (A+4)))
    (hqueue : S.R (batch 2) = (Fs.flatMap fun F => cstream A r.W (cyclicInterval targetOrigin targetSpan F))++tail)
    (harchive : S.R (batch 3) = []) (hacc : S.R (batch 4) = [])
    (hdst : S.R source = []) (hline : S.R (geometry 110) = []) (hinput : S.R (plan.work 124) = [])
    (hblank : ∀ j ∈ [batch 0,batch 1,scratch 0,scratch 1,scratch 2,scratch 3], S.R j = []) :
    bulkTargetCoreSpec (body := body) b d r W V L k radius targetSpan Fs Zs v S
      (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target) := by
  unfold bulkTargetCoreSpec
  have hcounts : ∀ j ∈ [batch 0,batch 1,scratch 2,scratch 3], S.R j = [] := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> exact hblank _ (by simp)
  obtain ⟨v₁,B,m₁,hu₁,hm₁,he₁,hr₁,hpayload,hrows,hqueue₁,hrecovery,hscratch,_,htrace₁⟩ :=
    countedBulkSelection_exec (body := body) hn hwide hwindow hwV hspanV hvol hVW hA hVpos Fs tail v S hheaders
      hspanRuler hready.packet hqueue harchive hacc hdst hline hcounts hready
  let G := selectionCountsState Fs.length targetSpan r.W S
  let K := embOvr geometry B.get G
  let F : Stacks tapes A := {K with R := (Function.update (Function.update (Function.update K.R (batch 0) []) source
    (selectedWindowPayload (s := s) A r.W r.problem.origin r.problem.span targetOrigin targetSpan Fs)) (batch 1) [])}
  have hinputF : F.R (plan.work 124) = [] := (hrecovery (.work 124)).trans hinput
  have hblankF : ∀ j ∈ [scratch 0,scratch 1,scratch 2,scratch 3], F.R j = [] := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> rw [hscratch] <;> exact hblank _ (by simp)
  have htail : F.R (crop.reg 12) = S.R (crop.reg 12) := by
    rw [(RecoveryBanks.crop_ports recovery recovery_injective).2.2]
    exact hrecovery (.control .cropDst)
  obtain ⟨Gs,hGs,v₂,m₂,hu₂,hm₂,he₂,hgood,htrace₂⟩ := plan.generated_routed_target_owned_exec (body := body)
    b crop replicas_ne_count replicas_ne_spare d r hmastersEq L k radius targetOrigin targetSpan hcore hspan
    Fs hfields hwindow Zs hlen htargets wl hwl v₁ F hr₁ rowCount (scratch 0) (scratch 1) source (scratch 2) (scratch 3)
    handoff_regs (geometry_off_support 108) source_ne_output [] (by simpa only [List.append_nil] using hpayload)
    (by rw [hrows,List.length_replicate]) hinputF hblankF
  refine ⟨F,Gs,hGs,hqueue₁,hrecovery,v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ he₂,?_,?_⟩
  · simpa only [htail] using hgood
  · intro Cprog hpush hbody depth
    have ht := mn_seq_within_add (htrace₁ 0) (htrace₂ Cprog hpush hbody 0)
    simpa only [Nat.zero_add,bulkTargetCoreProgram] using ht.shift depth
      (J := fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        bulkTargetCoreReserve W V targetSpan b d r L k radius Fs.length Cprog)
      (by intro j z hz; dsimp only [bulkTargetCoreReserve]; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
