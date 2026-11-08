module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellActualBulkTargetCoreRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPublicationHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! The ordinary-header bulk caller instantiated on the actual floor-owned job.
Reference solutions, master agreement and component order are constructed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.NLogN.PhaseCellMatrix
  ComputedRecoveryPlan
noncomputable section
variable {s t p u l Q A : ℕ} [NeZero s] {α gap : ℝ} {P U : Type} {body : P → Pr P tapes Q A U}

def bulkPublishedProgram (b : RawRecoveryProgramBounds Q A U) : Pr P tapes Q A U :=
  .seq (bulkTargetCoreProgram b) normalizeQueue.normalizeProgram

theorem bulk_published_exec_ofAxisBounds (b : RawRecoveryProgramBounds Q A U)
    (axis : RecoveryAxisBounds s t p u l α gap) (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (W V targetOrigin targetSpan : ℕ)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let radius := localityDepth p target*PhaseCellBand.width p u
    let d := axis.ownedMasterInput target L k hnear hL ha hb
    let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
    let Zs := axis.ownedTargets target L k hnear hL ha hb hfit Fs
    ∀
    (_ : r.problem.origin+r.problem.span+2*t*(r.problem.origin+r.problem.span)+3*s < 2^W)
    (_ : ∀ j < r.problem.span, targetOrigin ≤ nearestNatural s t (r.problem.origin+j) ∧
      nearestNatural s t (r.problem.origin+j) < targetOrigin+targetSpan)
    (_ : r.W < 2^V) (_ : targetSpan < 2^V) (_ : targetSpan*r.W < 2^V)
    (_ : V ≤ W) (_ : 4 ≤ A) (_ : 0 < V)
    (wl : List (Fin (A+4))) (_ : wl.length = d.B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (_ : plan.CroppedReady crop d r Fs.length radius (rows s t L k) wl S)
    (_ : LocalSelectionHeaders A W V s t r.problem.origin targetOrigin r.W r.problem.span (embStk geometry S))
    (_ : (S.R (batch 5)).length = targetSpan)
    (tail : List (Fin (A+4)))
    (_ : S.R (batch 2) = (Fs.flatMap fun F => cstream A r.W (cyclicInterval targetOrigin targetSpan F))++tail)
    (_ : S.R (batch 3) = []) (_ : S.R (batch 4) = [])
    (_ : S.R source = []) (_ : S.R (geometry 110) = []) (_ : S.R (plan.work 124) = [])
    (_ : ∀ j ∈ [batch 0,batch 1,scratch 0,scratch 1,scratch 2,scratch 3], S.R j = [])
    (Cprog depth : ℕ)
    (_ : mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) plan.work plan.src plan.saved plan.count plan.tmp plan.spare
        plan.result b.hR b.hQ)) ≤ Cprog)
    (_ : ∀ f, mnProgPush (body f) ≤ Cprog),
    ∃ (F : Stacks tapes A) (Gs : List (ZMod s → GaussianInt)), Gs.length = Fs.length ∧
      F.R (batch 2) = S.R (batch 2) ∧ (∀ i, F.R (recovery i) = S.R (recovery i)) ∧
    let output := (Gs.map (fun D => cstream A r.W (packedInterval (cut s t L k) (rows s t L k) D))).flatten++F.R (crop.reg 12)
    let final : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) output}
    ∃ v' n, v'.user = v.user ∧
      n ≤ bulkTargetCoreTime W V targetSpan b d r L k radius Fs.length+
        RecoveryParameterQueue.prepareTimeCost d+RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Fs.length ∧
      Exec body (bulkPublishedProgram b) (Host.mk v S) n (Host.mk v' final) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
        (packedIntervalRead p r.W (cut s t L k)
          (cstream A r.W (packedInterval (cut s t L k) (rows s t L k) D)++F.R (crop.reg 12))) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)))
        (Zs.reverse.map (fun z i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i)) Gs ∧
      ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (bulkTargetCoreReserve W V targetSpan b d r L k radius Fs.length Cprog+
          (8*(2*(4*d.B+4))+13*RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Fs.length)))
        depth (bulkPublishedProgram b) (Host.mk v S) n (Host.mk v' final) := by
  dsimp only
  intro hwide hwindow hwV hspanV hvol hVW hA hVpos wl hwl v S hready hheaders hspanRuler tail
    hqueue harchive hacc hdst hline hinput hblank Cprog depth hpush hbody
  let radius := localityDepth p target*PhaseCellBand.width p u
  let d := axis.ownedMasterInput target L k hnear hL ha hb
  let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
  let Zs := axis.ownedTargets target L k hnear hL ha hb hfit Fs
  have hbulk := bulk_target_exec_ofAxisBounds (body := body) b axis target L k hnear hL ha hb hfit
    W V targetOrigin targetSpan Fs hF hwide hwindow hwV hspanV hvol hVW hA hVpos wl hwl v S hready
    hheaders hspanRuler tail hqueue harchive hacc hdst hline hinput hblank
  change bulkTargetCoreSpec (body := body) b d r W V L k radius targetSpan Fs Zs v S (1/(2 : ℝ)^target) at hbulk
  obtain ⟨F,Ds,hDs,hqueueF,hframe,v₁,m₁,hu₁,hm₁,he₁,hgood,htrace₁⟩ := hbulk
  let q := packedHaloPrecision p l s t u (target+1) 2
    (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
    (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
  have ht : r.problem.t = t := rfl
  have hprec : r.problem.precision = q := rfl
  have hword : r.problem.wordWidth = 2*q+8 := by
    have hw : r.problem.wordWidth = 2*r.problem.precision+8 := by
      unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
      omega
    rw [hw,hprec]
  have hwidth : r.W = packedHaloCommonWidth p l s u (target+1) 2 := rfl
  simp only [ht,hprec,hword] at hgood
  have hnormal := owned_normalize_after_bulk (body := body) hA axis target L k hnear hL ha hb hfit Fs hF
    Ds.reverse (by rw [List.length_reverse]; exact hDs) wl hwl depth v₁ S F hready hframe
  have hnormal' := hnormal hgood
  obtain ⟨hlen,v₂,m₂,hu₂,hm₂,he₂,haccuracy,htrace₂⟩ := hnormal'
  let Gs := Ds.reverse.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
  have hGs : Gs.length = Fs.length := by simp only [Gs,List.length_map,List.length_reverse]; exact hDs
  let old := (Ds.reverse.map (fun D => cstream A (2*q+8) (packedInterval (cut s t L k) (rows s t L k) D))).flatten++F.R (crop.reg 12)
  let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) old}
  let output := (Gs.map (fun D => cstream A r.W (packedInterval (cut s t L k) (rows s t L k) D))).flatten++F.R (crop.reg 12)
  have hh : E.R normalize.header = [] := by
    have hp := RecoveryBanks.publicationReady_after_bulk recovery recovery_injective d r Fs.length radius (rows s t L k)
      wl S F hready hframe source (fun i => geometry_ne_recovery 108 i) old
    exact hp.header
  have hfinal : {E with R := Function.update (Function.update E.R normalize.header []) normalize.src output} =
      {F with R := Function.update (Function.update F.R source []) (crop.reg 12) output} := by
    have hu : Function.update E.R normalize.header [] = E.R := by
      rw [←hh]
      exact Function.update_eq_self ..
    rw [hu]
    change {E with R := Function.update E.R (crop.reg 12) output} = _
    congr 1
    simp only [E,Function.update_idem]
  simp only [ht,hword] at he₁
  simp only [←hwidth] at he₂ haccuracy htrace₂ hm₂
  change Exec body normalizeQueue.normalizeProgram (Host.mk v₁ E) m₂
    (Host.mk v₂ {E with R := Function.update (Function.update E.R normalize.header []) normalize.src output}) at he₂
  rw [hfinal] at he₂
  have ht₁ := htrace₁ Cprog hpush hbody depth
  simp only [ht,hword] at ht₁
  change ExecWithin body _ depth (bulkTargetCoreProgram b) (Host.mk v S) m₁ (Host.mk v₁ E) at ht₁
  change ExecWithin body _ depth normalizeQueue.normalizeProgram (Host.mk v₁ E) m₂
    (Host.mk v₂ {E with R := Function.update (Function.update E.R normalize.header []) normalize.src output}) at htrace₂
  have ht := mn_seq_within_add ht₁ htrace₂
  change ExecWithin body _ depth (bulkPublishedProgram b) (Host.mk v S) (m₁+m₂)
    (Host.mk v₂ {E with R := Function.update (Function.update E.R normalize.header []) normalize.src output}) at ht
  rw [hfinal] at ht
  refine ⟨F,Gs,hGs,hqueueF,hframe,v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,haccuracy,?_⟩
  · change m₂ ≤ RecoveryParameterQueue.prepareTimeCost d+RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Ds.reverse.length at hm₂
    rw [List.length_reverse,hDs] at hm₂
    change m₁+m₂ ≤ bulkTargetCoreTime W V targetSpan b d r L k radius Fs.length+
      RecoveryParameterQueue.prepareTimeCost d+RecoveryNormalizePlan.generatedIntervalTimeCost d r.W (rows s t L k) Fs.length
    exact (Nat.add_le_add hm₁ hm₂).trans_eq (Nat.add_assoc _ _ _).symm
  · rw [List.length_reverse,hDs] at ht
    exact ht

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
