module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBulkTargetCoreRecovery
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

theorem bulk_target_exec_ofAxisBounds (b : RawRecoveryProgramBounds Q A U)
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
    (_ : ∀ j ∈ [batch 0,batch 1,scratch 0,scratch 1,scratch 2,scratch 3], S.R j = []),
    bulkTargetCoreSpec (body := body) b d r W V L k radius targetSpan Fs Zs v S (1/(2 : ℝ)^target) := by
  dsimp only
  intro hwide hwindow hwV hspanV hvol hVW hA hVpos wl hwl v S hready hheaders hspanRuler tail
    hqueue harchive hacc hdst hline hinput hblank
  let radius := localityDepth p target*PhaseCellBand.width p u
  let d := axis.ownedMasterInput target L k hnear hL ha hb
  let r := axis.ownedJob target L k hnear hL ha hb hfit Fs hF
  let Zs := axis.ownedTargets target L k hnear hL ha hb hfit Fs
  obtain ⟨_,_,hcore,hspan,hfields,htarget,_⟩ := axis.ownedJob_profile target L k hnear hL ha hb hfit Fs hF
  have hn : 0 < r.problem.span := by
    rw [hspan]
    have hrows := rows_pos s t L k (lt_trans (NeZero.pos s) axis.hst) hnear hL
    omega
  have hex := bulk_target_owned_exec (body := body)
    b d r (axis.ownedJob_masterValues target L k hnear hL ha hb hfit Fs hF)
    W V L k radius targetOrigin targetSpan hcore hspan hn hwide hwindow hwV hspanV hvol hVW hA hVpos
    Fs hfields Zs (axis.ownedTargets_length target L k hnear hL ha hb hfit Fs)
    (axis.ownedJob_solutionOrder target L k hnear hL ha hb hfit Fs hF)
    wl hwl v S hready hheaders hspanRuler tail hqueue harchive hacc hdst hline hinput hblank
  change r.target = target+1 at htarget
  simpa only [htarget,component_error_bit] using hex

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
