module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryHaloGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteGeometryHaloGatherStock

/-! Adapt the complete gather trace to its prepared origin bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem completeGeometryHaloGather_prepared_runs_within (P q s t u band a b L : ℕ)
    (hst : s < t) (hband : band ≤ s) (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (S : Stacks 117 A) (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (htSrc : (S.R 98).length = t) (huSrc : (S.R 99).length = u)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117),104,106,115,116,88,89,90], S.R k = []) :
    RunsWithin body completeGeometryHaloGather
      {S with R := preparedGeometryHaloClassR A q s t band a b L S.R}
      {S with R := (haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u)
        s t band a b L (2*q+8) S.R)} (completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L)
      (completeGeometryHaloGatherWorkspace P q (2*q+8) s t u band a b L) := by
  let S₁ : Stacks 117 A := {S with R := preparedGeometryHaloClassR A q s t band a b L S.R}
  let S₂ : Stacks 117 A := {S with R := (haloOriginAndGatherControlsR A
    (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R)}
  intro v₀
  change ∃ v' n, v'.user = v₀.user ∧ n ≤ completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L ∧
    (∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₁)+depth+
        completeGeometryHaloGatherWorkspace P q (2*q+8) s t u band a b L)
      depth completeGeometryHaloGather (mk v₀ S₁) n (mk v' S₂))
  have h94 := hfresh 94 (by simp)
  have h115 := hfresh 115 (by simp)
  have heffect : {S₁ with R := (Function.update
      (completedHaloGatherR A s t band a b L (2*q+8) S₁.R) 109
      (haloOriginPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L++S.R 109))} = S₂ := by
    simpa only [S₁,S₂] using congrArg (fun R => ({S with R := R} : Stacks 117 A))
      (completed_preparedGeometryHaloClassR P q s t u band a b L S.R h94 h115)
  rw [← heffect]
  apply completeGeometryHaloGather_exec_within (body := body) P q (2*q+8) s t u band a b L hst.le (hband.trans hst.le) hgroup v₀ S₁ (S.R 109)
  all_goals simp only [S₁,preparedGeometryHaloClassR,haloClassControlsR,Function.update_apply]
  all_goals norm_num
  all_goals first | assumption | rfl | skip
  · intro k hk
    have hne (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
    simpa [Fin.ext_iff,hne 94 (by decide),hne 115 (by decide),hne 109 (by decide),hne 116 (by decide)] using hblank k hk
  · repeat' constructor
    all_goals exact hfresh _ (by simp)


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
