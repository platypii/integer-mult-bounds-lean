module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareGeometryHaloClassControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteGeometryHaloGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloGatherControls
public import IntegerMultBounds.MathlibTM2.Host.RunContract

/-! The generated geometry controller publishes the existing numerical batch interface. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateGeometryHaloGatherControls : Pr P₀ 117 Q A U :=
  .seq prepareGeometryHaloClassControls completeGeometryHaloGather

def generateGeometryHaloGatherControlsCost (P q s t u band a b L : ℕ) : ℕ :=
  prepareGeometryHaloClassControlsCost q s t band a b L+
    completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L

theorem completed_preparedGeometryHaloClassR (P q s t u band a b L : ℕ)
    (R : Fin 117 → List (Fin (A+4))) (h94 : R 94 = []) (h115 : R 115 = []) :
    Function.update
      (completedHaloGatherR A s t band a b L (2*q+8) (preparedGeometryHaloClassR A q s t band a b L R))
      109 (haloOriginPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L++R 109) =
      haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) R := by
  funext k
  by_cases hk94 : k = 94
  · subst k; simp [completedHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,h94]
  by_cases hk115 : k = 115
  · subst k; simp [completedHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,h115]
  by_cases hk109 : k = 109
  · subst k; simp [completedHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR]
  simp [completedHaloGatherR,preparedGeometryHaloClassR,haloOriginAndGatherControlsR,haloClassControlsR,
    Function.update_apply,hk94,hk115,hk109]

theorem generateGeometryHaloGatherControls_exec (P q s t u band a b L : ℕ)
    (hs : 0 < s) (hst : s < t) (hbandP : band ≤ P)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117),104,106,115,116,88,89,90], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateGeometryHaloGatherControlsCost P q s t u band a b L ∧
      Exec body generateGeometryHaloGatherControls (mk v S) n
        (mk v' {S with R := (haloOriginAndGatherControlsR A
          (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R)}) := by
  let S₁ : Stacks 117 A := {S with R := preparedGeometryHaloClassR A q s t band a b L S.R}
  let S₂ : Stacks 117 A := {S with R := (haloOriginAndGatherControlsR A
    (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R)}
  have prepare : Runs body prepareGeometryHaloClassControls S S₁
      (prepareGeometryHaloClassControlsCost q s t band a b L) := by
    intro v₀
    exact prepareGeometryHaloClassControls_exec (body := body) q s t band a b L hs hst hband has hbs hL hLs hA
      v₀ S hq hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hblank (by
        intro k hk; apply hfresh k
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  have finish : Runs body completeGeometryHaloGather S₁ S₂
      (completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L) := by
    intro v₀
    have h94 := hfresh 94 (by simp)
    have h115 := hfresh 115 (by simp)
    have heffect : {S₁ with R := (Function.update
        (completedHaloGatherR A s t band a b L (2*q+8) S₁.R) 109
        (haloOriginPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L++S.R 109))} = S₂ := by
      simpa only [S₁,S₂] using congrArg (fun R => ({S with R := R} : Stacks 117 A))
        (completed_preparedGeometryHaloClassR P q s t u band a b L S.R h94 h115)
    rw [← heffect]
    apply completeGeometryHaloGather_exec (body := body) P q (2*q+8) s t u band a b L hst.le hbandP hgroup v₀ S₁ (S.R 109)
    all_goals simp only [S₁,preparedGeometryHaloClassR,haloClassControlsR,Function.update_apply]
    all_goals norm_num
    all_goals first | assumption | rfl | skip
    · intro k hk
      have hne (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simpa [Fin.ext_iff,hne 94 (by decide),hne 115 (by decide),hne 109 (by decide),hne 116 (by decide)] using hblank k hk
    · repeat' constructor
      all_goals exact hfresh _ (by simp)

  exact (prepare.seq finish) v

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
