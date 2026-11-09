module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbeGeometryHaloGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareGeometryHaloClassStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryHaloGatherControlsStock

/-! Empty and nonempty classes retain their actual branch workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def probeGeometryHaloGatherWorkspace (P q s t u band a b L : ℕ) : ℕ :=
  prepareGeometryHaloClassWorkspace q s t band a b L+
    (if 0 < (haloLengthGroup s t band a b L).length then
      completeGeometryHaloGatherWorkspace P q (2*q+8) s t u band a b L else 0)

theorem probeGeometryHaloGather_exec_within (P q s t u band a b L : ℕ)
    (hs : 0 < s) (hst : s < t)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117),104,106,115,116,88,89,90], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧
      n ≤ probeGeometryHaloGatherCost P q s t u band a b L ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          probeGeometryHaloGatherWorkspace P q s t u band a b L)
        depth probeGeometryHaloGather (mk v S) n
        (mk v' {S with R := probedGeometryHaloGatherR A P q s t u band a b L S.R})) := by
  let B := (haloLengthGroup s t band a b L).length
  let S₁ : Stacks 117 A := {S with R := preparedGeometryHaloClassR A q s t band a b L S.R}
  let Syes : Stacks 117 A := {S with R := (haloOriginAndGatherControlsR A
    (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R)}
  let S₂ : Stacks 117 A := {S with R := probedGeometryHaloGatherR A P q s t u band a b L S.R}
  have hbool : (S₁.R 116).head?.isSome = decide (0 < B) := by
    cases h : (haloLengthGroup s t band a b L).length <;> simp [S₁,preparedGeometryHaloClassR,haloClassControlsR,B,h]
  have prepare : RunsWithin body prepareGeometryHaloClassControls S S₁
      (prepareGeometryHaloClassControlsCost q s t band a b L)
      (prepareGeometryHaloClassWorkspace q s t band a b L) := by
    intro v₀
    exact prepareGeometryHaloClassControls_exec_within (body := body) q s t band a b L hs hst hband has hbs hL hLs hA
      v₀ S hq hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hblank (by
        intro k hk; apply hfresh k
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  have finish : (S₁.R 116).head?.isSome = true → RunsWithin body completeGeometryHaloGather S₁ Syes
      (completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L)
      (completeGeometryHaloGatherWorkspace P q (2*q+8) s t u band a b L) := by
    intro hb
    have hpos : 0 < B := by simpa only [hbool,decide_eq_true_eq] using hb
    exact completeGeometryHaloGather_prepared_runs_within (body := body) P q s t u band a b L
      hst hband hpos S hP hq htSrc huSrc hblank hfresh
  have empty : (S₁.R 116).head?.isSome = false → Runs body (clearWords [94,115]) S₁ S
      (2*((2*q+8)+haloGeometryWidth t (2*q+8))+5) := by
    intro hb
    have hzero : B = 0 := by have h := hb; rw [hbool] at h; simp only [decide_eq_false_iff_not] at h; omega
    apply Runs.of_exact
    intro v₀
    exact releaseEmptyGeometryHaloOrigins_exec (body := body) q s t band a b L hzero v₀ S
      (hfresh 94 (by simp)) (hfresh 115 (by simp)) (hfresh 116 (by simp))
  have emptyStock : (S₁.R 116).head?.isSome = false → RunsWithin body (clearWords [94,115]) S₁ S
      (2*((2*q+8)+haloGeometryWidth t (2*q+8))+5) 0 := by
    intro hb
    simpa only [Nat.zero_mul] using (empty hb).native_within (clearWords_native_zero _)
  have branch := RunsWithin.branch 116 finish emptyStock
  have branch' : RunsWithin body
      (.seq (.act (peekR 116)) (.cond (·.flag) completeGeometryHaloGather (clearWords [94,115]))) S₁ S₂
      ((if 0 < B then completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L
        else 2*((2*q+8)+haloGeometryWidth t (2*q+8))+5)+2)
      (if 0 < B then completeGeometryHaloGatherWorkspace P q (2*q+8) s t u band a b L else 0) := by
    by_cases hB : 0 < (haloLengthGroup s t band a b L).length
    all_goals simpa [hbool,Syes,S₂,probedGeometryHaloGatherR,B,hB] using branch
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := (prepare.seq branch') v
  have hflag : (S₂.R 116).head?.isSome = decide (0 < B) := by
    cases h : (haloLengthGroup s t band a b L).length <;> simp [S₂,probedGeometryHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,B,h,hfresh 116 (by simp)]
  have hpeek := Exec.act (body := body) (peekR 116) (mk v₂ S₂)
  rw [peekR_run,hflag] at hpeek
  refine ⟨{v₂ with flag := decide (0 < B)},n₂+1,hu₂,rfl,?_,?_⟩
  · dsimp only [probeGeometryHaloGatherCost]
    dsimp only [B] at hn₂ ⊢
    omega
  · intro depth
    have hnative : mnNativePushBound 0 (.act (peekR (116 : Fin 117)) : Pr P₀ 117 Q A U) := by
      simp [peekR,mnNativePushBound,mnActPush]
    have ht := mn_native_exec_within hpeek 0 hnative depth _ (Nat.le_refl _)
    exact (mn_seq_within_add (he₂ depth) ht).mono (by
      intro d z hz
      unfold probeGeometryHaloGatherWorkspace
      dsimp only [B] at hz
      omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
