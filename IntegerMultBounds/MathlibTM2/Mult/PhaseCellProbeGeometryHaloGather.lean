module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryHaloGatherControls

/-! Select empty/nonempty geometry classes after one origin scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def probeGeometryHaloGather : Pr P₀ 117 Q A U :=
  .seq (.seq prepareGeometryHaloClassControls
    (.seq (.act (peekR 116)) (.cond (·.flag) completeGeometryHaloGather (clearWords [94,115]))))
      (.act (peekR 116))

def probedGeometryHaloGatherR (A P q s t u band a b L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  if 0 < (haloLengthGroup s t band a b L).length then
    haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) R else R

def probeGeometryHaloGatherCost (P q s t u band a b L : ℕ) : ℕ :=
  prepareGeometryHaloClassControlsCost q s t band a b L+
    (if 0 < (haloLengthGroup s t band a b L).length then
      completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L
    else 2*((2*q+8)+haloGeometryWidth t (2*q+8))+5)+3

theorem releaseEmptyGeometryHaloOrigins_exec (q s t band a b L : ℕ)
    (hB : (haloLengthGroup s t band a b L).length = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (h94 : S.R 94 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = []) :
    ∃ v', v'.user = v.user ∧ Exec body (clearWords [94,115])
      (mk v {S with R := preparedGeometryHaloClassR A q s t band a b L S.R})
      (2*((2*q+8)+haloGeometryWidth t (2*q+8))+5) (mk v' S) := by
  let S₁ : Stacks 117 A := {S with R := preparedGeometryHaloClassR A q s t band a b L S.R}
  have hpkt : haloOriginPackets A (haloGeometryWidth t (2*q+8)) s t band a b L = [] :=
    List.eq_nil_of_length_eq_zero (by simp [hB])
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v S₁
  refine ⟨v',hu,he.cast ?_ ?_⟩
  · simp [S₁,preparedGeometryHaloClassR,haloClassControlsR]
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk94 : k = 94
    · subst k; simp [S₁,h94]
    by_cases hk115 : k = 115
    · subst k; simp [S₁,h115]
    by_cases hk116 : k = 116
    · subst k; simp [S₁,preparedGeometryHaloClassR,haloClassControlsR,hB,h116]
    by_cases hk109 : k = 109
    · subst k; simp [S₁,preparedGeometryHaloClassR,haloClassControlsR,hpkt]
    simp [S₁,preparedGeometryHaloClassR,haloClassControlsR,hk94,hk115,hk116,hk109,Function.update_apply]

theorem probeGeometryHaloGather_exec (P q s t u band a b L : ℕ)
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
      Exec body probeGeometryHaloGather (mk v S) n
        (mk v' {S with R := probedGeometryHaloGatherR A P q s t u band a b L S.R}) := by
  let B := (haloLengthGroup s t band a b L).length
  let S₁ : Stacks 117 A := {S with R := preparedGeometryHaloClassR A q s t band a b L S.R}
  let Syes : Stacks 117 A := {S with R := (haloOriginAndGatherControlsR A
    (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R)}
  let S₂ : Stacks 117 A := {S with R := probedGeometryHaloGatherR A P q s t u band a b L S.R}
  have hbool : (S₁.R 116).head?.isSome = decide (0 < B) := by
    cases h : (haloLengthGroup s t band a b L).length <;> simp [S₁,preparedGeometryHaloClassR,haloClassControlsR,B,h]
  have prepare : Runs body prepareGeometryHaloClassControls S S₁
      (prepareGeometryHaloClassControlsCost q s t band a b L) := by
    intro v₀
    exact prepareGeometryHaloClassControls_exec (body := body) q s t band a b L hs hst hband has hbs hL hLs hA
      v₀ S hq hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hblank (by
        intro k hk; apply hfresh k
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  have finish : (S₁.R 116).head?.isSome = true → Runs body completeGeometryHaloGather S₁ Syes
      (completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L) := by
    intro hb
    have hpos : 0 < B := by simpa only [hbool,decide_eq_true_eq] using hb
    exact completeGeometryHaloGather_prepared_runs (body := body) P q s t u band a b L
      hst hband hpos S hP hq htSrc huSrc hblank hfresh
  have empty : (S₁.R 116).head?.isSome = false → Runs body (clearWords [94,115]) S₁ S
      (2*((2*q+8)+haloGeometryWidth t (2*q+8))+5) := by
    intro hb
    have hzero : B = 0 := by have h := hb; rw [hbool] at h; simp only [decide_eq_false_iff_not] at h; omega
    apply Runs.of_exact
    intro v₀
    exact releaseEmptyGeometryHaloOrigins_exec (body := body) q s t band a b L hzero v₀ S
      (hfresh 94 (by simp)) (hfresh 115 (by simp)) (hfresh 116 (by simp))
  have branch := Runs.branch 116 finish empty
  have branch' : Runs body
      (.seq (.act (peekR 116)) (.cond (·.flag) completeGeometryHaloGather (clearWords [94,115]))) S₁ S₂
      ((if 0 < B then completeGeometryHaloGatherCost P q (2*q+8) s t u band a b L
        else 2*((2*q+8)+haloGeometryWidth t (2*q+8))+5)+2) := by
    by_cases hB : 0 < (haloLengthGroup s t band a b L).length
    all_goals simpa [hbool,Syes,S₂,probedGeometryHaloGatherR,B,hB] using branch
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := (prepare.seq branch') v
  have hflag : (S₂.R 116).head?.isSome = decide (0 < B) := by
    cases h : (haloLengthGroup s t band a b L).length <;> simp [S₂,probedGeometryHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,B,h,hfresh 116 (by simp)]
  have hpeek := Exec.act (body := body) (peekR 116) (mk v₂ S₂)
  rw [peekR_run,hflag] at hpeek
  refine ⟨{v₂ with flag := decide (0 < B)},n₂+1,hu₂,rfl,?_,Exec.seq he₂ hpeek⟩
  dsimp only [probeGeometryHaloGatherCost]
  dsimp only [B] at hn₂ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
