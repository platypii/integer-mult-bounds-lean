module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunsFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmitHaloRunMask

/-! The complete interval mask pipeline, with no supplied run packets or flags. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def haloRunMaskFromHeaders (off on : Fin (A+4)) : Pr P 117 Q A U :=
  .seq (haloRunsFromHeaders false 109) (.seq (haloRunsFromHeaders true 108)
    (.seq (emitRunPackets off on) (uclear 108)))

def haloRunMaskFromHeadersCost (W s t band a b : ℕ) : ℕ :=
  haloRunsFromHeadersCost false W s t band a b+haloRunsFromHeadersCost true W s t band a b+
    (10*s+(19*W+22)*(2*(t-s+1)+1)+6)+(2*(2*(haloRunIntervals s t band a b).length+1)+2)

theorem haloRunMaskFromHeaders_exec {W s t band a b : ℕ} [NeZero s]
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hA : 4 ≤ A) (off on : Fin (A+4))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hWsrc : (S.R 115).length = W) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ haloRunMaskFromHeadersCost W s t band a b ∧
      Exec body (haloRunMaskFromHeaders off on) (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          ((List.range s).map (fun k => if haloInteriorAt s t band a b k then on else off)++S.R 109))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := haloRunsFromHeaders_exec (body := body) false 109 (by decide)
    hst has hbs hwide hA v S hs ht hband ha hb hWsrc h106 hblank
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 109 (haloRunMetadata false A W s t band a b++S.R 109)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := haloRunsFromHeaders_exec (body := body) true 108 (by decide)
    hst has hbs hwide hA v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using ht)
    (by simpa [S₁] using hband) (by simpa [S₁] using ha) (by simpa [S₁] using hb)
    (by simpa [S₁] using hWsrc) (by simpa [S₁] using h106) (by
      intro r hr
      have hr109 : r ≠ (109 : Fin 117) := by intro he; subst r; norm_num at hr
      simpa [S₁,hr109] using hblank r hr)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 108 (haloRunMetadata true A W s t band a b)}
  have he₂' : Exec body (haloRunsFromHeaders true 108) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,h108] using he₂
  let mask := (List.range s).map (fun k => if haloInteriorAt s t band a b k then on else off)
  have hsW : s < 2^W := by nlinarith only [hwide,hst]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := emitHaloRunMask_exec (body := body) hst W band a b hbs hsW off on
    v₂ S₂ (S.R 109) (by simpa [S₂,S₁] using hWsrc) (by simp [S₂,haloRunMetadata])
    (by simp [S₂,S₁,haloRunMetadata]) (by
      intro k hk
      have hk108 : k ≠ (108 : Fin 117) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk109 : k ≠ (109 : Fin 117) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk31 : k.val < 31 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [S₂,S₁,hk108,hk109,hblank k hk31])
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 109 (mask++S.R 109)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 108 v₃ S₃
  have hlen : (S₃.R 108).length = 2*(haloRunIntervals s t band a b).length+1 := by
    simp [S₃,S₂,haloRunMetadata,IntervalRunMask.length_runs]
  refine ⟨v₄,n₁+(n₂+(n₃+(2*(2*(haloRunIntervals s t band a b).length+1)+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · dsimp only [haloRunMaskFromHeadersCost]
    omega
  · rw [hlen]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₃,S₂,S₁,Function.update_apply]
    split_ifs <;> simp_all [mask]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
