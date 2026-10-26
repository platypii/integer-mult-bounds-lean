module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedPrepareHaloReplicaSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloKeyRuntimeFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseHaloGroupHeaders

/-! Initialize the counted iterator from ordinary retained master headers.
Private setup is released before the loop starts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem copiedHaloGroupR_clear109 {A : ℕ} (P N q l s t u band a b : ℕ)
    (R : Regs 144 A) (h109 : R 109 = []) :
    Function.update (copiedHaloGroupR P N q l s t u band a b 0 R) 109 [] =
      copiedHaloGroupR P N q 0 s t u band a b 0 R := by
  funext k
  by_cases hk : k = 109
  · subst k
    simp [copiedHaloGroupR,copiedGroupR,unaryCopiesR,groupHeaderCopies,groupHeaderValue,h109]
  · simp [copiedHaloGroupR,copiedGroupR,unaryCopiesR,groupHeaderCopies,groupHeaderValue,
      Function.update_apply,hk]

def initializeHaloReplicaSchedule : Pr P₀ 144 Q A U :=
  .seq installHaloGroupHeaders (.seq protectedPrepareHaloReplicaSchedule
    (.seq installKeyRuntime releaseHaloGroupHeaders))

def initializeHaloReplicaScheduleCost (P N q l s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let K := (haloCellPhases s t band a b).length
  installHaloGroupHeadersCost P N q l s t u band a b 0 + prepareHaloReplicaScheduleCost P q l s t u band a b +
    (6*(V+w)+4*(K*(2*V))+2*K+19) + (2*(P+N+q+s+t+u+band+a+b)+26)

theorem initializeHaloReplicaSchedule_exec (P N q l s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmasters : ∀ r ∈ groupHeaderCopies,
      (S.R r.1).length = groupHeaderValue P N q l s t u band 0 r.1)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hfresh : ∀ k ∈ [(125 : Fin 144),127,130,133,138], S.R k = []) :
    let w := 2*q+8
    let V := weightWorkspaceWidth P q w t u
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeHaloReplicaScheduleCost P N q l s t u band a b ∧
      Exec (embTab groupReg body) initializeHaloReplicaSchedule (mk v S) n
        (mk v' { S with R := (initializedKeyRuntimeR S.R V w
          (haloCellPhases s t band a b).length (haloDescriptorPackets A V s t band a b)) }) := by
  dsimp only
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let K := (haloCellPhases s t band a b).length
  let keys := haloDescriptorPackets A V s t band a b
  obtain ⟨v₁,hu₁,he₁⟩ := installHaloGroupHeaders_exec (body := embTab groupReg body)
    P N q l s t u band a b 0 v S hmasters haMaster hbMaster
      (hblank 111 (by decide) (by decide) (by decide))
      (hblank 113 (by decide) (by decide) (by decide)) (hfresh 133 (by simp))
  let S₁ : Stacks 144 A := { S with R := copiedHaloGroupR P N q l s t u band a b 0 S.R }
  have hbank := copiedHaloGroup_project P N q l s t u band a b 0 S (S.R 110) [] hleft hblank (by simp)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := protectedPrepareHaloReplicaSchedule_exec (body := body)
    P N q l s t u band a b hP hs hst hu hband has hbs hA v₁ S₁ (S.R 110) (S.R 93) hbank
  let S₂ : Stacks 144 A := { S₁ with R := generatedKeyRuntimeR (Function.update S₁.R 109 []) V w K keys }
  have hprivate : ∀ k ∈ [(86 : Fin 144),87,94,115], S₁.R k = [] := by
    intro k hk
    have hlo : k.val < 117 ∧ k ≠ 93 ∧ k ≠ 110 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    have hz := hblank k hlo.1 hlo.2.1 hlo.2.2
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    all_goals simpa [S₁,copiedHaloGroupR,copiedGroupR,groupHeaderCopies,unaryCopiesR] using hz
  obtain ⟨v₃,hu₃,he₃⟩ := installKeyRuntime_exec (body := embTab groupReg body) V w K keys v₂ S₂
    (by simp [S₂,generatedKeyRuntimeR]) (by simp [S₂,generatedKeyRuntimeR])
    (by simp [S₂,generatedKeyRuntimeR]) (by simp [S₂,generatedKeyRuntimeR]) (by
      intro k hk
      have hz := hfresh k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals simpa [S₂,generatedKeyRuntimeR,S₁,copiedHaloGroupR_off] using hz)
  let S₃ : Stacks 144 A := { S with R := initializedKeyRuntimeR S.R V w K keys }
  have hframe : installedKeyRuntimeR S₂.R V w K keys = copiedHaloGroupR P N q 0 s t u band a b 0 S₃.R := by
    dsimp only [S₂]
    rw [installed_generatedKeyRuntimeR (Function.update S₁.R 109 []) V w K keys (by
      intro k hk
      have h109 : k ≠ 109 := by intro he; subst k; norm_num at hk
      simpa [h109] using hprivate k hk)]
    rw [show Function.update S₁.R 109 [] = copiedHaloGroupR P N q 0 s t u band a b 0 S.R from
      copiedHaloGroupR_clear109 P N q l s t u band a b S.R
        (hblank 109 (by decide) (by decide) (by decide))]
    exact initializedKeyRuntimeR_copiedHaloGroupR S.R P N q 0 s t u band a b 0 V w K keys
  have he₃' : Exec (embTab groupReg body) installKeyRuntime (mk v₂ S₂)
      (6*(V+w)+4*keys.length+2*K+19)
      (mk v₃ { S₃ with R := copiedHaloGroupR P N q 0 s t u band a b 0 S₃.R }) := by
    simpa only [hframe,S₂,S₁,S₃] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := releaseHaloGroupHeaders_exec (body := embTab groupReg body)
    P N q 0 s t u band a b 0 v₃ S₃ (by
      intro r hr
      have hrlo : r.2.val < 117 ∧ r.2 ≠ 93 ∧ r.2 ≠ 110 := by
        simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (initializedKeyRuntimeR_private S.R V w K keys r.2 hrlo.1).trans
        (hblank r.2 hrlo.1 hrlo.2.1 hrlo.2.2))
    ((initializedKeyRuntimeR_private S.R V w K keys 111 (by decide)).trans
      (hblank 111 (by decide) (by decide) (by decide)))
    ((initializedKeyRuntimeR_private S.R V w K keys 113 (by decide)).trans
      (hblank 113 (by decide) (by decide) (by decide)))
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))⟩
  simp only [initializeHaloReplicaScheduleCost]
  have hlen : keys.length = K*(2*V) := haloDescriptorPackets_length A V s t band a b
  dsimp only [w,V,K] at *
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
