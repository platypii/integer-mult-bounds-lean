module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Construct publication controls on protected register 140 from the existing
private-bank gather controls. The encoded window length is computed from the
retained row and word widths; all temporary counters are released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

theorem protectedHaloPublicationControls_exec {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b L w : ℕ) (hwpos : 1 ≤ w) (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (borrowed : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hL : (S.R 128).length = L) (hw : (S.R 130).length = w)
    (hc : S.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hs : S.R 91 = haloGatherControls A s t band a b L w++borrowed)
    (hz : ∀ k ∈ [(88 : Fin 144),89,90,92,94,104,106,131,134,135], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 48*s*w+27 ∧
      Exec body protectedPublicationControls (mk v S) n
        (mk v' { S with R := (Function.update S.R 140
          (gatherControls A (haloScatterGaps s t band a b L w)++S.R 140)) }) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 128) (b := 130) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S
    (hz 134 (by simp)) (hz 135 (by simp))
  let S₁ : Stacks 144 A := { S with R := Function.update S.R 131 (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct 128 130 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hL,hw,hz 131 (by simp)] using he₁
  have hn₁' : n₁ ≤ L*(4*w+9)+4 := by simpa [hL,hw] using hn₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := haloPublicationControls_exec (body := body)
    (count := 116) (savedCount := 88) (control := 91) (savedControl := 89) (counter := 90)
    (window := 131) (zero := 92) (acc := 94) (dst := 140) (trash := 104) (tmp := 106)
    (by decide) hst band a b L w hwpos hgroup borrowed v₁ S₁
    (by simpa [S₁] using hc) (by simpa [S₁] using hs) (by simp [S₁]) (by
      intro k hk
      have hk131 : k ≠ (131 : Fin 144) := by
        intro he; subst k; norm_num at hk
      simp only [S₁,Function.update_of_ne hk131]
      apply hz k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₂ : Stacks 144 A := { S₁ with R := (Function.update S₁.R 140
    (gatherControls A (haloScatterGaps s t band a b L w)++S₁.R 140)) }
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 131 v₂ S₂
  have hlen : (S₂.R 131).length = L*w := by simp [S₂,S₁]
  refine ⟨v₃,n₁+(n₂+(2*(L*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_⟩
  · have hLs : L ≤ s := by
      have hh := haloGroup_volume_le hst band a b L
      nlinarith only [hh,hgroup]
    have hrow := Nat.mul_le_mul_right w hLs
    have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hwpos
    nlinarith only [hn₁',hn₂,hLs,hrow,hsw]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = 131
    · subst k; simp [hz 131 (by simp)]
    simp [S₂,S₁,Function.update_apply,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
