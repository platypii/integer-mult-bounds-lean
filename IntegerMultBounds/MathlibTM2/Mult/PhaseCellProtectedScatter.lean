module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalScatter
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Publish one solved class from the protected caller. The retained row and
word widths construct the window counter; owned publication controls and all
scratch are released for the next class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def protectedScatter : Pr P 144 Q A U :=
  .seq (unaryProduct 128 130 131 134 135)
    (.seq (scatterBatch 140 88 89 131 93 132 90 92 94) (clearWords [131,140]))

theorem protectedScatter_exec {s t : ℕ} [NeZero s] (hst : s < t) (band L w : ℕ) (hwpos : 1 ≤ w)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (naturalLengthGroup s t band L).length*(L*w))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hL : (S.R 128).length = L) (hw : (S.R 130).length = w)
    (hc : S.R 140 = gatherControls A (naturalScatterGaps s t band L w))
    (hdst : S.R 132 = E++outputTail) (hsrc : S.R 93 = ys++sourceTail)
    (hz : ∀ k ∈ [(88 : Fin 144),89,90,92,94,131,134,135], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 54*s*w+15 ∧
      Exec body protectedScatter (mk v S) n
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 93 sourceTail)
          132 (scatterRows (L*w) E (ys++sourceTail) (naturalScatterGaps s t band L w)++outputTail)) 140 []) }) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 128) (b := 130) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S
    (hz 134 (by simp)) (hz 135 (by simp))
  let S₁ : Stacks 144 A := { S with R := Function.update S.R 131 (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct 128 130 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hL,hw,hz 131 (by simp)] using he₁
  have hn₁' : n₁ ≤ L*(4*w+9)+4 := by simpa [hL,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := naturalScatter_exec (body := body)
    (control := 140) (savedControl := 88) (gap := 89) (window := 131) (src := 93)
    (dst := 132) (acc := 90) (trash := 92) (tmp := 94) (by decide)
    s t band L w E ys sourceTail outputTail hE hys v₁ S₁
    (by simpa [S₁] using hc) (by simpa [S₁] using hdst) (by simpa [S₁] using hsrc)
    (by simp [S₁]) (by
      intro k hk
      have hk131 : k ≠ (131 : Fin 144) := by intro he; subst k; norm_num at hk
      simp only [S₁,Function.update_of_ne hk131]
      apply hz k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₂ : Stacks 144 A := { S₁ with R := (Function.update (Function.update S₁.R 93 sourceTail)
    132 (scatterRows (L*w) E (ys++sourceTail) (naturalScatterGaps s t band L w)++outputTail)) }
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(131 : Fin 144),140] (by decide) v₂ S₂
  have hsum : (([(131 : Fin 144),140]).map (fun k => (S₂.R k).length)).sum =
      L*w+(naturalScatterGaps s t band L w).sum+(naturalLengthGroup s t band L).length := by
    simp [S₂,S₁,hc]
    omega
  refine ⟨v₃,n₁+(naturalScatterCost s t band L w+(2*(_)+5)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hsum]
    have hn₂ := naturalScatterCost_le hst band L w hwpos
    have hvol := naturalScatterGaps_volume s t band L w
    simp only [scatterVolume,naturalScatterGaps_length] at hvol
    have hgap : (naturalScatterGaps s t band L w).sum ≤ s*w := by omega
    have hLpos : 0 < L := ((mem_naturalLengthGroup s t band L _).mp
      (naturalGroupPhase_mem s t band L ⟨0,hgroup⟩)).2.1
    have hBvol := naturalGroup_volume_le hst band L
    have hBs : (naturalLengthGroup s t band L).length ≤ s := by nlinarith only [hBvol,hLpos]
    have hLs : L ≤ s := by nlinarith only [hBvol,hgroup]
    have hrow := Nat.mul_le_mul_right w hLs
    have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hwpos
    nlinarith only [hn₁',hn₂,hgap,hBs,hLs,hrow,hsw]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk131 : k = 131
    · subst k; simp [hz 131 (by simp)]
    by_cases hk140 : k = 140
    · subst k; simp
    simp [S₂,S₁,Function.update_apply,hk131,hk140]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
