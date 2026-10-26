module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGroupCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedScatter

/-! Finish one solved nonempty class: retire its gathered RHS, publish the
solved rows and release the per-class headers and publication controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def finishNaturalClass : Pr P 144 Q A U :=
  .seq retireGroupRHS (.seq protectedScatter (clearWords [128,129]))

def finishedClassR (R : Regs 144 A) (ambient sourceTail published : List (Fin (A+4))) : Regs 144 A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update R 110 ambient) 93 sourceTail) 132 published) 140 []) 128 []) 129 []

theorem finishNaturalClass_exec {s t : ℕ} [NeZero s] (hst : s < t) (band L w : ℕ) (hwpos : 1 ≤ w)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (rhs ambient E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (naturalLengthGroup s t band L).length*(L*w))
    (hrhs : rhs.length = (naturalLengthGroup s t band L).length*L*w)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hL : (S.R 128).length = L) (hw : (S.R 130).length = w)
    (hB : (S.R 129).length = (naturalLengthGroup s t band L).length)
    (hr : S.R 110 = rhs++ambient) (hc : S.R 140 = gatherControls A (naturalScatterGaps s t band L w))
    (hdst : S.R 132 = E++outputTail) (hsrc : S.R 93 = ys++sourceTail)
    (hz : ∀ k ∈ [(88 : Fin 144),89,90,92,94,131,134,135,136,137], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 94*s*w+39 ∧
      Exec body finishNaturalClass (mk v S) n
        (mk v' { S with R := (finishedClassR S.R ambient sourceTail
          (scatterRows (L*w) E (ys++sourceTail) (naturalScatterGaps s t band L w)++outputTail)) }) := by
  let B := (naturalLengthGroup s t band L).length
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retireGroupRHS_exec (body := body) B L w rhs ambient v S hL hB hw hr hrhs (by
    intro k hk
    apply hz k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 144 A := { S with R := Function.update S.R 110 ambient }
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := protectedScatter_exec (body := body) hst band L w hwpos hgroup
    E ys sourceTail outputTail hE hys v₁ S₁
    (by simpa [S₁] using hL) (by simpa [S₁] using hw) (by simpa [S₁] using hc)
    (by simpa [S₁] using hdst) (by simpa [S₁] using hsrc) (by
      intro k hk
      have hk110 : k ≠ (110 : Fin 144) := by intro he; subst k; norm_num at hk
      simp only [S₁,Function.update_of_ne hk110]
      apply hz k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let published := scatterRows (L*w) E (ys++sourceTail) (naturalScatterGaps s t band L w)++outputTail
  let S₂ : Stacks 144 A := { S₁ with R := (Function.update (Function.update (Function.update S₁.R 93 sourceTail)
    132 published) 140 []) }
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(128 : Fin 144),129] (by decide) v₂ S₂
  have hsum : (([(128 : Fin 144),129]).map (fun k => (S₂.R k).length)).sum = L+B := by
    simp [S₂,S₁,hL,hB,B]
  refine ⟨v₃,n₁+(n₂+(2*(L+B)+5)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · have hret := retireNaturalGroupCost_le hst band L w hgroup hwpos
    have hBvol : B*L ≤ s := naturalGroup_volume_le hst band L
    have hLpos : 0 < L := ((mem_naturalLengthGroup s t band L _).mp
      (naturalGroupPhase_mem s t band L ⟨0,hgroup⟩)).2.1
    have hBs : B ≤ s := by nlinarith only [hBvol,hLpos]
    have hLs : L ≤ s := by nlinarith only [hBvol,hgroup]
    have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hwpos
    dsimp only [B] at *
    nlinarith only [hn₁,hret,hn₂,hLs,hBs,hsw,hsum]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk128 : k = 128 <;> by_cases hk129 : k = 129 <;>
      simp [S₂,S₁,finishedClassR,Function.update_apply,published,hk128,hk129]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
