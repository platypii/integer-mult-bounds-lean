module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGroupCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedHaloScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishNaturalClass

/-! Finish one solved nonempty class: retire its gathered RHS, publish the
solved rows and release the per-class headers and publication controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

theorem retireHaloGroupCost_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b L w : ℕ)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length) (hw : 1 ≤ w) :
    let B := (haloLengthGroup s t band a b L).length
    12*B*L*w+6*L*w+9*L+9*B+19 ≤ 36*s*w+19 := by
  dsimp only
  let B := (haloLengthGroup s t band a b L).length
  have hvol : B*L ≤ s := haloGroup_volume_le hst band a b L
  have hL : 0 < L := ((mem_haloLengthGroup s t band a b L _).mp
    (haloGroupPhase_mem s t band a b L ⟨0,hgroup⟩)).2.1
  have hBs : B ≤ s := by nlinarith only [hvol,hL]
  have hLs : L ≤ s := by have hB : 0 < B := hgroup; nlinarith only [hvol,hB]
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  have hwork := Nat.mul_le_mul_right w hvol
  have hrow := Nat.mul_le_mul_right w hLs
  change 12*B*L*w+6*L*w+9*L+9*B+19 ≤ _
  nlinarith only [hBs,hLs,hsw,hwork,hrow]


theorem finishHaloClass_exec {s t : ℕ} [NeZero s] (hst : s < t) (band a b L w : ℕ) (hwpos : 1 ≤ w)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (rhs ambient E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (haloLengthGroup s t band a b L).length*(L*w))
    (hrhs : rhs.length = (haloLengthGroup s t band a b L).length*L*w)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hL : (S.R 128).length = L) (hw : (S.R 130).length = w)
    (hB : (S.R 129).length = (haloLengthGroup s t band a b L).length)
    (hr : S.R 110 = rhs++ambient) (hc : S.R 140 = gatherControls A (haloScatterGaps s t band a b L w))
    (hdst : S.R 132 = E++outputTail) (hsrc : S.R 93 = ys++sourceTail)
    (hz : ∀ k ∈ [(88 : Fin 144),89,90,92,94,131,134,135,136,137], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 94*s*w+39 ∧
      Exec body finishNaturalClass (mk v S) n
        (mk v' { S with R := (finishedClassR S.R ambient sourceTail
          (scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail)) }) := by
  let B := (haloLengthGroup s t band a b L).length
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retireGroupRHS_exec (body := body) B L w rhs ambient v S hL hB hw hr hrhs (by
    intro k hk
    apply hz k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 144 A := { S with R := Function.update S.R 110 ambient }
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := protectedHaloScatter_exec (body := body) hst band a b L w hwpos hgroup
    E ys sourceTail outputTail hE hys v₁ S₁
    (by simpa [S₁] using hL) (by simpa [S₁] using hw) (by simpa [S₁] using hc)
    (by simpa [S₁] using hdst) (by simpa [S₁] using hsrc) (by
      intro k hk
      have hk110 : k ≠ (110 : Fin 144) := by intro he; subst k; norm_num at hk
      simp only [S₁,Function.update_of_ne hk110]
      apply hz k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let published := scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail
  let S₂ : Stacks 144 A := { S₁ with R := (Function.update (Function.update (Function.update S₁.R 93 sourceTail)
    132 published) 140 []) }
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(128 : Fin 144),129] (by decide) v₂ S₂
  have hsum : (([(128 : Fin 144),129]).map (fun k => (S₂.R k).length)).sum = L+B := by
    simp [S₂,S₁,hL,hB,B]
  refine ⟨v₃,n₁+(n₂+(2*(L+B)+5)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · have hret := retireHaloGroupCost_le hst band a b L w hgroup hwpos
    have hBvol : B*L ≤ s := haloGroup_volume_le hst band a b L
    have hLpos : 0 < L := ((mem_haloLengthGroup s t band a b L _).mp
      (haloGroupPhase_mem s t band a b L ⟨0,hgroup⟩)).2.1
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
