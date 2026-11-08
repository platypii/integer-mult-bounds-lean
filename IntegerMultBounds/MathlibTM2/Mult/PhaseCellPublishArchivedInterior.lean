module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreRecoveryOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedPublication

/-! Restore and merge one archived interior while preserving the shared arithmetic bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem componentReady_archive_output {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S : Stacks 148 A}
    (h : LengthKeyReady P N q l s t u band V w input (embStk componentReg S))
    (archive output : List (Fin (A+4))) :
    LengthKeyReady P N q l s t u band V w input
      (embStk componentReg {S with R := (Function.update (Function.update S.R 147 archive) 132 output)}) := by
  have harchive : embStk componentReg {S with R := Function.update S.R 147 archive} = embStk componentReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hne : componentReg k ≠ (147 : Fin 148) := by
      intro he
      have hv := congrArg (fun j : Fin 148 => j.val) he
      change k.val = 147 at hv
      have := k.isLt
      omega
    simp only [embStk,Function.comp_apply,Function.update_of_ne hne]
  have hproject := componentProject_updateR_inner {S with R := Function.update S.R 147 archive}
    (132 : Fin 144) output
  have hc : componentReg (132 : Fin 144) = (132 : Fin 148) := by decide
  rw [hc,harchive] at hproject
  rw [hproject]
  exact h.update_output output

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def publishArchivedInterior (lower upper : Fin 148) : Pr P 148 Q A U :=
  .seq restoreRecoveryOutput (windowedPublication lower upper)

def publishArchivedInteriorCost (P q s t u band a b : ℕ) : ℕ :=
  archiveResidualPrefixCost q s+((4*a+4)+((4*b+4)+(publishHaloCost P q s t u band a b+(2*(a+b)+5))))

theorem publishArchivedInterior_exec {P₀ N q l s t u band a b : ℕ} [NeZero s]
    (lower upper : Fin 148) (hports : [lower,upper,141,142,143].Nodup)
    (hlower : lower ≠ 132 ∧ lower ≠ 147) (hupper : upper ≠ 132 ∧ upper ≠ 147)
    (hA : 4 ≤ A) (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : band ≤ s)
    (D C : ZMod s → GaussianInt) (tail archiveTail input : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg S))
    (ha : (S.R lower).length = a) (hb : (S.R upper).length = b)
    (h141 : S.R 141 = []) (h142 : S.R 142 = []) (h143 : S.R 143 = [])
    (harchive : S.R 147 = cstream A (2*q+8) (chirpLine s D)++archiveTail)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s C)++tail) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    let F : Stacks 148 A := {S with R := (Function.update (Function.update S.R 147 archiveTail) 132
      (cstream A (2*q+8) (chirpLine s G)++tail))}
    ∃ v' m, v'.user = v.user ∧ m ≤ publishArchivedInteriorCost P₀ q s t u band a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (publishArchivedInterior lower upper) (mk v S) m (mk v' F) ∧
      LengthKeyReady P₀ N q l s t u band 0 0 input (embStk componentReg F) := by
  dsimp only
  let words := cstream A (2*q+8) (chirpLine s D)
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hclean : ∀ k ∈ ([(94 : Fin 148),131,134,135,143]), S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg] using hready.fresh 131 (by simp)
    · simpa [embStk,componentReg] using hready.fresh 134 (by simp)
    · simpa [embStk,componentReg] using hready.fresh 135 (by simp)
    · exact h143
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := restoreRecoveryOutput_exec (body := embTab groupReg body)
    q s words archiveTail (by simp [words]) v S hq hs harchive hclean
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update S.R 147 archiveTail) 132 (words++S.R 132))}
  have hready₁ := componentReady_archive_output hready archiveTail (words++S.R 132)
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := windowedPublication_exec (body := body) lower upper hports
    hA hst has hbs hband D C tail input v₁ S₁ hready₁
    (by simpa [S₁,hlower.1,hlower.2] using ha) (by simpa [S₁,hupper.1,hupper.2] using hb)
    (by simpa [S₁] using h141) (by simpa [S₁] using h142) (by simpa [S₁] using h143)
    (by simp [S₁,words,hsource])
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_,
    componentReady_archive_output hready archiveTail _⟩
  apply congrArg (mk v₂)
  simp only [S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
