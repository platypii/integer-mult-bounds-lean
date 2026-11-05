module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstBoundaryMasterPreparation

/-! The first crop starts at zero and has the full core width. Decode that
width, multiply by the narrow word ruler, and release the decoded control. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

def exportFirstBoundaryCount (dst : Fin 117) : Pr P 117 Q A U :=
  .seq (toUnary 56 26 30 31 32) (.seq (unaryProduct 26 17 dst 27 28) (uclear 26))

theorem exportFirstBoundaryCount_exec (body : P → Pr P 117 Q A U)
    (dst : Fin 117) (hreg : [26,17,dst,27,28].Nodup) (D width w : ℕ) (hfit : width < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbinary : S.R 56 = binSyms D width) (hwide : (S.R 17).length = w)
    (hdst : S.R dst = []) (h26 : S.R 26 = [])
    (hscratch : S.R 30 = [] ∧ S.R 31 = [] ∧ S.R 32 = [] ∧ S.R 27 = [] ∧ S.R 28 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (6*width+11*D+6)+(width*(4*w+9)+4)+(2*width+2) ∧
      Exec body (exportFirstBoundaryCount dst) (mk v S) n
        (mk v' {S with R := Function.update S.R dst (List.replicate (width*w) tick)}) := by
  obtain ⟨h30,h31,h32,h27,h28⟩ := hscratch
  have hr := hreg
  regs_ne hr
  have hdst26 : dst ≠ 26 := Ne.symm (by assumption)
  obtain ⟨u,a,hu,ha,he⟩ := toUnary_exec_linear (body := body)
    (a := 56) (z := 26) (w := 30) (t := 31) (t₂ := 32) (by decide +kernel)
    hfit v S hbinary h30 h31 h32
  simp only [h26,List.append_nil] at he
  let M : Stacks 117 A := {S with R := Function.update S.R 26 (List.replicate width tick)}
  obtain ⟨u',b,hu',hb,hprod⟩ := unaryProduct_exec (body := body)
    (a := 26) (b := 17) (dst := dst) (t₁ := 27) (t₂ := 28) hreg u M
    (by simpa [M] using h27) (by simpa [M] using h28)
  have hprod' : Exec body (unaryProduct 26 17 dst 27 28) (mk u M) b
      (mk u' {M with R := Function.update M.R dst (List.replicate (width*w) tick)}) := by
    simpa [M,hwide,hdst,hdst26] using hprod
  have hb' : b ≤ width*(4*w+9)+4 := by simpa [M,hwide] using hb
  let N : Stacks 117 A := {M with R := Function.update M.R dst (List.replicate (width*w) tick)}
  obtain ⟨v',hv,hclear⟩ := uclear_exec (body := body) 26 u' N
  have hN26 : N.R 26 = List.replicate width tick := by simp [N,M,hdst26.symm]
  rw [hN26,List.length_replicate] at hclear
  have hend : ({N with R := Function.update N.R 26 []} : Stacks 117 A) =
      {S with R := Function.update S.R dst (List.replicate (width*w) tick)} := by
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext i
    by_cases hi : i = 26
    · subst i; simp [hdst26.symm,h26]
    · simp [N,M,hi,Function.update_apply]
  rw [hend] at hclear
  refine ⟨v',a+(b+(2*width+2)),hv.trans (hu'.trans hu),by omega,?_⟩
  exact Exec.seq he (Exec.seq hprod' hclear)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
