module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSizeStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTableValues

/-! Sum clipped block sizes from runtime unary dimensions with a counted scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def packedSizeLoop : Pr P 154 Q A U := scanP 152 153 packedSizeStep

def packedSizeLoopCost (N W start L : ℕ) : ℕ :=
  (∑ i ∈ Finset.range L, (packedSizeStepCost (start+i) W N+3))+2*L+4

theorem packedSizeLoop_exec (N W start L : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hN : (S.R 116).length = N) (hW : (S.R 94).length = W)
    (hcursor : (S.R 151).length = start) (hcount : (S.R 152).length = L)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,153], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ packedSizeLoopCost N W start L ∧
      Exec body packedSizeLoop (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 0
          (List.replicate (packedBandWordCount N W L start) tick++S.R 0))
          151 (List.replicate L tick++S.R 151))}) := by
  let Ψ : ℕ → Regs 154 A := fun i => Function.update (Function.update S.R
    0 (List.replicate (packedBandWordCount N W i start) tick++S.R 0))
    151 (List.replicate i tick++S.R 151)
  have hstep : IterSpec body packedSizeStep 152 153 Ψ (fun i => packedSizeStepCost (start+i) W N) L := by
    intro i hi vi Si hSi
    have hoff (k : Fin 154) (hk0 : k ≠ 0) (hk151 : k ≠ 151) (hk152 : k ≠ 152) (hk153 : k ≠ 153) :
        Si.R k = S.R k := by rw [hSi k hk152 hk153]; simp [Ψ,hk0,hk151]
    have hcursor' : (Si.R 151).length = start+i := by
      rw [hSi 151 (by decide) (by decide)]
      simp [Ψ,hcursor,Nat.add_comm]
    obtain ⟨vi',hu,he⟩ := packedSizeStep_exec (body := body) (start+i) W N vi Si hcursor'
      (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact hW)
      (by rw [hoff 116 (by decide) (by decide) (by decide) (by decide)]; exact hN) (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;>
          rw [hoff _ (by decide) (by decide) (by decide) (by decide)] <;> exact hfresh _ (by simp))
    let count := min N (start+i+W+1)-(start+i-W)
    let R' : Regs 154 A := Function.update (Function.update Si.R 0 (List.replicate count tick++Si.R 0))
      151 (tick::Si.R 151)
    refine ⟨vi',R',packedSizeStepCost (start+i) W N,hu,le_rfl,he,by simp [R'],by simp [R'],?_⟩
    intro k hk152 hk153
    by_cases hk0 : k = 0
    · subst k
      rw [show R' 0 = List.replicate count tick++Si.R 0 by simp [R'],hSi 0 (by decide) (by decide)]
      simp [Ψ,packedBandWordCount_succ,count,Nat.add_comm]
      rw [← List.append_assoc,List.replicate_append_replicate]
    by_cases hk151 : k = 151
    · subst k
      rw [show R' 151 = tick::Si.R 151 by simp [R'],hSi 151 (by decide) (by decide)]
      simp [Ψ,List.replicate_succ]
    rw [show R' k = Si.R k by simp [R',hk0,hk151],hSi k hk152 hk153]
    simp [Ψ,hk0,hk151]
  obtain ⟨v',R',steps,hu,hsteps,he,h152,h153,hrest⟩ := scanP_exec (body := body)
    (show (152 : Fin 154) ≠ 153 by decide) hstep 0 v S (by simp [hcount]) (by
      intro k _ _
      by_cases hk0 : k = 0 <;> by_cases hk151 : k = 151 <;> simp [Ψ,packedBandWordCount,hk0,hk151])
  have hR : R' = Ψ L := by
    funext k
    by_cases hk152 : k = 152
    · subst k; simpa [Ψ,hfresh 153 (by simp)] using h152
    by_cases hk153 : k = 153
    · subst k; simpa [Ψ,hfresh 153 (by simp)] using h153
    simpa [hcount] using hrest k hk152 hk153
  rw [hR] at he
  refine ⟨v',steps,hu,?_,he⟩
  simpa [packedSizeLoopCost,hcount,hfresh 153 (by simp)] using hsteps

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
