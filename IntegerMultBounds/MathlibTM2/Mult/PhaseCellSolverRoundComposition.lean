module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundTape
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedError

/-! Compose a frame-restoring numerical solver with its executed normalization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem solver_round_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w q p j E k target : ℕ) (hp : p ≤ q) (hw : q+E+5 ≤ w)
    (hk : p+E+5 ≤ k) (hsize : q-p+j+k ≤ w)
    (solver : Pr P T Q A U) (v v₁ : HS T Q A U) (S : Stacks T A) (n : ℕ)
    (G : ZMod s → GaussianInt) (x : ZMod s → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 4*(2 : ℝ)^E)
    (herror : ∀ i, ‖pairedCellRead q w (cstream A w (chirpLine s G)) i-x i‖ ≤ 1/(2 : ℝ)^target)
    (hu : v₁.user = v.user)
    (hsolver : Exec body solver (mk v S) n
      (mk v₁ {S with R := (Function.update S.R src (cstream A w (chirpLine s G)))}))
    (hdst : S.R dst = []) (hg : topShiftG tmp cW cS cE cD sp sg cy w (q-p+j) k S.R) :
    ∃ v', ∃ H : ZMod s → GaussianInt, v'.user = v.user ∧
      Exec body (.seq solver (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy)))
        (mk v S) (n+(1+(s*(topShiftWordCost w (q-p+j) k+1)+1)+(2*(s*k)+2)))
        (mk v' {S with R := (Function.update S.R src (cstream A k (chirpLine s H)))}) ∧
      ∀ i : ZMod s, ‖pairedCellRead p k (cstream A k (chirpLine s H)) i-
        ((2 : ℂ)^j)⁻¹*x i‖ ≤ 2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j := by
  have hregs := hreg
  regs_ne hregs
  let S₁ : Stacks T A := {S with R := Function.update S.R src (cstream A w (chirpLine s G))}
  have hg₁ : topShiftG tmp cW cS cE cD sp sg cy w (q-p+j) k S₁.R := by
    simpa [S₁,topShiftG,ne_comm, *] using hg
  have hm : ∀ i : ZMod s, ‖pairedCellRead q w (cstream A w (chirpLine s G)) i‖ ≤ 8*(2 : ℝ)^E :=
    fun i => computed_solution_norm target E _ _ (hx i) (herror i)
  obtain ⟨v',H,hu',he,hr⟩ := finalRound_tape_exec (body := body) hA hreg w q p j E k hp hw hk hsize
    G hm v₁ S₁ (by simp only [S₁,Function.update_self])
    (by simpa only [S₁,Function.update_of_ne ‹src ≠ dst›.symm] using hdst) hg₁
  refine ⟨v',H,hu'.trans hu,?_,?_⟩
  · have heq : {S₁ with R := Function.update S₁.R src (cstream A k (chirpLine s H))} =
        {S with R := Function.update S.R src (cstream A k (chirpLine s H))} := by
      simp only [S₁,Function.update_idem]
    exact (Exec.seq hsolver he).cast rfl (congrArg (mk v') heq)
  · intro i
    rw [hr i]
    exact scaleRound_error p j _ _ _ (herror i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
