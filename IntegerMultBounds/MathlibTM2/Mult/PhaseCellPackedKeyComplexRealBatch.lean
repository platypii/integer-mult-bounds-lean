module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyRealBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! Execute component expansion and the actual shared-factor packed numerical batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type}
variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

def packedKeyComplexReg : Fin 276 → Fin 277 := Fin.castLE (by decide)

theorem packedKeyComplexReg_injective : Function.Injective packedKeyComplexReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 277 => k.val) he)

theorem packedKeyComplexReg_off : ∀ i, packedKeyComplexReg i ≠ (276 : Fin 277) := by
  intro i he
  have hh := congrArg Fin.val he
  have hi := i.isLt
  change i.val = 276 at hh
  omega

noncomputable def packedKeyComplexRealBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 277 Q A U :=
  .seq (expandComplexKeyCounted 264 267 269 263 270 271 272 276)
    (embProg packedKeyComplexReg id (packedKeyRealBatch hR hQ))

/-- Expansion preserves the solver bank except its input queue and replica
counter. The original count is kept in the fresh register for later pairing. -/
theorem packedKeyComplexExpand_exec (bodyComplex : P → Pr P 277 Q A U)
    (hA : 4 ≤ A) {s : ℕ} (a L W : ℕ) (hfit : a+L ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (v : HS 277 Q A U) (M : Stacks 276 A)
    (hreplicas : (M.R 264).length = Fs.length)
    (hwidth : (M.R 267).length = L*W)
    (hsrc : M.R 263 = cstream A W ((Fs.map (packedInterval a L)).flatten)++tail)
    (hblank : ∀ i ∈ ([269,270,271,272] : List (Fin 276)), M.R i = []) :
    let queue := cstream A W (((complexComponentFields Fs).map (packedInterval a L)).flatten)++tail
    let M₁ : Stacks 276 A := {M with R := (Function.update (Function.update M.R 263 queue)
      264 (List.replicate Fs.length tick++M.R 264))}
    ∃ v' n G, v'.user = v.user ∧ n ≤ Fs.length*(26*(L*W)+17)+34 ∧
      Exec bodyComplex (expandComplexKeyCounted 264 267 269 263 270 271 272 276)
        (mk v (extendStacks (by decide : 276 ≤ 277) M)) n (mk v' G) ∧
      embStk packedKeyComplexReg G = M₁ ∧
      G.L 276 = [] ∧ G.R 276 = List.replicate Fs.length tick := by
  dsimp only
  let T₀ := extendStacks (by decide : 276 ≤ 277) M
  obtain ⟨v',n,hu,hn,he⟩ := expandComplexFields_exec (body := bodyComplex)
    (replicas := 264) (width := 267) (count := 269) (src := 263)
    (imag := 270) (saved := 271) (tmp := 272) (hold := 276)
    (by decide) hA a L W hfit Fs tail v T₀
    (by simpa [T₀,extendStacks] using hreplicas)
    (by simpa [T₀,extendStacks] using hwidth)
    (by simpa [T₀,extendStacks] using hsrc)
    (by simpa [T₀,extendStacks] using hblank 269 (by simp))
    (by simpa [T₀,extendStacks] using hblank 270 (by simp))
    (by simpa [T₀,extendStacks] using hblank 271 (by simp))
    (by simpa [T₀,extendStacks] using hblank 272 (by simp))
    (by simp [T₀,extendStacks])
  refine ⟨v',n,_,hu,hn,he,?_,?_,?_⟩
  · refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      simp [embStk,packedKeyComplexReg,T₀,extendStacks,i.isLt]
    · funext i
      have hoff : packedKeyComplexReg i ≠ (276 : Fin 277) := packedKeyComplexReg_off i
      have heq (j : Fin 276) : packedKeyComplexReg i = packedKeyComplexReg j ↔ i = j :=
        packedKeyComplexReg_injective.eq_iff
      change (Function.update (Function.update (Function.update T₀.R 276 _)
        (packedKeyComplexReg 263) _) (packedKeyComplexReg 264) _) (packedKeyComplexReg i) = _
      simp only [Function.update_apply,heq,hoff,ite_false]
      simp [T₀,extendStacks,packedKeyComplexReg,i.isLt]
  · simp [T₀,extendStacks]
  · simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
