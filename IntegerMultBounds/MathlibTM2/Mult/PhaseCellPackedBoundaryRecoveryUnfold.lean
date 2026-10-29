module

public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! Derive the inverse-fold handoff from the actual boundary solver's retained
workspace. Only the six newly allocated ports need fresh-bank hypotheses. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Keep the complete solver bank in place beside six recovery ports. -/
def packedBoundaryRecoveryBase : Fin 242 → Fin 248 := Fin.castLE (by decide)

theorem packedBoundaryRecoveryBase_injective : Function.Injective packedBoundaryRecoveryBase := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 248 => k.val) h)

private theorem empty_swap {α β : Type*} [DecidableEq α] (f : α → List β)
    (a b x : α) (ha : f a = []) (hb : f b = []) (hx : f x = []) :
    f (Equiv.swap a b x) = [] := by
  by_cases hxa : x = a
  · subst x; simpa using hb
  by_cases hxb : x = b
  · subst x; simpa using ha
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  exact hx

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

/-- All old-bank preconditions come from the solver endpoint. Fresh ports are
independent of the solution and its borrowed suffix. -/
theorem packedBoundaryRecoveryUnfold_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w W : ℕ) (B : Finset (ZMod s)) (solution : List GaussianInt)
    (hlen : solution.length = B.card) (tail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hready : BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase S)))) q w W B.card)
    (h143 : S.R 143 = []) (hcount : S.R 116 = List.replicate B.card tick)
    (hsrc : S.R 238 = cstream A w solution ++ tail)
    (hfreshL : ∀ i : Fin 248, 242 ≤ i.val → S.L i = [])
    (hfreshR : ∀ i : Fin 248, 242 ≤ i.val → S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ ScalarPlacement.moveCountedLineCost B.card w +
        (generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12) ∧
      Exec body packedBoundarySolutionUnfold (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          238 tail) 231 []) 245
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  have hleft : ∀ i : Fin 224, (embStk packedBoundaryUnfoldReg S).L i = [] := by
    intro i
    have hi := hwork.left i
    have h203 : S.L 203 = [] := hwork.left 189
    have h205 : S.L 205 = [] := hwork.left 191
    have h212 : S.L 212 = [] := hwork.left 198
    have h218 : S.L 218 = [] := hwork.left 204
    exact empty_swap S.L 218 245 _ h218 (hfreshL 245 (by decide))
      (empty_swap S.L 212 244 _ h212 (hfreshL 244 (by decide))
        (empty_swap S.L 205 243 _ h205 (hfreshL 243 (by decide))
          (empty_swap S.L 203 242 _ h203 (hfreshL 242 (by decide)) hi)))
  have hmul : ∀ i : Fin 64,
      (embStk packedBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [] := by
    intro i
    change S.R (packedBoundaryUnfoldReg (boundaryFactorMulReg i)) = []
    rw [packedBoundaryUnfoldReg_low _ i.isLt]
    have hi := i.isLt
    simpa [embStk,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,
      packedBoundaryFactorReg,boundaryFactorMulReg,Fin.ext_iff,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega] using hwork.mul i
  have hclean : ∀ i ∈ ([231,239,246,247,143,242,243,198,237,245,222,225,244,215,229] :
      List (Fin 248)), S.R i = [] := by
    have hc := packedBoundaryRecovery_clean hwork hready
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc 231 (by decide)
    · exact hc 239 (by decide)
    · exact hfreshR 246 (by decide)
    · exact hfreshR 247 (by decide)
    · exact h143
    · exact hfreshR 242 (by decide)
    · exact hfreshR 243 (by decide)
    · exact hc 198 (by decide)
    · exact hc 237 (by decide)
    · exact hfreshR 245 (by decide)
    · exact hc 222 (by decide)
    · exact hc 225 (by decide)
    · exact hfreshR 244 (by decide)
    · exact hc 215 (by decide)
    · exact hc 229 (by decide)
  exact packedBoundarySolutionUnfold_exec hA w B solution hlen tail v S hleft hmul
    (by simp only [hcount,List.length_replicate]) hsrc
    (packedBoundaryRecovery_width hready) hclean

/-- Allocate the recovery workspace as a blank bank extension. No fresh-bank
or inverse-fold readiness oracle is needed beyond the solver's own postconditions. -/
theorem packedBoundaryRecoveryUnfold_extended_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w W : ℕ) (B : Finset (ZMod s)) (solution : List GaussianInt)
    (hlen : solution.length = B.card) (tail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 242 A)
    (hwork : PackedBoundarySolveWorkspace q S)
    (hready : BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg S))) q w W B.card)
    (h143 : S.R 143 = []) (hcount : S.R 116 = List.replicate B.card tick)
    (hsrc : S.R 238 = cstream A w solution ++ tail) :
    let F := extendStacks (by decide : 242 ≤ 248) S
    ∃ v' n, v'.user = v.user ∧
      n ≤ ScalarPlacement.moveCountedLineCost B.card w +
        (generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12) ∧
      Exec body packedBoundarySolutionUnfold (mk v F) n
        (mk v' {F with R := (Function.update (Function.update (Function.update F.R
          238 tail) 231 []) 245
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  dsimp only
  have hproj : embStk packedBoundaryRecoveryBase
      (extendStacks (by decide : 242 ≤ 248) S) = S := embStk_extendStacks _ S
  exact packedBoundaryRecoveryUnfold_exec hA q w W B solution hlen tail v _
    (by rw [hproj]; exact hwork) (by rw [hproj]; exact hready)
    (by simpa [extendStacks] using h143) (by simpa [extendStacks] using hcount)
    (by simpa [extendStacks] using hsrc)
    (fun i hi => (extendStacks_fresh _ S i hi).1)
    (fun i hi => (extendStacks_fresh _ S i hi).2)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
