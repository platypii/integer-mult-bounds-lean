module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedRecoveryAssembly
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSecondInterior

/-! Assemble both physical piece archives with six shared scratch tapes and
separate output tapes. The row reserve is independent of replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

namespace CyclicPackedAssemblyPlacement
abbrev extend : Fin 842 → Fin 850 := Fin.castLE (by decide)
def left (i : Fin 12) : Fin 850 :=
  ([839,842,94,843,247,125,844,848,845,846,121,847] : List (Fin 850))[i.val]'(by simpa using i.isLt)
def right (i : Fin 12) : Fin 850 :=
  ([838,842,394,843,547,425,844,849,845,846,421,847] : List (Fin 850))[i.val]'(by simpa using i.isLt)
theorem left_injective : Function.Injective left := by decide +kernel
theorem right_injective : Function.Injective right := by decide +kernel
theorem right_off_left (i : Fin 12) : right i ≠ 125 ∧ right i ≠ 247 ∧ right i ≠ 848 := by revert i; decide +kernel
end CyclicPackedAssemblyPlacement

open CyclicPackedAssemblyPlacement
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 850 Q A U}

def cyclicPackedAssembly : Pr P 850 Q A U :=
  .seq (placedPackedRecoveryAssembly left) (placedPackedRecoveryAssembly right)

theorem cyclicPackedAssembly_exec (H K : ReplicaHaloProblem s)
    (rowsL rowsR : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hlenL : rowsL.length = H.Fs.length) (hlenR : rowsR.length = K.Fs.length)
    (hA : 4 ≤ A) (tailXL tailYL tailXR tailYR : List (Fin (A+4)))
    (v : HS 850 Q A U) (S : Stacks 842 A)
    (controlsL : ReplicaAssemblyControls H CyclicSecondInteriorPlacement.left.plan.gather
      (CyclicSecondInteriorPlacement.extend (CyclicRecoveryPlacement.bank 239)) S)
    (controlsR : ReplicaAssemblyControls K CyclicSecondInteriorPlacement.right.plan.gather
      (CyclicSecondInteriorPlacement.extend (CyclicRecoveryPlacement.bank 238)) S)
    (hXL : S.R 247 = rowsL.flatMap (fun row => cstream A H.wordWidth (packedInterval H.origin H.span row.1))++tailXL)
    (hYL : S.R 125 = rowsL.flatMap (fun row => cstream A H.wordWidth (packedInterval H.origin H.span row.2))++tailYL)
    (hXR : S.R 547 = rowsR.flatMap (fun row => cstream A K.wordWidth (packedInterval K.origin K.span row.1))++tailXR)
    (hYR : S.R 425 = rowsR.flatMap (fun row => cstream A K.wordWidth (packedInterval K.origin K.span row.2))++tailYR)
    (depth : ℕ) :
    let E := extendStacks (by decide : 842 ≤ 850) S
    let wordsL := rowsL.map (fun row => cstream A H.wordWidth
      (packedInterval H.origin H.span (publicationField H.t H.band H.origin (H.origin+H.span) row.1 row.2)))
    let wordsR := rowsR.map (fun row => cstream A K.wordWidth
      (packedInterval K.origin K.span (publicationField K.t K.band K.origin (K.origin+K.span) row.1 row.2)))
    ∃ vf G n, vf.user = v.user ∧
      n ≤ (rowsL.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
        (rowsR.length*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4) ∧
      G.R 848 = wordsL.reverse.flatten ∧ G.R 849 = wordsR.reverse.flatten ∧
      G.R 247 = tailXL ∧ G.R 125 = tailYL ∧ G.R 547 = tailXR ∧ G.R 425 = tailYR ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v E)+depth+
        (2*retainedPackedPublicationMergeCost H.span H.wordWidth+
          2*retainedPackedPublicationMergeCost K.span K.wordWidth)) depth cyclicPackedAssembly (mk v E) n (mk vf G) ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = E.L ∧
      (∀ k, k ∉ [125,247,848,425,547,849] → G.R k = E.R k) := by
  dsimp only
  let E := extendStacks (by decide : 842 ≤ 850) S
  let wordsL := rowsL.map (fun row => cstream A H.wordWidth
    (packedInterval H.origin H.span (publicationField H.t H.band H.origin (H.origin+H.span) row.1 row.2)))
  let wordsR := rowsR.map (fun row => cstream A K.wordWidth
    (packedInterval K.origin K.span (publicationField K.t K.band K.origin (K.origin+K.span) row.1 row.2)))
  have hread (i : Fin 842) : E.R (extend i) = S.R i :=
    congrArg (fun C : Stacks 842 A => C.R i) (embStk_extendStacks (by decide : 842 ≤ 850) S)
  have hblank (i : Fin 850) (hi : 842 ≤ i.val) : E.R i = [] :=
    (extendStacks_fresh (by decide : 842 ≤ 850) S i hi).2
  obtain ⟨vi,m,huL,hmL,heL⟩ := placedPackedRecoveryAssembly_exec (body := body) left left_injective
    H.t H.band H.origin H.span H.wordWidth H.s_lt_t H.span_fit rowsL hA tailXL tailYL v E
    ((hread 839).trans controlsL.mask) ((congrArg List.length (hread 94)).trans controlsL.width)
    ((hread 247).trans hXL) ((hread 125).trans hYL)
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by decide))
    (((congrArg List.length (hread 121)).trans controlsL.replicas).trans hlenL.symm) depth
  let F : Stacks 850 A := {E with R := (Function.update (Function.update (Function.update E.R 125 tailYL)
    247 tailXL) 848 (wordsL.reverse.flatten++E.R 848))}
  have hright (i : Fin 12) : F.R (right i) = E.R (right i) := by
    have hi := right_off_left i
    simp only [F,Function.update_of_ne hi.2.2,Function.update_of_ne hi.2.1,Function.update_of_ne hi.1]
  obtain ⟨vf,n,huR,hmR,heR⟩ := placedPackedRecoveryAssembly_exec (body := body) right right_injective
    K.t K.band K.origin K.span K.wordWidth K.s_lt_t K.span_fit rowsR hA tailXR tailYR vi F
    (((hright 0).trans (hread 838)).trans controlsR.mask)
    ((congrArg List.length ((hright 2).trans (hread 394))).trans controlsR.width)
    (((hright 4).trans (hread 547)).trans hXR) (((hright 5).trans (hread 425)).trans hYR)
    (by
      intro i hi
      rw [hright i]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by decide))
    (((congrArg List.length ((hright 10).trans (hread 421))).trans controlsR.replicas).trans hlenR.symm) depth
  let G : Stacks 850 A := {F with R := (Function.update (Function.update (Function.update F.R 425 tailYR)
    547 tailXR) 849 (wordsR.reverse.flatten++F.R 849))}
  have hstock : mnSize (mk vi F)+depth ≤ mnSize (mk v E)+depth+2*retainedPackedPublicationMergeCost H.span H.wordWidth := heL.final
  refine ⟨vf,G,m+n,huR.trans huL,Nat.add_le_add hmL hmR,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,?_⟩
  · simp [G,F,hblank 848 (by decide),wordsL]
  · simp [G,F,hblank 849 (by decide),wordsR]
  · simp [G,F]
  · simp [G,F]
  · simp [G]
  · simp [G]
  · apply ExecWithin.seq (heL.mono ?_) (heR.mono ?_)
    · intro d z hz
      change mnSize z+d ≤ mnSize (mk v E)+depth+
        (2*retainedPackedPublicationMergeCost H.span H.wordWidth+2*retainedPackedPublicationMergeCost K.span K.wordWidth)
      change mnSize z+d ≤ mnSize (mk v E)+depth+2*retainedPackedPublicationMergeCost H.span H.wordWidth at hz
      omega
    · intro d z hz
      change mnSize z+d ≤ mnSize (mk v E)+depth+
        (2*retainedPackedPublicationMergeCost H.span H.wordWidth+2*retainedPackedPublicationMergeCost K.span K.wordWidth)
      change mnSize z+d ≤ mnSize (mk vi F)+depth+2*retainedPackedPublicationMergeCost K.span K.wordWidth at hz
      omega
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    simp only [G,F,Function.update_of_ne hk.2.2.2.2.2,Function.update_of_ne hk.2.2.2.2.1,
      Function.update_of_ne hk.2.2.2.1,Function.update_of_ne hk.2.2.1,Function.update_of_ne hk.2.1,
      Function.update_of_ne hk.1]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
