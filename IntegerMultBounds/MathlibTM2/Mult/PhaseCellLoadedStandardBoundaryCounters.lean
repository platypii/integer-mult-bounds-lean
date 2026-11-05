module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundarySeedLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounters

/-! Concrete seed initialization in the existing bank. Retained binary masters
55--57, width ruler 58 and empty zero source 59 are outside the metadata table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

theorem loadedStandardBoundaryCounters_exec (body : P → Pr P 117 Q A U)
    (last : Bool) (D s width W : ℕ)
    (hwidthPos : 0 < width) (hwordPos : 0 < W) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = []) (depth : ℕ) :
    let M := loadedInputTable boundaryCounterRegister (seedSources boundarySeedGlobals 59) D
      (seedSourceValue value 59) S
    ∃ v' n, v'.user = v.user ∧ n ≤ (64*D+81)+(16*tblC D 0+6*(s*W)+22*D+13) ∧
      Exec body (.seq (chirpBankLoad boundaryCounterRegister (seedSources boundarySeedGlobals 59) 58 59)
        (.seq (standardBoundaryCounterProgram last) (tblCompile boundaryCounterRegister restoreCode)))
        (mk v S) n (mk v' {M with R := (Function.update (Function.update M.R 26
          (List.replicate (coreStart width (index last s width)*W) tick)) 24
          (List.replicate (coreLength s width (index last s width)*W) tick))}) := by
  dsimp only
  obtain ⟨u,hu,hload,hholds⟩ := standardBoundarySeedLoad_exec body D s width W value hvalues hfit
    v S hwidth hzero hwords hblank depth
  let M := loadedInputTable boundaryCounterRegister (seedSources boundarySeedGlobals 59) D
    (seedSourceValue value 59) S
  have hoff (i : Fin 117) (hi : i.val < 30) : ∀ r, i ≠ boundaryCounterRegister r := by
    intro r he
    have hb := boundaryCounterRegister_bounds r
    have hh := congrArg Fin.val he
    omega
  have hmasterM : M.R 26 = [] ∧ M.R 24 = [] := by
    constructor
    · rw [loadedInputTable_off _ _ _ _ _ _ (hoff 26 (by decide))]; exact hmasters.1
    · rw [loadedInputTable_off _ _ _ _ _ _ (hoff 24 (by decide))]; exact hmasters.2
  obtain ⟨v',n,hv,hn,hex⟩ := restoredStandardBoundaryCounters_exec (body := body) last D s width W
    (seed A s width W) (by simp [seed]) (by simp [seed]) (by simp [seed])
    hwidthPos hwordPos hroom hvolumeFit
    (seed_fits A D s width W (by omega) hwordPos (by omega) hvolumeFit)
    (List.replicate D tick) (by simp) u M hholds hmasterM (seed_working_zero A s width W)
  exact ⟨v',(64*D+81)+n,hv.trans hu,Nat.add_le_add_left hn _,Exec.seq hload.toExec hex⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
