module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCounterSeedLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounters

/-! Concrete seed initialization in the existing bank. Retained binary masters
55--57, width ruler 58 and empty zero source 59 are outside the metadata table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

def boundarySeedGlobals : Fin 3 → Fin 117 := ![55,56,57]

theorem boundaryCounterRegister_off_upper (k : Fin 117) (hk : 54 ≤ k.val) (r : TblR 9) :
    boundaryCounterRegister r ≠ k := by
  have hb := boundaryCounterRegister_bounds r
  intro h
  have he := congrArg Fin.val h
  omega

theorem standardBoundarySeedLoad_exec (body : P → Pr P 117 Q A U)
    (D s width W : ℕ) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = []) (depth : ℕ) :
    let F := loadedInputTable boundaryCounterRegister (seedSources boundarySeedGlobals 59) D
      (seedSourceValue value 59) S
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(64*D+81)) depth
        (chirpBankLoad boundaryCounterRegister (seedSources boundarySeedGlobals 59) 58 59)
        (mk v S) (64*D+81) (mk v' F) ∧
      tblHolds boundaryCounterRegister F (tblRho D (List.replicate D tick) [] (seed A s width W)) := by
  exact BoundaryCropMetadata.loadSeed_exec body boundaryCounterRegister boundaryCounterRegister_injective
    boundarySeedGlobals 59 58
    (boundaryCounterRegister_off_upper 58 (by decide))
    (boundaryCounterRegister_off_upper 59 (by decide))
    (by intro j r; apply boundaryCounterRegister_off_upper; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> decide) D s width W value hvalues hfit v S hwidth hzero hwords hblank depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
