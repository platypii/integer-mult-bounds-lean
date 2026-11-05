module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCounterSeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableLoad

/-! Load three retained binary inputs and generate six zero working words
through the existing restoring padded-bank loader. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def seedSources (globals : Fin 3 → Fin T) (zero : Fin T) : Fin 9 → Fin T :=
  ![globals 0,globals 1,globals 2,zero,zero,zero,zero,zero,zero]

def seedSourceBits (D : ℕ) (zero k : Fin T) := if k = zero then 0 else D
def seedSourceValue (value : Fin T → ℕ) (zero k : Fin T) := if k = zero then 0 else value k

theorem seedLoadCost_eq (rg : TblR 9 → Fin T) (globals : Fin 3 → Fin T) (zero : Fin T)
    (hoff : ∀ j, globals j ≠ zero) (D : ℕ) :
    chirpBankLoadCost rg (seedSources globals zero) D 0 (seedSourceBits D zero) = 64*D+81 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,List.ofFn_succ,
    seedSources,seedSourceBits,hoff]
  omega

theorem loadSeed_exec (body : P → Pr P T Q A U) (rg : TblR 9 → Fin T)
    (hinj : Function.Injective rg) (globals : Fin 3 → Fin T) (zero widthMaster : Fin T)
    (hwidthOff : ∀ r, rg r ≠ widthMaster) (hzeroOff : ∀ r, rg r ≠ zero)
    (hglobalOff : ∀ j r, rg r ≠ globals j) (hoff : ∀ j, globals j ≠ zero)
    (D s width W : ℕ) (value : Fin T → ℕ)
    (hvalues : ∀ j, value (globals j) = ![s,width,W] j)
    (hfit : ∀ j, value (globals j) < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R widthMaster).length = D) (hzero : S.R zero = [])
    (hwords : ∀ j, S.R (globals j) = binSyms D (value (globals j)))
    (hblank : ∀ r, S.R (rg r) = []) (depth : ℕ) :
    let cost := 64*D+81
    let F := loadedInputTable rg (seedSources globals zero) D (seedSourceValue value zero) S
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost) depth
        (chirpBankLoad rg (seedSources globals zero) widthMaster zero) (mk v S) cost (mk v' F) ∧
      tblHolds rg F (tblRho D (List.replicate D tick) [] (seed A s width W)) := by
  dsimp only
  have hinput (i r) : rg r ≠ seedSources globals zero i := by
    fin_cases i <;> simp [seedSources,hglobalOff,hzeroOff]
  have hfits (i) : seedSourceValue value zero (seedSources globals zero i) <
      2^seedSourceBits D zero (seedSources globals zero i) := by
    fin_cases i <;> simp [seedSources,seedSourceValue,seedSourceBits,hoff,hfit]
  have hbits (i) : seedSourceBits D zero (seedSources globals zero i) ≤ D := by
    fin_cases i <;> simp [seedSources,seedSourceBits,hoff]
  have hsource (i) : S.R (seedSources globals zero i) =
      binSyms (seedSourceBits D zero (seedSources globals zero i))
        (seedSourceValue value zero (seedSources globals zero i)) := by
    fin_cases i <;> simp [seedSources,seedSourceBits,seedSourceValue,hoff,hwords,hzero,binSyms]
  obtain ⟨v',hu,hx⟩ := chirpBankLoad_exec (body := body) rg hinj (seedSources globals zero)
    widthMaster zero hwidthOff hzeroOff hinput D 0 (seedSourceBits D zero) (seedSourceValue value zero)
    hfits hbits v S hwidth (by rw [hzero]; rfl) hsource hblank
  rw [seedLoadCost_eq rg globals zero hoff D] at hx
  have hseed : (fun i => seedSourceValue value zero (seedSources globals zero i)) = (seed A s width W).val := by
    funext i
    fin_cases i <;> simp [seedSources,seedSourceValue,hoff,hvalues,seed]
  refine ⟨v',hu,mn_native_exec_within hx 3 (chirpBankLoad_native _ _ _ _) depth _ (by omega),?_⟩
  simpa only [loadedInputTable,List.replicate_zero,hseed,seed] using
    chirpBankLoad_holds rg hinj (seedSources globals zero) D 0 (seedSourceValue value zero) S hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
