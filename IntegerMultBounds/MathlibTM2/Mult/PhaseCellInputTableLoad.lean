module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Reuse the restoring padded-word loader to initialize the external input
table from retained fixed-width caller words and a borrowed width counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A n : ℕ} {P U : Type}

def loadedInputTable (rg : TblR n → Fin T) (input : Fin n → Fin T) (D : ℕ)
    (value : Fin T → ℕ) (S : Stacks T A) :=
  {S with R := chirpBankLoadR rg input D 0 value S.R}

theorem inputTableLoadCost_eq (rg : TblR n → Fin T) (input : Fin n → Fin T) (D : ℕ) :
    chirpBankLoadCost rg input D 0 (fun _ => D) = (8*n+4)*D+8*n+9 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,Function.comp_def]
  ring

theorem loadInputTable_exec_within (body : P → Pr P T Q A U)
    (rg : TblR n → Fin T) (hrg : Function.Injective rg) (input : Fin n → Fin T)
    (width zero : Fin T) (hwidth : ∀ r, rg r ≠ width) (hzero : ∀ r, rg r ≠ zero)
    (hinput : ∀ i r, rg r ≠ input i) (D : ℕ) (value : Fin T → ℕ)
    (hfit : ∀ i, value (input i) < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hw : (S.R width).length = D) (hz : S.R zero = [])
    (hsrc : ∀ i, S.R (input i) = binSyms D (value (input i)))
    (hblank : ∀ r, S.R (rg r) = []) (depth : ℕ) :
    let cost := (8*n+4)*D+8*n+9
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+3*cost) depth
        (chirpBankLoad rg input width zero) (Host.mk v S) cost
        (Host.mk v' (loadedInputTable rg input D value S)) ∧
      tblHolds rg (loadedInputTable rg input D value S)
        (tblRho D (List.replicate D tick) [] ⟨fun i => value (input i),[]⟩) := by
  dsimp only
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) rg hrg input width zero hwidth hzero hinput
    D 0 (fun _ => D) value hfit (by intros; exact le_rfl) v S hw (by rw [hz]; rfl) hsrc hblank
  rw [inputTableLoadCost_eq] at he
  refine ⟨v',hu,mn_native_exec_within he 3 (chirpBankLoad_native _ _ _ _) depth _ (by omega),?_⟩
  simpa only [loadedInputTable,List.replicate_zero] using chirpBankLoad_holds rg hrg input D 0 value S hblank

theorem loadedInputTable_off (rg : TblR n → Fin T) (input : Fin n → Fin T) (D : ℕ)
    (value : Fin T → ℕ) (S : Stacks T A) (k : Fin T) (hoff : ∀ r, k ≠ rg r) :
    (loadedInputTable rg input D value S).R k = S.R k := chirpBankLoad_off rg input D 0 value S.R k hoff

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
