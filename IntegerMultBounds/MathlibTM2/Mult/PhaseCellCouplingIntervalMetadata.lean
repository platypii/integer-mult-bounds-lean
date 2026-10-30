module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBinaryRecoveryGuardInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskBankLoad

/-! One physical geometry bank supplies both interval guards and ribbon masks.
The two consumers retain their own register placements, but cannot disagree on
ambient dimensions, cuts, local origin or local length. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def couplingIntervalValue (s t band a b origin N : ℕ) (k : Fin 168) : ℕ :=
  if k = 145 then s else if k = 146 then t else if k = 147 then band else
  if k = 148 then 2*band else if k = 149 then a else if k = 151 then b else
  if k = 155 then origin else if k = 156 then origin+N else
  if k = 164 then origin+(N+2*band) else if k = 165 then N else 0

def couplingIntervalPorts : List (Fin 168) := [145,146,147,148,149,151,154,155,156,164,165]

structure CouplingIntervalMetadata {A : ℕ} (V s t band a b origin N : ℕ) (S : Stacks 168 A) : Prop where
  width : (S.R 163).length = V
  encoded : ∀ k ∈ couplingIntervalPorts,
    S.R k = binSyms V (couplingIntervalValue s t band a b origin N k)


/-- Transport the geometry bank through an execution that preserves its ports. -/
theorem CouplingIntervalMetadata.of_frame {A V s t band a b origin N : ℕ}
    {S F : Stacks 168 A} (h : CouplingIntervalMetadata V s t band a b origin N S)
    (hwidth : F.R 163 = S.R 163)
    (hframe : ∀ k ∈ couplingIntervalPorts, F.R k = S.R k) :
    CouplingIntervalMetadata V s t band a b origin N F := by
  constructor
  · rw [hwidth]; exact h.width
  · intro k hk
    rw [hframe k hk]
    exact h.encoded k hk

variable {A V s t band a b origin N : ℕ} {S : Stacks 168 A}

theorem couplingIntervalValue_bound (hfit : origin+N ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hst : s < t) (hfitV : origin+(N+2*band)+s < 2^V) (htV : t < 2^V) (k : Fin 168) :
    couplingIntervalValue s t band a b origin N k < 2^V := by
  simp only [couplingIntervalValue]
  split_ifs <;> omega

theorem CouplingIntervalMetadata.guard (h : CouplingIntervalMetadata V s t band a b origin N S)
    (i : Fin 17) :
    (embStk intervalGuardPlacement S).R (intervalGuardBankSource i) =
      binSyms V (couplingIntervalValue s t band a b origin N
        (intervalGuardPlacement (intervalGuardBankSource i))) := by
  apply h.encoded
  simp only [intervalGuardBankSource]
  split_ifs <;> decide

theorem CouplingIntervalMetadata.ribbon (h : CouplingIntervalMetadata V s t band a b origin N S)
    (i : Fin 18) : S.R (ribbonMaskBankSource i) =
      binSyms V (couplingIntervalValue s t band a b origin N (ribbonMaskBankSource i)) := by
  apply h.encoded
  simp only [ribbonMaskBankSource]
  split_ifs <;> decide

theorem CouplingIntervalMetadata.count (h : CouplingIntervalMetadata V s t band a b origin N S) :
    S.R 165 = binSyms V N := by
  simpa [couplingIntervalValue] using h.encoded 165 (by simp [couplingIntervalPorts])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
