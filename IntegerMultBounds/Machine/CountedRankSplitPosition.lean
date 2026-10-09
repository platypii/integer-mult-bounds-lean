import IntegerMultBounds.Machine.CountedRankSplitCopy
import IntegerMultBounds.Machine.CountedPosition

/-! Counted left positioning with paid clock initialization and deletion. -/
namespace IntegerMultBounds.Machine.CountedRankSplitPosition
noncomputable section
variable {a : ℕ}

def bank (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool) :=
  ((CountedPosition.one f p).append (SharedBank.empty 1 a)).append (CountedRankSplitCopy.header bs)
def setup := extend (ArbitraryWidthZeroHeaderShared.program (a := a) (t := 1)) 1
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (1 : Fin 3)
def program := seq (seq (setup (a := a)) (CountedPosition.program .left)) cleanup

private theorem encoded_binary (bs : List Bool) :
    RadixZeroFill.encodedBinary (q := a) bs = CountedLoopReuseAlphabet.binary bs :=
  CountedLoopReuseAlphabet.encoding_binary bs

theorem sets_up (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool) :
    HoareTime (setup (a := a)) (fun w => w = bank f p bs)
      (fun w => w = CountedPosition.bank f p bs) 6 := by
  have h := hoare_extend_eq (ArbitraryWidthZeroHeaderShared.constructs (CountedPosition.one f p))
    (CountedRankSplitCopy.header bs)
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact encoded_binary bs

theorem cleans (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool) :
    HoareTime (cleanup (a := a)) (fun w => w = CountedPosition.bank f p bs)
      (fun w => w = bank f p bs) 4 := by
  have h := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3) (CountedPosition.bank f p bs) [] (by rfl) rfl
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact (encoded_binary bs).symm

/-- Even walks through the blank counter tail are actual paid transitions. -/
theorem moves (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool)
    (n : ℕ) (hv : Counter.value bs = n) :
    HoareTime (program (a := a)) (fun w => w = bank f p bs)
      (fun w => w = bank f (p-n) bs) (7*n+7*bs.length+28) := by
  have h0 := CountedPosition.position_hoare .left f p bs n hv
  simp only [Move.offset,mul_neg_one] at h0
  have h := ((sets_up f p bs).seq h0).seq (cleans f (p-n) bs)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRankSplitPosition
