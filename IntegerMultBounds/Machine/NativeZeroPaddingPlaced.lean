import IntegerMultBounds.Machine.NativeZeroPaddingHeaders
import IntegerMultBounds.Machine.CleanSubbank

/-! Complete counted native row padding from original numeric row/dimension/
polynomial/width headers and one native word. Derived count is physically
constructed, consumed and erased; payload EOF and origin movements are paid. -/
namespace IntegerMultBounds.Machine.NativeZeroPaddingPlaced
noncomputable section
open NativeZeroPaddingHeaders
open CountedLoopReuseAlphabet (one)
open RecursiveChildQuotientsConstant (bits)

def ports : Fin 3 → Fin 7 := ![0,1,4]
def focus : Fin 3 → Fin 44 := ![43,4,9]
theorem ports_injective : Function.Injective ports := by decide
theorem focus_injective : Function.Injective focus := by decide

def common (st : ActiveRepairRankHeadersCommands.State) (xs : List (Fin 6)) :=
  (ActiveRepairRankHeadersCommands.bank st).append (one (NativeZeroPadding.word xs) 0)
def bank (st : ActiveRepairRankHeadersCommands.State) (xs : List (Fin 6)) :=
  (common st xs).append (SharedBank.empty 7 2)

def padProgram := Placement.placed NativeZeroPadding.program
  (CleanSubbank.placement ports focus focus_injective)
def headerProgram (ops : List ButterflyAxisHeadersArithmetic.Op) :=
  extend (extend (ButterflyAxisHeadersArithmetic.compile (a:=2) ops).2 1) 7
def program := seq (seq (headerProgram schedule) padProgram) (headerProgram cleanup)

theorem payload (rows padded D ell width : ℕ) (xs : List (Fin 6)) :
    SharedBank.payload (NativeZeroStream.bank (NativeZeroPadding.word xs) 0 (bits width) (bits (count rows padded D ell))) ports=
      SharedBank.payload (common (output rows padded D ell width) xs) focus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clean (f : ℤ → Fin 6) (width count : List Bool) :
    SharedBank.strip (NativeZeroStream.bank f 0 width count) ports=SharedBank.empty 7 2 := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simp only [hi,ite_false]
      fin_cases i
      all_goals first | rfl | exact (hi ⟨0,rfl⟩).elim | exact (hi ⟨1,rfl⟩).elim | exact (hi ⟨2,rfl⟩).elim
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simp only [hi,ite_false]
      fin_cases i
      all_goals first | rfl | exact (hi ⟨0,rfl⟩).elim | exact (hi ⟨1,rfl⟩).elim | exact (hi ⟨2,rfl⟩).elim

theorem frame (st : ActiveRepairRankHeadersCommands.State) (xs ys : List (Fin 6)) :
    SharedBank.strip (common st xs) focus=SharedBank.strip (common st ys) focus := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    by_cases hi : ∃ j,focus j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      fin_cases i
      all_goals first | rfl | exact (hi ⟨0,rfl⟩).elim

theorem pad_runs (rows padded D ell width : ℕ) (xs : List (Fin 6)) (hn : ∀ x∈xs,x≠blank) :
    HoareTime padProgram
      (fun v => v=bank (output rows padded D ell width) xs)
      (fun v => v=bank (output rows padded D ell width)
        (xs++NativeZeroStream.records width (count rows padded D ell)))
      (NativeZeroPadding.cost xs (bits width) (bits (count rows padded D ell)) width (count rows padded D ell)) := by
  have hh := NativeZeroPadding.runs xs hn (bits width) (bits (count rows padded D ell)) width (count rows padded D ell)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
  apply CleanSubbank.realizes (c:=3) (s:=7) (k:=44) NativeZeroPadding.program ports focus ports_injective focus_injective
    (common (output rows padded D ell width) xs)
    (common (output rows padded D ell width) (xs++NativeZeroStream.records width (count rows padded D ell))) _ _ _
    ?_ ?_ ?_ ?_ ?_ hh
  · exact payload rows padded D ell width xs
  · exact payload rows padded D ell width _
  · exact clean _ _ _
  · exact clean _ _ _
  · exact frame _ _ _

def cost (rows padded D ell width : ℕ) (xs : List (Fin 6)) :=
  ButterflyAxisHeadersArithmetic.scheduleCost schedule (initial rows padded D ell width)+
  NativeZeroPadding.cost xs (bits width) (bits (count rows padded D ell)) width (count rows padded D ell)+
  ButterflyAxisHeadersArithmetic.scheduleCost cleanup (output rows padded D ell width)+2

theorem runs (rows padded D ell width : ℕ) (hpad : rows≤padded) (xs : List (Fin 6)) (hn : ∀ x∈xs,x≠blank) :
    HoareTime program (fun v => v=bank (initial rows padded D ell width) xs)
      (fun v => v=bank (initial rows padded D ell width)
        (xs++NativeZeroStream.records width (count rows padded D ell)))
      (cost rows padded D ell width xs) := by
  have h0 := hoare_extend_eq (hoare_extend_eq (NativeZeroPaddingHeaders.runs rows padded D ell width hpad)
    (one (NativeZeroPadding.word xs) 0)) (SharedBank.empty 7 2)
  have h1 := pad_runs rows padded D ell width xs hn
  have h2 := hoare_extend_eq (hoare_extend_eq (NativeZeroPaddingHeaders.cleanup_runs rows padded D ell width)
    (one (NativeZeroPadding.word (xs++NativeZeroStream.records width (count rows padded D ell))) 0)) (SharedBank.empty 7 2)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.NativeZeroPaddingPlaced
