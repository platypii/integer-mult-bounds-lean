import IntegerMultBounds.Machine.CountedRepairKeyScan
import IntegerMultBounds.Machine.CountedGuardConstantsFill

/-! Runtime construction of the unary sort width and zero rank counter, using
only original q/b/n headers and blank reusable product workspace. -/
namespace IntegerMultBounds.Machine.CountedRepairScanMetadata
noncomputable section
open CountedRankSplitBank
open CountedRankSplitBank (placed_exact)

def vbPlace : Fin (3+9) ≃ Fin 12 where
  toFun := ![1,8,7,0,2,3,4,5,6,9,10,11]
  invFun := ![3,0,4,5,6,7,8,2,1,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def fillVq := Placement.placed (CountedGuardConstantsFill.fill (a := 1) true) vPlace
def fillVb := Placement.placed (CountedGuardConstantsFill.fill (a := 1) true) vbPlace
def fillCq := Placement.placed (CountedGuardConstantsFill.fill (a := 1) false) ctrQPlace
def fillCb := Placement.placed (CountedGuardConstantsFill.fill (a := 1) false) ctrBPlace
def backVb := Placement.placed (CountedRankSplitPosition.program (a := 1)) vbPlace

theorem fillsVq (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hN : Counter.value qs=N) :
    HoareTime fillVq (fun u => u=bank f g h p v w hs (some qs) (some bs))
      (fun u => u=bank f (putWord g v (List.replicate N (bitSymbol true))) h p (v+N) w hs (some qs) (some bs))
      (7*N+7*qs.length+23) := by
  apply placed_exact vPlace _ _ _ _ _ _ _ (CountedGuardConstantsFill.fills true g v qs N hN)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedGuardGadgetHeaders.binary_eq _ | exact (CountedGuardGadgetHeaders.binary_eq _).symm

theorem fillsVb (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hN : Counter.value bs=N) :
    HoareTime fillVb (fun u => u=bank f g h p v w hs (some qs) (some bs))
      (fun u => u=bank f (putWord g v (List.replicate N (bitSymbol true))) h p (v+N) w hs (some qs) (some bs))
      (7*N+7*bs.length+23) := by
  apply placed_exact vbPlace _ _ _ _ _ _ _ (CountedGuardConstantsFill.fills true g v bs N hN)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedGuardGadgetHeaders.binary_eq _ | exact (CountedGuardGadgetHeaders.binary_eq _).symm

theorem fillsCq (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hN : Counter.value qs=N) :
    HoareTime fillCq (fun u => u=bank f g h p v w hs (some qs) (some bs))
      (fun u => u=bank (putWord f p (List.replicate N (bitSymbol false))) g h (p+N) v w hs (some qs) (some bs))
      (7*N+7*qs.length+23) := by
  apply placed_exact ctrQPlace _ _ _ _ _ _ _ (CountedGuardConstantsFill.fills false f p qs N hN)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedGuardGadgetHeaders.binary_eq _ | exact (CountedGuardGadgetHeaders.binary_eq _).symm

theorem fillsCb (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hN : Counter.value bs=N) :
    HoareTime fillCb (fun u => u=bank f g h p v w hs (some qs) (some bs))
      (fun u => u=bank (putWord f p (List.replicate N (bitSymbol false))) g h (p+N) v w hs (some qs) (some bs))
      (7*N+7*bs.length+23) := by
  apply placed_exact ctrBPlace _ _ _ _ _ _ _ (CountedGuardConstantsFill.fills false f p bs N hN)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedGuardGadgetHeaders.binary_eq _ | exact (CountedGuardGadgetHeaders.binary_eq _).symm

theorem movesVb (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hN : Counter.value bs=N) :
    HoareTime backVb (fun u => u=bank f g h p v w hs (some qs) (some bs))
      (fun u => u=bank f g h p (v-N) w hs (some qs) (some bs)) (7*N+7*bs.length+28) := by
  apply placed_exact vbPlace _ _ _ _ _ _ _ (CountedRankSplitPosition.moves g v bs N hN)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (qProgram (a := 1)) bProgram) fillVq) fillVb) fillCq) fillCb) backV) backVb) backCtrQ) backCtrB) clearQ) clearB

end
end IntegerMultBounds.Machine.CountedRepairScanMetadata
