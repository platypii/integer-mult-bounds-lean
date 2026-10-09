import IntegerMultBounds.Machine.RadixHighBlockJoinRun
import IntegerMultBounds.Machine.RadixHighBlockSeparateRun
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Concrete shared-source placement of the actual high-block join/separate
machines. All other caller tapes and heads are literally framed; the private
source remains blank and the original private header bank is restored. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighMovementPlacement
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {q a t : ℕ}

def sourceSlot : Fin (RadixHighBlockJoinSetup.total q) :=
  Fin.castAdd 2 ⟨0,by unfold RadixHighBlockJoinBank.count RadixDigitMoveCore.count; omega⟩

def bank (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :=
  RadixHighBlockJoinInitialize.input (q := q) source ss op oe
    (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)

def privateBank (ss op oe rs : List Bool) := bank (q := q) (a := a) (fun _ => blank) ss op oe rs

theorem bank_eq (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :
    bank (q := q) source ss op oe rs =
      RadixHighBlockJoinInitialize.input source ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs) := rfl

theorem bank_head_source (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :
    (bank (q := q) source ss op oe rs).head sourceSlot = 0 := rfl

theorem bank_tape_source (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :
    (bank (q := q) source ss op oe rs).tape sourceSlot = source := rfl

/-- Replacing the physically shared source changes no private descriptor,
clock, workspace tape or head. -/
theorem bank_source (source target : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :
    setTape (bank (q := q) source ss op oe rs) sourceSlot target 0 = bank target ss op oe rs := by
  unfold bank RadixHighBlockJoinInitialize.input RadixHighBlockJoinSetup.bank
  unfold sourceSlot RadixHighBlockJoinSetup.total
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun v : Tapes (RadixHighBlockJoinBank.count q) a => v.append
    (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val=0
    all_goals simp [Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi]
  · funext i
    by_cases hi : i.val=0
    all_goals simp [Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi]

theorem cleared_source (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :
    setTape (bank (q := q) source ss op oe rs) sourceSlot (fun _ => blank) 0 = privateBank ss op oe rs :=
  bank_source _ _ _ _ _ _

def joinProgram (focus : Fin t) := Placement.placed (RadixHighBlockJoinRun.program (q := q) (a := a))
  (SharedPlacementAlphabet.sharedPlacement focus (sourceSlot (q := q)))
def separateProgram (focus : Fin t) := Placement.placed (RadixHighBlockSeparateRun.program (q := q) (a := a))
  (SharedPlacementAlphabet.sharedPlacement focus (sourceSlot (q := q)))

/-- The actual complete join runs on the caller's source tape. Its unused
private source is wholly blank/head zero at both endpoints; every other
caller tape/head and every original private header is preserved exactly. -/
theorem join_hoare (v : Tapes t a) (focus : Fin t) (r P S E : ℕ)
    (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4))
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hf : v.tape focus = RadixHighBlockJoinLoop.word source x) (hh : v.head focus = 0) :
    HoareTime (joinProgram (q := q) focus)
      (fun w => w = v.append (privateBank ss op oe rs))
      (fun w => w = (setTape v focus
        (RadixHighBlockJoinLoop.word source (RadixHighBlockJoinSemantics.join q r P S E x)) 0).append
        (privateBank ss op oe rs))
      (RadixHighBlockJoinRun.coefficient q*(r+1)*(P*S*q^r*E)) := by
  have hrun := RadixHighBlockJoinRun.joins r P S E source ss op oe rs x hq hP hS hE hs cs hp cp he ce hr cr
  have h := SharedPlacementAlphabet.shared_hoare hrun v focus (sourceSlot (q := q)) (fun _ => blank) 0
    (by exact hf) (by exact hh)
  simpa only [joinProgram,← bank_eq,bank_tape_source,bank_head_source,cleared_source] using h

/-- The complete inverse separator is likewise an actual shared-source
program; its literal whole-block movement and all cleanup are paid internally. -/
theorem separate_hoare (v : Tapes t a) (focus : Fin t) (r P S E : ℕ)
    (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4))
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hf : v.tape focus = RadixHighBlockJoinLoop.word source x) (hh : v.head focus = 0) :
    HoareTime (separateProgram (q := q) focus)
      (fun w => w = v.append (privateBank ss op oe rs))
      (fun w => w = (setTape v focus
        (RadixHighBlockJoinLoop.word source (RadixDigitMoveBlockRows.move x)) 0).append
        (privateBank ss op oe rs))
      (RadixHighBlockSeparateRun.coefficient q*(r+1)*(P*S*q^r*E)) := by
  have hrun := RadixHighBlockSeparateRun.separates r P S E source ss op oe rs x hq hP hS hE hs cs hp cp he ce hr cr
  have h := SharedPlacementAlphabet.shared_hoare hrun v focus (sourceSlot (q := q)) (fun _ => blank) 0
    (by exact hf) (by exact hh)
  simpa only [separateProgram,← bank_eq,bank_tape_source,bank_head_source,cleared_source] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthHighMovementPlacement
