module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementPlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.RadixHighBlockJoinRunWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.RadixHighBlockSeparateRunWithin
public import IntegerMultBounds.Machine.SharedPlacementWithin

/-! Ordered movement prefix bounds lift through the same physical source-sharing
placement as the endpoint proofs, preserving every complementary tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementPlacementWithin
open IntegerMultBounds.Machine
noncomputable section
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighMovementPlacement
variable {q a t : ℕ}

theorem join_within (v : Tapes t a) (focus : Fin t) (r P S E : ℕ)
    (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4))
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hf : v.tape focus = RadixHighBlockJoinLoop.word source x) (hh : v.head focus = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(RadixHighBlockJoinRunWithin.coefficient q*(P*S*q^r*E) : ℕ) ≤
      (v.append (privateBank (q := q) ss op oe rs)).head j ∧
      (v.append (privateBank (q := q) ss op oe rs)).head j+(RadixHighBlockJoinRunWithin.coefficient q*(P*S*q^r*E) : ℕ) ≤ hi) :
    HoareWithin (joinProgram (q := q) focus)
      (fun w => w = v.append (privateBank (q := q) ss op oe rs))
      (fun w => w = (setTape v focus
        (RadixHighBlockJoinLoop.word source (RadixHighBlockJoinSemantics.join q r P S E x)) 0).append
        (privateBank (q := q) ss op oe rs))
      (RadixHighBlockJoinRun.coefficient q*(r+1)*(P*S*q^r*E)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hsource := hmargin (Fin.castAdd (RadixHighBlockJoinSetup.total q) focus)
  simp only [Tapes.append,Fin.addCases_left,hh] at hsource
  have hlo : lo ≤ -(RadixHighBlockJoinRunWithin.coefficient q*(P*S*q^r*E) : ℕ) := by omega
  have hhi : (RadixHighBlockJoinRunWithin.coefficient q*(P*S*q^r*E) : ℕ) ≤ hi := by omega
  have hrun := (RadixHighBlockJoinRunWithin.joins_within r P S E source ss op oe rs x hq hP hS hE hs cs hp cp he ce hr cr).consequence
    (J := fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi)
    (fun _ h => h) (fun _ h => h) le_rfl (by intro z hz j; have h := hz j; omega)
  have hframe : ∀ j, lo ≤ (v.append (privateBank (q := q) ss op oe rs)).head j ∧
      (v.append (privateBank (q := q) ss op oe rs)).head j ≤ hi := by
    intro j
    have hm := hmargin j
    omega
  have h := SharedPlacementAlphabet.shared_within hrun v focus (sourceSlot (q := q)) (fun _ => blank) 0
    (by exact hf) (by exact hh) (by simpa only [← bank_eq,cleared_source] using hframe)
  simpa only [joinProgram,← bank_eq,bank_tape_source,bank_head_source,cleared_source] using h

theorem separate_within (v : Tapes t a) (focus : Fin t) (r P S E : ℕ)
    (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4))
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hf : v.tape focus = RadixHighBlockJoinLoop.word source x) (hh : v.head focus = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(RadixHighBlockSeparateRunWithin.coefficient q*(P*S*q^r*E) : ℕ) ≤
      (v.append (privateBank (q := q) ss op oe rs)).head j ∧
      (v.append (privateBank (q := q) ss op oe rs)).head j+(RadixHighBlockSeparateRunWithin.coefficient q*(P*S*q^r*E) : ℕ) ≤ hi) :
    HoareWithin (separateProgram (q := q) focus)
      (fun w => w = v.append (privateBank (q := q) ss op oe rs))
      (fun w => w = (setTape v focus
        (RadixHighBlockJoinLoop.word source (RadixDigitMoveBlockRows.move x)) 0).append
        (privateBank (q := q) ss op oe rs))
      (RadixHighBlockSeparateRun.coefficient q*(r+1)*(P*S*q^r*E)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hsource := hmargin (Fin.castAdd (RadixHighBlockJoinSetup.total q) focus)
  simp only [Tapes.append,Fin.addCases_left,hh] at hsource
  have hlo : lo ≤ -(RadixHighBlockSeparateRunWithin.coefficient q*(P*S*q^r*E) : ℕ) := by omega
  have hhi : (RadixHighBlockSeparateRunWithin.coefficient q*(P*S*q^r*E) : ℕ) ≤ hi := by omega
  have hrun := (RadixHighBlockSeparateRunWithin.separates_within r P S E source ss op oe rs x hq hP hS hE hs cs hp cp he ce hr cr).consequence
    (J := fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi)
    (fun _ h => h) (fun _ h => h) le_rfl (by intro z hz j; have h := hz j; omega)
  have hframe : ∀ j, lo ≤ (v.append (privateBank (q := q) ss op oe rs)).head j ∧
      (v.append (privateBank (q := q) ss op oe rs)).head j ≤ hi := by
    intro j
    have hm := hmargin j
    omega
  have h := SharedPlacementAlphabet.shared_within hrun v focus (sourceSlot (q := q)) (fun _ => blank) 0
    (by exact hf) (by exact hh) (by simpa only [← bank_eq,cleared_source] using hframe)
  simpa only [separateProgram,← bank_eq,bank_tape_source,bank_head_source,cleared_source] using h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementPlacementWithin
