import IntegerMultBounds.Machine.RadixDigitMovePlacement

/-! Complete physical fixed-radix digit movement and its inverse. Only canonical
P/S descriptors and the payload are supplied; constant/product construction,
all streaming passes, head restoration and scratch erasure are charged. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveExecution
variable {P Q S a : ℕ}
noncomputable section
open RadixDigitMoveCounts (oneBits productBits)
open RadixDigitMovePlacement (placement)
open RadixDigitMoveRows (move)

def bank (source : ℤ → Fin (a+4)) (ss ps : List Bool) :=
  RadixDigitMovePlacement.bank (Q := Q) source ss ps none none

def prepareProgram (Q a : ℕ) := Placement.placed (RadixDigitMoveCounts.program (a := a)) (placement (Q := Q))
def cleanupProgram (Q a : ℕ) := Placement.placed (RadixDigitMoveCounts.cleanupProgram (a := a)) (placement (Q := Q))
def forwardProgram (Q a : ℕ) := seq
  (seq (prepareProgram Q a) (extend (RadixDigitMovePrepared.program Q a) 3)) (cleanupProgram Q a)
def backwardProgram (Q a : ℕ) := seq
  (seq (prepareProgram Q a) (extend (RadixDigitMovePrepared.backwardProgram Q a) 3)) (cleanupProgram Q a)
def bound (Q : ℕ) := RadixDigitMovePrepared.bound Q+108

private theorem prepare_hoare (source : ℤ → Fin (a+4)) (ss ps : List Bool)
    (P S : ℕ) (hP : 0 < P) (hS : 0 < S) (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (prepareProgram Q a) (fun v => v = bank (Q := Q) source ss ps)
      (fun v => v = (RadixDigitMovePrepared.bank (Q := Q) source ss ps oneBits (productBits P S)).append (SharedBank.empty 3 a))
      (91*(P*S)) := by
  have h := RadixDigitMovePlacement.placed_hoare (Q := Q) source ss ps none none
    (some oneBits) (some (productBits P S)) (RadixDigitMoveCounts.construct_hoare ss ps P S hP hS hs hp cs cp)
  simpa only [RadixDigitMovePlacement.prepared_bank,bank,prepareProgram,cleanupProgram] using h

private theorem cleanup_hoare (source : ℤ → Fin (a+4)) (ss ps : List Bool)
    (P S : ℕ) (hP : 0 < P) (hS : 0 < S) :
    HoareTime (cleanupProgram Q a)
      (fun v => v = (RadixDigitMovePrepared.bank (Q := Q) source ss ps oneBits (productBits P S)).append (SharedBank.empty 3 a))
      (fun v => v = bank (Q := Q) source ss ps) (15*(P*S)) := by
  have h := RadixDigitMovePlacement.placed_hoare (Q := Q) source ss ps
    (some oneBits) (some (productBits P S)) none none (RadixDigitMoveCounts.cleanup_hoare ss ps P S hP hS)
  simpa only [RadixDigitMovePlacement.prepared_bank,bank,prepareProgram,cleanupProgram] using h

/-- The full forward routine is volume-linear for each compile-time fixed Q.
Blank and separator payload symbols are ordinary counted data. -/
theorem forward_hoare (source : ℤ → Fin (a+4)) (x : Fin (P*Q*S) → Fin (a+4))
    (ss ps : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S)
    (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (forwardProgram Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn x)) ss ps)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (move x))) ss ps)
      (bound Q*(P*Q*S)) := by
  have h1 := prepare_hoare (Q := Q) (putWord source 0 (List.ofFn x)) ss ps P S hP hS hs hp cs cp
  have h2 := hoare_extend_eq (RadixDigitMovePrepared.forward_hoare source x ss ps oneBits (productBits P S)
    hP hQ hS hs hp RadixDigitMoveCounts.one_value (RadixDigitMoveCounts.product_value P S)
    cs cp RadixDigitMoveCounts.one_canonical (RadixDigitMoveCounts.product_canonical P S)) (SharedBank.empty 3 a)
  have h3 := cleanup_hoare (Q := Q) (putWord source 0 (List.ofFn (move x))) ss ps P S hP hS
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hv : 0 < P*Q*S := Nat.mul_pos (Nat.mul_pos hP hQ) hS
  have hpq := Nat.le_mul_of_pos_right P hQ
  have hps := Nat.mul_le_mul_right S hpq
  unfold bound
  nlinarith

/-- The full inverse uses the same fixed tape bank and restores all scratch. -/
theorem backward_hoare (source : ℤ → Fin (a+4)) (x : Fin (P*Q*S) → Fin (a+4))
    (ss ps : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S)
    (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (backwardProgram Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (move x))) ss ps)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn x)) ss ps)
      (bound Q*(P*Q*S)) := by
  have h1 := prepare_hoare (Q := Q) (putWord source 0 (List.ofFn (move x))) ss ps P S hP hS hs hp cs cp
  have h2 := hoare_extend_eq (RadixDigitMovePrepared.backward_hoare source x ss ps oneBits (productBits P S)
    hP hQ hS hs hp RadixDigitMoveCounts.one_value (RadixDigitMoveCounts.product_value P S)
    cs cp RadixDigitMoveCounts.one_canonical (RadixDigitMoveCounts.product_canonical P S)) (SharedBank.empty 3 a)
  have h3 := cleanup_hoare (Q := Q) (putWord source 0 (List.ofFn x)) ss ps P S hP hS
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hv : 0 < P*Q*S := Nat.mul_pos (Nat.mul_pos hP hQ) hS
  have hpq := Nat.le_mul_of_pos_right P hQ
  have hps := Nat.mul_le_mul_right S hpq
  unfold bound
  nlinarith

end
end IntegerMultBounds.Machine.RadixDigitMoveExecution
