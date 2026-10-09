import IntegerMultBounds.Machine.RadixDigitMoveBlockPlacement

/-! Complete fixed-radix movement [P][Q][S][E] ↔ [P][S][Q][E].
Only canonical P,S,E and arbitrary payload are supplied. Every generated
product, clock, role tape and tracking tape is physically initialized/cleaned. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveBlockExecution
variable {P Q S E a : ℕ}
noncomputable section
open RadixDigitMoveBlockCounts (seBits psBits)
open RadixDigitMoveBlockPlacement (placement tail)
open RadixDigitMoveBlockRows (move unmove move_unmove)

def bank (source : ℤ → Fin (a+4)) (ps ss es : List Bool) :=
  RadixDigitMoveBlockPlacement.bank (Q := Q) source ps ss es none none

def prepareProgram (Q a : ℕ) := Placement.placed (RadixDigitMoveBlockCounts.program (a := a)) (placement (Q := Q))
def cleanupProgram (Q a : ℕ) := Placement.placed (RadixDigitMoveBlockCounts.cleanupProgram (a := a)) (placement (Q := Q))
def forwardProgram (Q a : ℕ) := seq
  (seq (prepareProgram Q a) (extend (RadixDigitMoveBlockPrepared.program Q a) 4)) (cleanupProgram Q a)
def backwardProgram (Q a : ℕ) := seq
  (seq (prepareProgram Q a) (extend (RadixDigitMoveBlockPrepared.backwardProgram Q a) 4)) (cleanupProgram Q a)
def bound (Q : ℕ) := RadixDigitMoveBlockPrepared.bound Q+185

private theorem prepare_hoare (source : ℤ → Fin (a+4)) (ps ss es : List Bool)
    (P S E : ℕ) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (prepareProgram Q a) (fun v => v = bank (Q := Q) source ps ss es)
      (fun v => v = (RadixDigitMoveBlockPrepared.bank (Q := Q) source (seBits S E) ps es (psBits P S)).append (tail ss))
      (163*(P*S*E)) := by
  have h := RadixDigitMoveBlockPlacement.placed_hoare (Q := Q) source ps ss es none none
    (some (seBits S E)) (some (psBits P S)) (RadixDigitMoveBlockCounts.construct_hoare ps ss es P S E hP hS hE hp hs he cp cs ce)
  simpa only [RadixDigitMoveBlockPlacement.prepared_bank,bank,prepareProgram] using h

private theorem cleanup_hoare (source : ℤ → Fin (a+4)) (ps ss es : List Bool)
    (P S E : ℕ) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E) :
    HoareTime (cleanupProgram Q a)
      (fun v => v = (RadixDigitMoveBlockPrepared.bank (Q := Q) source (seBits S E) ps es (psBits P S)).append (tail ss))
      (fun v => v = bank (Q := Q) source ps ss es) (20*(P*S*E)) := by
  have h := RadixDigitMoveBlockPlacement.placed_hoare (Q := Q) source ps ss es
    (some (seBits S E)) (some (psBits P S)) none none (RadixDigitMoveBlockCounts.cleanup_hoare ps ss es P S E hP hS hE)
  simpa only [RadixDigitMoveBlockPlacement.prepared_bank,bank,cleanupProgram] using h

/-- Forward block-digit move, including descriptor generation and cleanup.
Q fixes the finite machine; P,S,E are read from their canonical input tapes. -/
theorem forward_hoare (source : ℤ → Fin (a+4)) (x : Fin (P*Q*(S*E)) → Fin (a+4))
    (ps ss es : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (forwardProgram Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn x)) ps ss es)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (move x))) ps ss es)
      (bound Q*(P*Q*(S*E))) := by
  have h1 := prepare_hoare (Q := Q) (putWord source 0 (List.ofFn x)) ps ss es P S E hP hS hE hp hs he cp cs ce
  have h2 := hoare_extend_eq (RadixDigitMoveBlockPrepared.forward_hoare source x (seBits S E) ps es (psBits P S)
    hP hQ hS hE (RadixDigitMoveBlockCounts.se_value S E) hp he (RadixDigitMoveBlockCounts.ps_value P S)
    (RadixDigitMoveBlockCounts.se_canonical S E) cp ce (RadixDigitMoveBlockCounts.ps_canonical P S)) (tail ss)
  have h3 := cleanup_hoare (Q := Q) (putWord source 0 (List.ofFn (move x))) ps ss es P S E hP hS hE
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hv : 0 < P*Q*(S*E) := Nat.mul_pos (Nat.mul_pos hP hQ) (Nat.mul_pos hS hE)
  have hpq := Nat.le_mul_of_pos_right P hQ
  have hps := Nat.mul_le_mul_right (S*E) hpq
  unfold bound
  nlinarith

/-- Inverse movement preserves trailing blocks, original descriptors and all
outside-payload symbols, with identical reusable blank workspace. -/
theorem backward_hoare (source : ℤ → Fin (a+4)) (x : Fin (P*Q*(S*E)) → Fin (a+4))
    (ps ss es : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (backwardProgram Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (move x))) ps ss es)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn x)) ps ss es)
      (bound Q*(P*Q*(S*E))) := by
  have h1 := prepare_hoare (Q := Q) (putWord source 0 (List.ofFn (move x))) ps ss es P S E hP hS hE hp hs he cp cs ce
  have h2 := hoare_extend_eq (RadixDigitMoveBlockPrepared.backward_hoare source x (seBits S E) ps es (psBits P S)
    hP hQ hS hE (RadixDigitMoveBlockCounts.se_value S E) hp he (RadixDigitMoveBlockCounts.ps_value P S)
    (RadixDigitMoveBlockCounts.se_canonical S E) cp ce (RadixDigitMoveBlockCounts.ps_canonical P S)) (tail ss)
  have h3 := cleanup_hoare (Q := Q) (putWord source 0 (List.ofFn x)) ps ss es P S E hP hS hE
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hv : 0 < P*Q*(S*E) := Nat.mul_pos (Nat.mul_pos hP hQ) (Nat.mul_pos hS hE)
  have hpq := Nat.le_mul_of_pos_right P hQ
  have hps := Nat.mul_le_mul_right (S*E) hpq
  unfold bound
  nlinarith

/-- The inverse program accepts every arbitrary serialized array in the
post-movement shape, with no supplied forward execution or source preimage. -/
theorem backward_unmove_hoare (source : ℤ → Fin (a+4)) (y : Fin (P*S*Q*E) → Fin (a+4))
    (ps ss es : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (backwardProgram Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn y)) ps ss es)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (unmove y))) ps ss es)
      (bound Q*(P*Q*(S*E))) := by
  simpa only [move_unmove] using backward_hoare source (unmove y) ps ss es
    hP hQ hS hE hp hs he cp cs ce

end
end IntegerMultBounds.Machine.RadixDigitMoveBlockExecution
