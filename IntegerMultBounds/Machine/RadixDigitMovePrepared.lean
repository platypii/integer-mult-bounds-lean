import IntegerMultBounds.Machine.RadixDigitMoveInitialized

/-! Fixed-radix digit movement with four canonical descriptors already present.
The source and every private head return to zero; all scratch is erased. -/
namespace IntegerMultBounds.Machine.RadixDigitMovePrepared
open RadixDigitMoveRows
open RadixDigitMoveCore (count)
variable {P Q S a : ℕ}
noncomputable section

def bank (source : ℤ → Fin (a+4)) (ss ps os ts : List Bool) :=
  (RadixDigitMoveInitialized.bank (Q := Q) source ss ps os ts).append (SharedBank.empty (count Q) a)

def program (Q a : ℕ) := RadixDigitMoveInitialized.program Q a

def bound (Q : ℕ) := (2+5*count Q)*301+11*count Q+4

theorem forward_hoare (source : ℤ → Fin (a+4)) (x : Fin (P*Q*S) → Fin (a+4))
    (ss ps os ts : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S)
    (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (ho : Counter.value os = 1) (ht : Counter.value ts = P*S)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps)
    (co : GrowingCounterData.Canonical os) (ct : GrowingCounterData.Canonical ts) :
    HoareTime (program Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn x)) ss ps os ts)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (move x))) ss ps os ts)
      (bound Q*(P*Q*S)) := by
  have hw : (CyclicRowSplit.sourceWord (splitRows x)).length =
      (CyclicRowSplit.sourceWord (mergeRows x)).length := by
    rw [split_source,merge_source,List.length_ofFn,List.length_ofFn]
    ring
  have h := RadixDigitMoveInitialized.redistribute_hoare source (splitRows x) (mergeRows x)
    S 1 ss ps os ts (split_length x) (merge_length x) hs hp ho ht (role_compatible x) hw
  simp only [split_source,merge_source] at h
  have h1 := CyclicRowSplit.cost_linear S ss ps hQ hP hS hs hp cs cp
  have h2 := CyclicRowSplit.cost_linear 1 os ts hQ (Nat.mul_pos hP hS) (by omega) ho ht co ct
  have hv : 0 < P*Q*S := Nat.mul_pos (Nat.mul_pos hP hQ) hS
  have h1' : P*(7*(Q*S)+Q*(7*ss.length+17))+6*P+7*ps.length+16 ≤ 74*(P*Q*S) := by nlinarith [h1]
  have h2' : (P*S)*(7*(Q*1)+Q*(7*os.length+17))+6*(P*S)+7*ts.length+16 ≤ 74*(P*Q*S) := by nlinarith [h2]
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hi : 2*(P*(7*(Q*S)+Q*(7*ss.length+17))+6*P+7*ps.length+16)+
      2*((P*S)*(7*(Q*1)+Q*(7*os.length+17))+6*(P*S)+7*ts.length+16)+5 ≤ 301*(P*Q*S) := by omega
  have hm := Nat.mul_le_mul_left (2+5*count Q) hi
  unfold bound
  nlinarith

def swap : Equiv.Perm (Fin (count Q+count Q)) :=
  Shared50RecursiveBank.join (RadixDigitMoveCore.swap (Q := Q)) (Equiv.refl _)

def backwardProgram (Q a : ℕ) := reindex (program Q a) (swap (Q := Q))

private theorem swapped (source : ℤ → Fin (a+4)) (ss ps os ts : List Bool) :
    (bank (Q := Q) source os ts ss ps).reindex swap = bank (Q := Q) source ss ps os ts := by
  rw [bank,swap,Shared50RecursiveBank.append_reindex]
  have hb : (RadixDigitMoveInitialized.bank (Q := Q) source os ts ss ps).reindex RadixDigitMoveCore.swap =
      RadixDigitMoveInitialized.bank source ss ps os ts := by
    rw [RadixDigitMoveInitialized.bank,RadixDigitMoveCore.swap,Shared50RecursiveBank.append_reindex]
    have hc : (RadixDigitMoveInitialized.controls (a := a) os ts ss ps).reindex RadixDigitMoveCore.swapControls =
        RadixDigitMoveInitialized.controls ss ps os ts := by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    rw [hc]
    rfl
  rw [hb]
  rfl

theorem backward_hoare (source : ℤ → Fin (a+4)) (x : Fin (P*Q*S) → Fin (a+4))
    (ss ps os ts : List Bool) (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S)
    (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (ho : Counter.value os = 1) (ht : Counter.value ts = P*S)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps)
    (co : GrowingCounterData.Canonical os) (ct : GrowingCounterData.Canonical ts) :
    HoareTime (backwardProgram Q a)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn (move x))) ss ps os ts)
      (fun v => v = bank (Q := Q) (putWord source 0 (List.ofFn x)) ss ps os ts)
      (bound Q*(P*Q*S)) := by
  have hw : (CyclicRowSplit.sourceWord (mergeRows x)).length =
      (CyclicRowSplit.sourceWord (splitRows x)).length := by
    rw [split_source,merge_source,List.length_ofFn,List.length_ofFn]
    ring
  have h0 := RadixDigitMoveInitialized.redistribute_hoare source (mergeRows x) (splitRows x)
    1 S os ts ss ps (merge_length x) (split_length x) ho ht hs hp (fun j => (role_compatible x j).symm) hw
  simp only [split_source,merge_source] at h0
  change HoareTime (program Q a) (fun v => v = bank _ os ts ss ps)
    (fun v => v = bank _ os ts ss ps) _ at h0
  have h := hoare_reindex_eq h0 (swap (Q := Q))
  simp only [swapped] at h
  have h1 := CyclicRowSplit.cost_linear S ss ps hQ hP hS hs hp cs cp
  have h2 := CyclicRowSplit.cost_linear 1 os ts hQ (Nat.mul_pos hP hS) (by omega) ho ht co ct
  have hv : 0 < P*Q*S := Nat.mul_pos (Nat.mul_pos hP hQ) hS
  have h1' : P*(7*(Q*S)+Q*(7*ss.length+17))+6*P+7*ps.length+16 ≤ 74*(P*Q*S) := by nlinarith [h1]
  have h2' : (P*S)*(7*(Q*1)+Q*(7*os.length+17))+6*(P*S)+7*ts.length+16 ≤ 74*(P*Q*S) := by nlinarith [h2]
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hi : 2*((P*S)*(7*(Q*1)+Q*(7*os.length+17))+6*(P*S)+7*ts.length+16)+
      2*(P*(7*(Q*S)+Q*(7*ss.length+17))+6*P+7*ps.length+16)+5 ≤ 301*(P*Q*S) := by omega
  have hm := Nat.mul_le_mul_left (2+5*count Q) hi
  unfold bound
  nlinarith

end
end IntegerMultBounds.Machine.RadixDigitMovePrepared
