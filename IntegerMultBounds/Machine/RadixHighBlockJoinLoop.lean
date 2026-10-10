import IntegerMultBounds.Machine.RadixHighBlockJoinBody
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! An actual counted loop executes every ordered high-digit join. Its exact
state arrays are computed from the literal single-digit movement, not supplied
execution callbacks. Runtime work is bounded by the original payload volume. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinLoop
noncomputable section
open RadixHighBlockJoinBank
open RadixHighBlockJoinBody
open RadixHighBlockJoinSemantics (join)
open RecursiveChildQuotientsConstant (bits)
variable {q a : ℕ}

def word {n : ℕ} (source : ℤ → Fin (a+4)) (x : Fin n → Fin (a+4)) :=
  putWord source 0 (List.ofFn x)

theorem word_reindex {n m : ℕ} (h : n=m) (source : ℤ → Fin (a+4)) (x : Fin m → Fin (a+4)) :
    word source (RadixHighBlockJoinSemantics.reindex h x) = word source x := by subst m; rfl

theorem ofFn_reindex {α : Type*} {n m : ℕ} (h : n=m) (x : Fin m → α) :
    List.ofFn (RadixHighBlockJoinSemantics.reindex h x) = List.ofFn x := by subst m; rfl

def firstBank (P S E r : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) :=
  bank (q := q) (word source x) ss op oe (some (bits P)) (some (bits (q^r*E))) (some (bits q))

def finalBank (P S E r : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) :=
  bank (q := q) (word source x) ss op oe (some (bits (P*q^r))) (some (bits E)) (some (bits q))

private theorem input_succ (P S q r E : ℕ) : P*S*q*(q^r*E) = P*S*q^(r+1)*E := by rw [pow_succ]; ring
private theorem middle_succ (P S q r E : ℕ) : (P*q)*S*q^r*E = P*q*(S*(q^r*E)) := by ring
private theorem output_succ (P S q r E : ℕ) : P*q^(r+1)*(S*E) = (P*q)*q^r*(S*E) := by rw [pow_succ]; ring

def nextArray (P S E r : ℕ) (x : Fin (P*S*q^(r+1)*E) → Fin (a+4)) :
    Fin ((P*q)*S*q^r*E) → Fin (a+4) := RadixHighBlockJoinSemantics.reindex (middle_succ P S q r E)
      (RadixDigitMoveBlockRows.unmove (RadixHighBlockJoinSemantics.reindex (input_succ P S q r E) x))

/-- A definitional list of exact physical iteration boundaries. -/
def trace : (r P S E : ℕ) → (source : ℤ → Fin (a+4)) → (ss op oe : List Bool) →
    (Fin (P*S*q^r*E) → Fin (a+4)) → List (Tapes (count q) a)
  | 0,P,S,E,source,ss,op,oe,x => [firstBank P S E 0 source ss op oe x]
  | r+1,P,S,E,source,ss,op,oe,x => firstBank P S E (r+1) source ss op oe x ::
      trace r (P*q) S E source ss op oe (nextArray P S E r x)

def defaultBank : Tapes (count q) a := SharedBank.empty (count q) a

theorem trace_head (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) :
    (trace r P S E source ss op oe x).getD 0 defaultBank = firstBank P S E r source ss op oe x := by cases r <;> rfl

private theorem first_step (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^(r+1)*E) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss) :
    HoareTime (joinProgram (q := q) (a := a))
      (fun v => v = firstBank P S E (r+1) source ss op oe x)
      (fun v => v = firstBank (P*q) S E r source ss op oe (nextArray P S E r x))
      (coefficient q*(P*S*q^(r+1)*E)) := by
  have h := join_hoare source P S (q^r*E) (RadixHighBlockJoinSemantics.reindex (input_succ P S q r E) x)
    ss op oe (bits P) (bits (q^(r+1)*E)) (bits q) hq hP hS
    (Nat.mul_pos (pow_pos (by omega : 0 < q) r) hE) (RecursiveChildQuotientsConstant.bits_value _) hs
    (by rw [RecursiveChildQuotientsConstant.bits_value,pow_succ]; ring) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) cs (RecursiveChildQuotientsConstant.bits_canonical _)
    (RecursiveChildQuotientsConstant.bits_canonical _)
  have hb : DimensionProductDescriptor.bits P q = bits (P*q) := by
    rw [RecursiveChildQuotientsConstant.bits_eq_advance]
    rfl
  rw [hb] at h
  have hv : P*q*(S*(q^r*E)) = P*S*q^(r+1)*E := by rw [pow_succ]; ring
  have h' := h.consequence (b' := coefficient q*(P*S*q^(r+1)*E)) (fun _ hh => hh) (fun _ hh => hh) (by rw [hv])
  simpa only [firstBank,word,nextArray,ofFn_reindex] using h'

theorem trace_steps (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss) :
    ∀ i < r, HoareTime (joinProgram (q := q) (a := a))
      (fun v => v = (trace r P S E source ss op oe x).getD i defaultBank)
      (fun v => v = (trace r P S E source ss op oe x).getD (i+1) defaultBank)
      (coefficient q*(P*S*q^r*E)) := by
  induction r generalizing P with
  | zero => intro i hi; omega
  | succ r ih =>
    intro i hi
    cases i with
    | zero =>
      simpa only [trace,List.getD_cons_zero,List.getD_cons_succ,trace_head] using
        first_step r P S E source ss op oe x hq hP hS hE hs cs
    | succ i =>
      have h := ih (P*q) (nextArray P S E r x) (Nat.mul_pos hP (by omega)) i (by omega)
      have hv : (P*q)*S*q^r*E = P*S*q^(r+1)*E := by rw [pow_succ]; ring
      simpa only [trace,List.getD_cons_succ,hv,Nat.succ_eq_add_one] using h

theorem trace_final (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) :
    (trace r P S E source ss op oe x).getD r defaultBank = finalBank P S E r source ss op oe (join q r P S E x) := by
  induction r generalizing P with
  | zero => simp only [trace,List.getD_cons_zero,firstBank,finalBank,join,pow_zero,mul_one,one_mul,word_reindex]
  | succ r ih =>
    rw [trace,List.getD_cons_succ,ih]
    unfold finalBank
    have hv : (P*q)*q^r = P*q^(r+1) := by rw [pow_succ]; ring
    have hbits := congrArg bits hv
    rw [hbits]
    have hj : join q (r+1) P S E x = RadixHighBlockJoinSemantics.reindex (output_succ P S q r E)
        (join q r (P*q) S E (nextArray P S E r x)) := rfl
    rw [hj,word_reindex]

def program := CountedLoopReuseAlphabet.program (joinProgram (q := q) (a := a))
def loopCoefficient (q : ℕ) := coefficient q+30

/-- Every join is a real iteration of one fixed body, with physical outer-clock
preparation and cleanup. The only inputs are canonical shape/count headers;
all body arithmetic counts are derived during the actual iterations. -/
theorem loop_hoare (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = CountedLoopReuseAlphabet.bank (firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (finalBank P S E r source ss op oe (join q r P S E x))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (loopCoefficient q*(r+1)*(P*S*q^r*E)) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (joinProgram (q := q) (a := a)) rs r
    (fun i => (trace r P S E source ss op oe x).getD i defaultBank)
    (fun _ => coefficient q*(P*S*q^r*E)) hr (trace_steps r P S E source ss op oe x hq hP hS hE hs cs)
  rw [trace_head,trace_final] at h
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hV : 0 < P*S*q^r*E := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hS) (pow_pos (by omega : 0 < q) r)) hE
  have hw := GrowingCounterData.canonical_width rs cr
  rw [hr] at hw
  have hl := Nat.log2_le_self r
  unfold loopCoefficient
  nlinarith

end
end IntegerMultBounds.Machine.RadixHighBlockJoinLoop
