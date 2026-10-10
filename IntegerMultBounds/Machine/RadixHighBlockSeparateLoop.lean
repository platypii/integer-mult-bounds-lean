import IntegerMultBounds.Machine.RadixHighBlockJoinLoop
import IntegerMultBounds.Machine.RadixHighBlockSeparateSemantics

/-! Actual inverse ordered high-block separation by a paid counted loop.
Every body removes the trailing prefix digit and restores it after S. -/
namespace IntegerMultBounds.Machine.RadixHighBlockSeparateLoop
noncomputable section
open RadixHighBlockJoinBank
open RadixHighBlockJoinBody
open RadixHighBlockSeparateSemantics (separate)
open RecursiveChildQuotientsConstant (bits)
open RadixHighBlockJoinLoop (word word_reindex ofFn_reindex)
variable {q a : ℕ}

def firstBank (P S E r : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) :=
  bank (q := q) (word source x) ss op oe (some (bits (P*q^r))) (some (bits E)) (some (bits q))
def finalBank (P S E r : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) :=
  bank (q := q) (word source x) ss op oe (some (bits P)) (some (bits (q^r*E))) (some (bits q))

private theorem input_succ (P S q r E : ℕ) : (P*q^r)*q*(S*E) = P*q^(r+1)*(S*E) := by rw [pow_succ]; ring
private theorem middle_succ (P S q r E : ℕ) : P*q^r*(S*(q*E)) = (P*q^r)*S*q*E := by ring
private theorem output_succ (P S q r E : ℕ) : P*S*q^(r+1)*E = P*S*q^r*(q*E) := by rw [pow_succ]; ring

def nextArray (P S E r : ℕ) (x : Fin (P*q^(r+1)*(S*E)) → Fin (a+4)) :
    Fin (P*q^r*(S*(q*E))) → Fin (a+4) := RadixHighBlockJoinSemantics.reindex (middle_succ P S q r E)
      (RadixDigitMoveBlockRows.move (RadixHighBlockJoinSemantics.reindex (input_succ P S q r E) x))

def trace : (r P S E : ℕ) → (source : ℤ → Fin (a+4)) → (ss op oe : List Bool) →
    (Fin (P*q^r*(S*E)) → Fin (a+4)) → List (Tapes (count q) a)
  | 0,P,S,E,source,ss,op,oe,x => [firstBank P S E 0 source ss op oe x]
  | r+1,P,S,E,source,ss,op,oe,x => firstBank P S E (r+1) source ss op oe x ::
      trace r P S (q*E) source ss op oe (nextArray P S E r x)

def defaultBank : Tapes (count q) a := SharedBank.empty (count q) a

theorem trace_head (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) :
    (trace r P S E source ss op oe x).getD 0 defaultBank = firstBank P S E r source ss op oe x := by cases r <;> rfl

private theorem first_step (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^(r+1)*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss) :
    HoareTime (separateProgram (q := q) (a := a))
      (fun v => v = firstBank P S E (r+1) source ss op oe x)
      (fun v => v = firstBank P S (q*E) r source ss op oe (nextArray P S E r x))
      (coefficient q*(P*S*q^(r+1)*E)) := by
  have h := separate_hoare source (P*q^r) S E (RadixHighBlockJoinSemantics.reindex (input_succ P S q r E) x)
    ss op oe (bits (P*q^(r+1))) (bits E) (bits q) hq
    (Nat.mul_pos hP (pow_pos (by omega : 0 < q) r)) hS hE
    (by rw [RecursiveChildQuotientsConstant.bits_value,pow_succ]; ring) hs (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _) cs
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
  have hb : DimensionProductDescriptor.bits E q = bits (q*E) := by
    rw [RecursiveChildQuotientsConstant.bits_eq_advance]
    unfold DimensionProductDescriptor.bits
    rw [Nat.mul_comm E q]
  rw [hb] at h
  have hv : (P*q^r)*q*(S*E) = P*S*q^(r+1)*E := by rw [pow_succ]; ring
  have h' := h.consequence (b' := coefficient q*(P*S*q^(r+1)*E)) (fun _ hh => hh) (fun _ hh => hh) (by rw [hv])
  simpa only [firstBank,word,nextArray,ofFn_reindex] using h'

theorem trace_steps (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss) :
    ∀ i < r, HoareTime (separateProgram (q := q) (a := a))
      (fun v => v = (trace r P S E source ss op oe x).getD i defaultBank)
      (fun v => v = (trace r P S E source ss op oe x).getD (i+1) defaultBank)
      (coefficient q*(P*S*q^r*E)) := by
  induction r generalizing E with
  | zero => intro i hi; omega
  | succ r ih =>
    intro i hi
    cases i with
    | zero =>
      simpa only [trace,List.getD_cons_zero,List.getD_cons_succ,trace_head] using
        first_step r P S E source ss op oe x hq hP hS hE hs cs
    | succ i =>
      have h := ih (q*E) (nextArray P S E r x) (Nat.mul_pos (by omega) hE) i (by omega)
      have hv : P*S*q^r*(q*E) = P*S*q^(r+1)*E := by rw [pow_succ]; ring
      simpa only [trace,List.getD_cons_succ,hv,Nat.succ_eq_add_one] using h

theorem trace_final (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) :
    (trace r P S E source ss op oe x).getD r defaultBank = finalBank P S E r source ss op oe (separate q r P S E x) := by
  induction r generalizing E with
  | zero => simp only [trace,List.getD_cons_zero,firstBank,finalBank,separate,pow_zero,mul_one,one_mul,word_reindex]
  | succ r ih =>
    rw [trace,List.getD_cons_succ,ih]
    unfold finalBank
    have hv : q^r*(q*E) = q^(r+1)*E := by rw [pow_succ]; ring
    have hbits := congrArg bits hv
    rw [hbits]
    have hj : separate q (r+1) P S E x = RadixHighBlockJoinSemantics.reindex (output_succ P S q r E)
        (separate q r P S (q*E) (nextArray P S E r x)) := rfl
    rw [hj,word_reindex]

def program := CountedLoopReuseAlphabet.program (separateProgram (q := q) (a := a))
def loopCoefficient (q : ℕ) := coefficient q+30

theorem loop_hoare (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = CountedLoopReuseAlphabet.bank (firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (finalBank P S E r source ss op oe (separate q r P S E x))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (loopCoefficient q*(r+1)*(P*S*q^r*E)) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (separateProgram (q := q) (a := a)) rs r
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

/-- The terminal payload is precisely the complete block inverse. -/
theorem loop_move_hoare (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = CountedLoopReuseAlphabet.bank (firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (finalBank P S E r source ss op oe (RadixDigitMoveBlockRows.move x))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (loopCoefficient q*(r+1)*(P*S*q^r*E)) := by
  simpa only [RadixHighBlockSeparateSemantics.separate_eq_move] using
    loop_hoare r P S E source ss op oe rs x hq hP hS hE hs cs hr cr

end
end IntegerMultBounds.Machine.RadixHighBlockSeparateLoop
