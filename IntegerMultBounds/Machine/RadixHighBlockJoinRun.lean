import IntegerMultBounds.Machine.RadixHighBlockJoinLoop
import IntegerMultBounds.Machine.RadixHighBlockJoinInitialize
import IntegerMultBounds.Machine.RadixHighBlockJoinCleanup
import IntegerMultBounds.Machine.ArbitraryWidthHighBudget

/-! Sole-header execution of ordered high-block joining, including all
physical setup, actual counted digit movements and private cleanup. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinRun
noncomputable section
open RecursiveChildQuotientsConstant (bits)
variable {q a : ℕ}

def program := seq (seq (RadixHighBlockJoinInitialize.program (q := q) (a := a) false)
  (RadixHighBlockJoinLoop.program (q := q) (a := a)))
  (RadixHighBlockJoinCleanup.program (q := q) (a := a))

def coefficient (q : ℕ) := RadixHighBlockJoinInitialize.coefficient q+
  RadixHighBlockJoinLoop.loopCoefficient q+RadixHighBlockJoinCleanup.coefficient q+2

private theorem canonical_bits (xs : List Bool) (N : ℕ)
    (hx : Counter.value xs = N) (cx : GrowingCounterData.Canonical xs) : xs = bits N :=
  BinaryCanonicalData.value_injective xs (bits N) cx
    (RecursiveChildQuotientsConstant.bits_canonical N)
    (hx.trans (RecursiveChildQuotientsConstant.bits_value N).symm)

private theorem grown_bits (N r : ℕ) : RadixHighBlockJoinSetup.grownBits (q := q) N r = bits (q^r*N) := by
  apply canonical_bits
  · simp only [RadixHighBlockJoinSetup.grownBits,BoundedProductDescriptor.bits_value,Nat.mul_comm]
  · exact BoundedProductDescriptor.bits_canonical _ _

theorem joins (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = RadixHighBlockJoinInitialize.input
        (RadixHighBlockJoinLoop.word source x) ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
      (fun v => v = RadixHighBlockJoinInitialize.input
        (RadixHighBlockJoinLoop.word source (RadixHighBlockJoinSemantics.join q r P S E x)) ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
      (coefficient q*(r+1)*(P*S*q^r*E)) := by
  have hi := RadixHighBlockJoinInitialize.initializes_volume (q := q) false
    (RadixHighBlockJoinLoop.word source x) ss op oe rs CountedLoopReuseAlphabet.empty 1
    P S E r hq hP hS hE hp he cp ce hr cr
  have hprep : RadixHighBlockJoinInitialize.prepared (q := q) false
      (RadixHighBlockJoinLoop.word source x) ss op oe E r
      (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs) =
      CountedLoopReuseAlphabet.bank (RadixHighBlockJoinLoop.firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1 := by
    simp only [RadixHighBlockJoinInitialize.prepared,Bool.false_eq_true,ite_false,
      canonical_bits op P hp cp,grown_bits]
    rfl
  change HoareTime _ _ (fun v => v = RadixHighBlockJoinInitialize.prepared false
    (RadixHighBlockJoinLoop.word source x) ss op oe E r
    (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)) _ at hi
  rw [hprep] at hi
  have hl := RadixHighBlockJoinLoop.loop_hoare (q := q) r P S E source ss op oe rs x hq hP hS hE hs cs hr cr
  have hV : 0 < P*S*q^r*E := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hS)
    (pow_pos (by omega : 0 < q) r)) hE
  have hPV : P*q^r ≤ P*S*q^r*E :=
    (Nat.mul_le_mul_right (q^r) (Nat.le_mul_of_pos_right P hS)).trans
      (Nat.le_mul_of_pos_right (P*S*q^r) hE)
  have hEV : E ≤ P*S*q^r*E := Nat.le_mul_of_pos_left E
    (Nat.mul_pos (Nat.mul_pos hP hS) (pow_pos (by omega : 0 < q) r))
  have hc := RadixHighBlockJoinCleanup.cleans_linear (q := q)
    (RadixHighBlockJoinLoop.word source (RadixHighBlockJoinSemantics.join q r P S E x))
    ss op oe (bits (P*q^r)) (bits E)
    (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)
    (P*S*q^r*E) hV (RecursiveChildQuotientsConstant.bits_canonical _)
    (RecursiveChildQuotientsConstant.bits_canonical _)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hPV)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hEV)
  have h := (hi.seq hl).seq hc
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh)
  have hiCost := Nat.mul_le_mul_right (P*S*q^r*E)
    (Nat.le_mul_of_pos_right (RadixHighBlockJoinInitialize.coefficient q) (by omega : 0 < r+1))
  have hcCost := Nat.mul_le_mul_right (P*S*q^r*E)
    (Nat.le_mul_of_pos_right (RadixHighBlockJoinCleanup.coefficient q) (by omega : 0 < r+1))
  have htwo : 2 ≤ 2*(r+1)*(P*S*q^r*E) := by
    have ht := Nat.mul_pos (by omega : 0 < r+1) hV
    nlinarith
  unfold coefficient
  simp only [Nat.add_mul]
  omega

/-- The complete physical join, including its setup and erasure, keeps every
positive target exponent when using the actual runtime high-digit selector. -/
theorem selected_cost (e V : ℕ) (τ : ℝ) (hq : 2 ≤ q) (he : 0 < e) (hτ : 0 < τ) :
    ((coefficient q*(ArbitraryWidthHighPrepare.highDepth q e+1)*V : ℕ) : ℝ) ≤
      ((coefficient q : ℝ)*ArbitraryWidthHighBudget.constant q τ)*(V : ℝ)*(e : ℝ)^τ := by
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
    ArbitraryWidthHighBudget.movement_bound q e V (coefficient q) τ hq he hτ

end
end IntegerMultBounds.Machine.RadixHighBlockJoinRun
