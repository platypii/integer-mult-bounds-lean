import IntegerMultBounds.Machine.RadixHighBlockSeparateLoop
import IntegerMultBounds.Machine.RadixHighBlockJoinInitialize
import IntegerMultBounds.Machine.RadixHighBlockJoinCleanup
import IntegerMultBounds.Machine.ArbitraryWidthHighBudget

/-! Sole-header execution of inverse ordered high-block separation. All
working descriptors are physically constructed, the actual counted inverse
loop moves the block, and every private descriptor is physically erased. -/
namespace IntegerMultBounds.Machine.RadixHighBlockSeparateRun
noncomputable section
open RecursiveChildQuotientsConstant (bits)
variable {q a : ℕ}

def program := seq (seq (RadixHighBlockJoinInitialize.program (q := q) (a := a) true)
  (RadixHighBlockSeparateLoop.program (q := q) (a := a)))
  (RadixHighBlockJoinCleanup.program (q := q) (a := a))

def coefficient (q : ℕ) := RadixHighBlockJoinInitialize.coefficient q+
  RadixHighBlockSeparateLoop.loopCoefficient q+RadixHighBlockJoinCleanup.coefficient q+2

private theorem canonical_bits (xs : List Bool) (N : ℕ)
    (hx : Counter.value xs = N) (cx : GrowingCounterData.Canonical xs) : xs = bits N :=
  BinaryCanonicalData.value_injective xs (bits N) cx
    (RecursiveChildQuotientsConstant.bits_canonical N)
    (hx.trans (RecursiveChildQuotientsConstant.bits_value N).symm)

private theorem grown_bits (N r : ℕ) : RadixHighBlockJoinSetup.grownBits (q := q) N r = bits (N*q^r) := by
  apply canonical_bits
  · exact BoundedProductDescriptor.bits_value _ _
  · exact BoundedProductDescriptor.bits_canonical _ _

/-- The complete physical inverse restores the [P][S][q^rho][E] order,
preserving arbitrary payload symbols, original headers, and the loop controls. -/
theorem separates (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = RadixHighBlockJoinInitialize.input
        (RadixHighBlockJoinLoop.word source x) ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
      (fun v => v = RadixHighBlockJoinInitialize.input
        (RadixHighBlockJoinLoop.word source (RadixDigitMoveBlockRows.move x)) ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
      (coefficient q*(r+1)*(P*S*q^r*E)) := by
  have hi := RadixHighBlockJoinInitialize.initializes_volume (q := q) true
    (RadixHighBlockJoinLoop.word source x) ss op oe rs CountedLoopReuseAlphabet.empty 1
    P S E r hq hP hS hE hp he cp ce hr cr
  have hprep : RadixHighBlockJoinInitialize.prepared (q := q) true
      (RadixHighBlockJoinLoop.word source x) ss op oe P r
      (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs) =
      CountedLoopReuseAlphabet.bank (RadixHighBlockSeparateLoop.firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1 := by
    simp only [RadixHighBlockJoinInitialize.prepared,ite_true,
      canonical_bits oe E he ce,grown_bits]
    rfl
  change HoareTime _ _ (fun v => v = RadixHighBlockJoinInitialize.prepared true
    (RadixHighBlockJoinLoop.word source x) ss op oe P r
    (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)) _ at hi
  rw [hprep] at hi
  have hl := RadixHighBlockSeparateLoop.loop_hoare (q := q) r P S E source ss op oe rs x hq hP hS hE hs cs hr cr
  rw [RadixHighBlockSeparateSemantics.separate_eq_move] at hl
  have hpow : 0 < q^r := pow_pos (by omega : 0 < q) r
  have hV : 0 < P*S*q^r*E := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hS) hpow) hE
  have hPV : P ≤ P*S*q^r*E := (Nat.le_mul_of_pos_right P hS).trans
    ((Nat.le_mul_of_pos_right (P*S) hpow).trans (Nat.le_mul_of_pos_right (P*S*q^r) hE))
  have hEV : q^r*E ≤ P*S*q^r*E :=
    Nat.mul_le_mul_right E (Nat.le_mul_of_pos_left (q^r) (Nat.mul_pos hP hS))
  have hc := RadixHighBlockJoinCleanup.cleans_linear (q := q)
    (RadixHighBlockJoinLoop.word source (RadixDigitMoveBlockRows.move x))
    ss op oe (bits P) (bits (q^r*E))
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

/-- The selector-derived repetition count costs no positive width exponent,
including all inverse setup, loop control, and cleanup transitions. -/
theorem selected_cost (e V : ℕ) (τ : ℝ) (hq : 2 ≤ q) (he : 0 < e) (hτ : 0 < τ) :
    ((coefficient q*(ArbitraryWidthHighPrepare.highDepth q e+1)*V : ℕ) : ℝ) ≤
      ((coefficient q : ℝ)*ArbitraryWidthHighBudget.constant q τ)*(V : ℝ)*(e : ℝ)^τ := by
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
    ArbitraryWidthHighBudget.movement_bound q e V (coefficient q) τ hq he hτ

end
end IntegerMultBounds.Machine.RadixHighBlockSeparateRun
