import IntegerMultBounds.Machine.RadixHighBlockJoinArithmetic
import IntegerMultBounds.Machine.RadixHighBlockJoinSemantics

/-! Actual high-digit join/separate iteration. Each body performs paid exact
quotient, a complete physical block-digit move, then paid prefix/suffix growth. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinBody
noncomputable section
open RadixHighBlockJoinBank
open RadixHighBlockJoinArithmetic
open RadixDigitMoveBlockRows (move unmove)
open RecursiveChildQuotientsConstant (bits)
variable {q a : ℕ}

def joinProgram := seq (seq (shrinkProgram (q := q) (a := a) false)
  (extend (RadixDigitMoveBlockExecution.backwardProgram q a) 16)) (growProgram true)
def separateProgram := seq (seq (shrinkProgram (q := q) (a := a) true)
  (extend (RadixDigitMoveBlockExecution.forwardProgram q a) 16)) (growProgram false)
def coefficient (q : ℕ) := 2*FixedBaseDescriptorQuotient.constant q+RadixDigitMoveBlockExecution.bound q+112

private theorem backward_hoare (source : ℤ → Fin (a+4)) (P S E : ℕ)
    (y : Fin (P*S*q*E) → Fin (a+4)) (ss op oe ps es ws : List Bool)
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (extend (RadixDigitMoveBlockExecution.backwardProgram q a) 16)
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn y)) ss op oe (some ps) (some es) (some ws))
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn (unmove y))) ss op oe (some ps) (some es) (some ws))
      (RadixDigitMoveBlockExecution.bound q*(P*q*(S*E))) := by
  have h := hoare_extend_eq (RadixDigitMoveBlockExecution.backward_unmove_hoare source y ps ss es
    hP (by omega) hS hE hp hs he cp cs ce) (tail ws op oe)
  simpa only [← initialized_eq] using h

private theorem forward_hoare (source : ℤ → Fin (a+4)) (P S E : ℕ)
    (x : Fin (P*q*(S*E)) → Fin (a+4)) (ss op oe ps es ws : List Bool)
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (extend (RadixDigitMoveBlockExecution.forwardProgram q a) 16)
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn x)) ss op oe (some ps) (some es) (some ws))
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn (move x))) ss op oe (some ps) (some es) (some ws))
      (RadixDigitMoveBlockExecution.bound q*(P*q*(S*E))) := by
  have h := hoare_extend_eq (RadixDigitMoveBlockExecution.forward_hoare source x ps ss es
    hP (by omega) hS hE hp hs he cp cs ce) (tail ws op oe)
  simpa only [← initialized_eq] using h

/-- Take one leading high digit from after S and join it to the prefix.
The suffix is actually divided before the move and prefix multiplied after. -/
theorem join_hoare (source : ℤ → Fin (a+4)) (P S E : ℕ)
    (y : Fin (P*S*q*E) → Fin (a+4)) (ss op oe ps es ws : List Bool)
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = q*E)
    (hw : Counter.value ws = q)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (joinProgram (q := q) (a := a))
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn y)) ss op oe (some ps) (some es) (some ws))
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn (unmove y))) ss op oe
        (some (DimensionProductDescriptor.bits P q)) (some (bits E)) (some ws))
      (coefficient q*(P*q*(S*E))) := by
  have h1 := shrink_hoare (q := q) false (putWord source 0 (List.ofFn y)) ss op oe ps es ws hq ce
  simp only [Bool.false_eq_true,ite_false] at h1
  rw [he,Nat.mul_div_right E (by omega : 0 < q)] at h1
  have h2 := backward_hoare source P S E y ss op oe ps (bits E) ws hq hP hS hE hp hs
    (RecursiveChildQuotientsConstant.bits_value E) cp cs (RecursiveChildQuotientsConstant.bits_canonical E)
  have h3 := grow_hoare (q := q) true (putWord source 0 (List.ofFn (unmove y))) ss op oe ps (bits E) ws
    P hq hP hw hp cw cp
  simp only [ite_true] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hV : 0 < P*q*(S*E) := Nat.mul_pos (Nat.mul_pos hP (by omega)) (Nat.mul_pos hS hE)
  have hSE : 1 ≤ S*E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hS hE).ne'
  have hPS : 1 ≤ P*S := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hP hS).ne'
  have hprefix : P*q ≤ P*q*(S*E) := by nlinarith
  have hsuffix : q*E ≤ P*q*(S*E) := by nlinarith [Nat.mul_le_mul_right (q*E) hPS]
  have hb := Nat.mul_le_mul_left (FixedBaseDescriptorQuotient.constant q) (by omega : q*E+1 ≤ 2*(P*q*(S*E)))
  unfold coefficient
  nlinarith

/-- Return one trailing prefix digit to immediately after S, retaining its
order relative to all following high digits. -/
theorem separate_hoare (source : ℤ → Fin (a+4)) (P S E : ℕ)
    (x : Fin (P*q*(S*E)) → Fin (a+4)) (ss op oe ps es ws : List Bool)
    (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = q*P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (hw : Counter.value ws = q)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (separateProgram (q := q) (a := a))
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn x)) ss op oe (some ps) (some es) (some ws))
      (fun v => v = bank (q := q) (putWord source 0 (List.ofFn (move x))) ss op oe
        (some (bits P)) (some (DimensionProductDescriptor.bits E q)) (some ws))
      (coefficient q*(P*q*(S*E))) := by
  have h1 := shrink_hoare (q := q) true (putWord source 0 (List.ofFn x)) ss op oe ps es ws hq cp
  simp only [ite_true] at h1
  rw [hp,Nat.mul_div_right P (by omega : 0 < q)] at h1
  have h2 := forward_hoare source P S E x ss op oe (bits P) es ws hq hP hS hE
    (RecursiveChildQuotientsConstant.bits_value P) hs he (RecursiveChildQuotientsConstant.bits_canonical P) cs ce
  have h3 := grow_hoare (q := q) false (putWord source 0 (List.ofFn (move x))) ss op oe (bits P) es ws
    E hq hE hw he cw ce
  simp only [Bool.false_eq_true,ite_false] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hV : 0 < P*q*(S*E) := Nat.mul_pos (Nat.mul_pos hP (by omega)) (Nat.mul_pos hS hE)
  have hSE : 1 ≤ S*E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hS hE).ne'
  have hPS : 1 ≤ P*S := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hP hS).ne'
  have hprefix : q*P ≤ P*q*(S*E) := by nlinarith
  have hsuffix : E*q ≤ P*q*(S*E) := by nlinarith [Nat.mul_le_mul_right (q*E) hPS]
  have hb := Nat.mul_le_mul_left (FixedBaseDescriptorQuotient.constant q) (by omega : q*P+1 ≤ 2*(P*q*(S*E)))
  unfold coefficient
  nlinarith

end
end IntegerMultBounds.Machine.RadixHighBlockJoinBody
