module

public import IntegerMultBounds.Machine.RadixHighBlockJoinSpace
public import IntegerMultBounds.Machine.RadixHighBlockSeparateLoop

/-! Inverse ordered separation uses the same normalized-bank and counted-loop
workspace language as joining, with one linear allowance for every stage. -/
@[expose] public section
namespace IntegerMultBounds.Machine
noncomputable section
variable {q a : ℕ}

namespace RadixHighBlockSeparateLoop

theorem trace_heads (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) :
    ∀ i j, 0 ≤ ((trace r P S E source ss op oe x).getD i defaultBank).head j ∧
      ((trace r P S E source ss op oe x).getD i defaultBank).head j ≤ 1 := by
  induction r generalizing E with
  | zero =>
    intro i j
    cases i with
    | zero => exact RadixHighBlockJoinBank.head_bounds _ _ _ _ _ _ _ j
    | succ i => simp [trace,List.getD,defaultBank,SharedBank.empty]
  | succ r ih =>
    intro i j
    cases i with
    | zero => exact RadixHighBlockJoinBank.head_bounds _ _ _ _ _ _ _ j
    | succ i => simpa only [trace,List.getD_cons_succ] using ih (q*E) (nextArray P S E r x) i j

def spaceCoefficient (q : ℕ) := RadixHighBlockJoinBody.coefficient q+20

theorem loop_within (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareWithin (program (q := q) (a := a))
      (· = CountedLoopReuseAlphabet.bank (firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (· = CountedLoopReuseAlphabet.bank (finalBank P S E r source ss op oe (RadixHighBlockSeparateSemantics.separate q r P S E x))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (loopCoefficient q*(r+1)*(P*S*q^r*E))
      (fun z => ∀ j, -(spaceCoefficient q*(P*S*q^r*E) : ℕ) ≤ z.head j ∧
        z.head j ≤ (spaceCoefficient q*(P*S*q^r*E) : ℕ)) := by
  have hV : 0 < P*S*q^r*E := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hS) (pow_pos (by omega) r)) hE
  have hqV : q^r ≤ P*S*q^r*E :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos hP hS)).trans (Nat.le_mul_of_pos_right _ hE)
  have hrV := (RadixToBinaryData.width_le_power hq r).trans hqV
  apply HoareWithin.of_time_invariant (loop_hoare r P S E source ss op oe rs x hq hP hS hE hs cs hr cr)
  intro c hc
  obtain ⟨v,rfl,n,hn⟩ := hc
  rw [← trace_head r P S E source ss op oe x] at hn
  exact CountedLoopReuseAlphabet.loop_heads_linear RadixHighBlockJoinBody.separateProgram rs
    (fun i => (trace r P S E source ss op oe x).getD i defaultBank)
    (RadixHighBlockJoinBody.coefficient q) (P*S*q^r*E) hV (by simpa only [hr] using hrV) cr
    (by simpa only [hr] using trace_steps r P S E source ss op oe x hq hP hS hE hs cs)
    (fun i _ => trace_heads r P S E source ss op oe x i) hn

end RadixHighBlockSeparateLoop
end
end IntegerMultBounds.Machine
