module

public import IntegerMultBounds.Machine.RadixHighBlockJoinLoop
public import IntegerMultBounds.Machine.CountedLoopReuseAlphabetSpace
public import IntegerMultBounds.Machine.HoareWithin

/-! Ordered high-digit joining shares one linear stage workspace across its
actual counted trace. Every boundary head is zero or one, independent of data. -/
@[expose] public section
namespace IntegerMultBounds.Machine
noncomputable section
variable {q a : ℕ}

namespace RadixHighBlockJoinBank

theorem head_bounds (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) :
    ∀ j, 0 ≤ (bank (q := q) source ss op oe ps es ws).head j ∧
      (bank (q := q) source ss op oe ps es ws).head j ≤ 1 := by
  have hp : 0 ≤ hd ps ∧ hd ps ≤ 1 := by cases ps <;> simp [hd]
  have he : 0 ≤ hd es ∧ hd es ≤ 1 := by cases es <;> simp [hd]
  have hw : 0 ≤ hd ws ∧ hd ws ≤ 1 := by cases ws <;> simp [hd]
  intro j
  dsimp only [bank]
  split_ifs <;> omega

theorem controlled_head_bounds (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (ps es ws : Option (List Bool)) :
    ∀ j, 0 ≤ (CountedLoopReuseAlphabet.bank (RadixHighBlockJoinBank.bank (q := q) source ss op oe ps es ws)
      CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1).head j ∧
      (CountedLoopReuseAlphabet.bank (RadixHighBlockJoinBank.bank (q := q) source ss op oe ps es ws)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1).head j ≤ 1 := by
  intro j
  induction j using Fin.addCases with
  | left j => simpa only [CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left]
      using RadixHighBlockJoinBank.head_bounds source ss op oe ps es ws j
  | right j =>
    simp only [CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,ite_self]
    omega


end RadixHighBlockJoinBank

namespace RadixHighBlockJoinLoop

theorem trace_heads (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) :
    ∀ i j, 0 ≤ ((trace r P S E source ss op oe x).getD i defaultBank).head j ∧
      ((trace r P S E source ss op oe x).getD i defaultBank).head j ≤ 1 := by
  induction r generalizing P with
  | zero =>
    intro i j
    cases i with
    | zero => exact RadixHighBlockJoinBank.head_bounds _ _ _ _ _ _ _ j
    | succ i => simp [trace,List.getD,defaultBank,SharedBank.empty]
  | succ r ih =>
    intro i j
    cases i with
    | zero => exact RadixHighBlockJoinBank.head_bounds _ _ _ _ _ _ _ j
    | succ i => simpa only [trace,List.getD_cons_succ] using ih (P*q) (nextArray P S E r x) i j

def spaceCoefficient (q : ℕ) := RadixHighBlockJoinBody.coefficient q+20

theorem loop_within (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*S*q^r*E) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareWithin (program (q := q) (a := a))
      (· = CountedLoopReuseAlphabet.bank (firstBank P S E r source ss op oe x)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary rs) 1 1)
      (· = CountedLoopReuseAlphabet.bank (finalBank P S E r source ss op oe (RadixHighBlockJoinSemantics.join q r P S E x))
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
  exact CountedLoopReuseAlphabet.loop_heads_linear RadixHighBlockJoinBody.joinProgram rs
    (fun i => (trace r P S E source ss op oe x).getD i defaultBank)
    (RadixHighBlockJoinBody.coefficient q) (P*S*q^r*E) hV (by simpa only [hr] using hrV) cr
    (by simpa only [hr] using trace_steps r P S E source ss op oe x hq hP hS hE hs cs)
    (fun i _ => trace_heads r P S E source ss op oe x i) hn

end RadixHighBlockJoinLoop
end
end IntegerMultBounds.Machine
