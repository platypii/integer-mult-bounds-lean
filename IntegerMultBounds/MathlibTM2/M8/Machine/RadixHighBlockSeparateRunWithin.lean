module

public import IntegerMultBounds.MathlibTM2.M8.Machine.RadixHighBlockSeparateRun
public import IntegerMultBounds.Machine.RadixHighBlockSeparateSpace

/-! Complete inverse ordered high-block separation shares one stage workspace across
paid descriptor setup, the counted movement trace and final erasure. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.RadixHighBlockSeparateRunWithin
open IntegerMultBounds.Machine
noncomputable section
variable {q a : ℕ}
open RadixHighBlockSeparateRun

/-- Successive phases share the largest of their local reserves. -/
def coefficient (q : ℕ) := max (RadixHighBlockJoinInitialize.coefficient q+1)
  (max (RadixHighBlockSeparateLoop.spaceCoefficient q) (RadixHighBlockJoinCleanup.coefficient q+1))

private theorem input_heads (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) :
    ∀ j, 0 ≤ (RadixHighBlockJoinInitialize.input (q := q) source ss op oe
      (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)).head j ∧
      (RadixHighBlockJoinInitialize.input (q := q) source ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)).head j ≤ 1 :=
  RadixHighBlockJoinBank.controlled_head_bounds source ss op oe rs none none none

theorem separates_within (r P S E : ℕ) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (x : Fin (P*q^r*(S*E)) → Fin (a+4)) (hq : 2 ≤ q) (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hs : Counter.value ss = S) (cs : GrowingCounterData.Canonical ss)
    (hp : Counter.value op = P) (cp : GrowingCounterData.Canonical op)
    (he : Counter.value oe = E) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareWithin (program (q := q) (a := a))
      (fun v => v = RadixHighBlockJoinInitialize.input
        (RadixHighBlockJoinLoop.word source x) ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
      (fun v => v = RadixHighBlockJoinInitialize.input
        (RadixHighBlockJoinLoop.word source (RadixDigitMoveBlockRows.move x)) ss op oe
        (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs))
      (RadixHighBlockSeparateRun.coefficient q*(r+1)*(P*S*q^r*E)) (fun z => ∀ j, -(coefficient q*(P*S*q^r*E) : ℕ) ≤ z.head j ∧
        z.head j ≤ (coefficient q*(P*S*q^r*E) : ℕ)) := by
  have hV : 0 < P*S*q^r*E := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hS) (pow_pos (by omega) r)) hE
  have hI : RadixHighBlockJoinInitialize.coefficient q+1 ≤ coefficient q := le_max_left _ _
  have hL : RadixHighBlockSeparateLoop.spaceCoefficient q ≤ coefficient q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC : RadixHighBlockJoinCleanup.coefficient q+1 ≤ coefficient q :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hbI : RadixHighBlockJoinInitialize.coefficient q*(P*S*q^r*E)+1 ≤ coefficient q*(P*S*q^r*E) := by
    have h := Nat.mul_le_mul_right (P*S*q^r*E) hI
    nlinarith only [h,hV]
  have hbL := Nat.mul_le_mul_right (P*S*q^r*E) hL
  have hbC : RadixHighBlockJoinCleanup.coefficient q*(P*S*q^r*E)+1 ≤
      coefficient q*(P*S*q^r*E) := by
    have h := Nat.mul_le_mul_right (P*S*q^r*E) hC
    nlinarith only [h,hV]
  obtain ⟨hi,hc⟩ := boundary_contracts r P S E source ss op oe rs x hq hP hS hE hp cp he ce hr cr
  have hwi := HoareWithin.of_time_unit_heads hi (coefficient q*(P*S*q^r*E)) hbI
    (by rintro w rfl; exact input_heads (RadixHighBlockJoinLoop.word source x) ss op oe rs)
  have hloop := RadixHighBlockSeparateLoop.loop_within r P S E source ss op oe rs x hq hP hS hE hs cs hr cr
  rw [RadixHighBlockSeparateSemantics.separate_eq_move] at hloop
  have hwl := hloop.consequence
    (J := fun z => ∀ j, -(coefficient q*(P*S*q^r*E) : ℕ) ≤ z.head j ∧ z.head j ≤ (coefficient q*(P*S*q^r*E) : ℕ))
    (fun _ h => h) (fun _ h => h) le_rfl (by intro z hz j; have h := hz j; omega)
  have hwc := HoareWithin.of_time_unit_heads hc (coefficient q*(P*S*q^r*E)) hbC
    (by rintro w rfl; exact RadixHighBlockJoinBank.controlled_head_bounds _ ss op oe rs _ _ _)
  have hfull := (hwi.seq hwl).seq hwc
  apply HoareWithin.of_time_invariant (separates r P S E source ss op oe rs x hq hP hS hE hs cs hp cp he ce hr cr)
  intro c hc
  exact hfull.invariant hc

end
end IntegerMultBounds.MathlibTM2.M8.Machine.RadixHighBlockSeparateRunWithin
