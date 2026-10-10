import IntegerMultBounds.Machine.CompactComplexControllerAlignedCommit
import IntegerMultBounds.Machine.CompactComplexScalarPathGuard
import IntegerMultBounds.Machine.CompactComplexStoppedGridHandoff

/-! The live true-denominator dependency envelope has actual retained-field
capacity. This does not identify the live header with width metadata: recursive
execution must propagate the stated live-progress invariant. Once propagated,
no separate denominator-at-most-stream-volume cost allowance is needed. -/
namespace IntegerMultBounds.Machine.CompactComplexDenominatorCapacity
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactRecursiveDependencyBudget
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorInheritedGrid (half)
attribute [local irreducible] Networks.ComplexFramedExecution.rows

def scalarRows := Networks.ComplexFramedExecution.rows.length

def ledger (R n levels frames returned usedRows : ℕ) :=
  n+levels*R+frames+2*returned+usedRows

def room (R : ℕ) := R+volumeCoefficient+2

/-- Scalar completion adds one true-denominator unit and one prefix row. -/
theorem scalar_advance (R n levels frames returned usedRows current : ℕ)
    (h : current≤ledger R n levels frames returned usedRows) :
    current+1≤ledger R n levels frames returned (usedRows+1) := by
  unfold ledger at *
  omega

/-- Enter the genuine call occurrence with its real preceding-sibling
counter. The ancestor's scalar prefix is paid by the next dependency level. -/
theorem child_entry (R n levels frames returned usedRows current k : ℕ)
    (call : Networks.ComplexRecursiveCallSchema.Call) (hp : usedRows≤R)
    (h : current≤ledger R n levels frames
      (returned+precedingCalls call*arity^k) usedRows) :
    current≤ledger R n (levels+1) (frames+arity^(k+1))
      (returned+precedingCalls call*arity^k) 0 := by
  unfold ledger at *
  simp only [Nat.add_mul,Nat.one_mul,Nat.add_zero]
  omega

/-- Both certified child return policies advance by at most twice the child
volume. The returned-sibling ledger pays this actual header advancement. -/
theorem returned_advance (R n levels frames returned usedRows current after gap : ℕ)
    (h : current≤ledger R n levels frames returned usedRows) (ha : after≤current+2*gap) :
    after≤ledger R n levels frames (returned+gap) usedRows := by
  unfold ledger at *
  simp only [Nat.mul_add]
  omega

private theorem path_bound_general {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned) (n usedRows R : ℕ)
    (hp : usedRows≤R) :
    n+levels*R+frames+2*returned+usedRows+2*arity^k≤n+(R+volumeCoefficient+2)*sh.active := by
  have hl := path.levels_le
  have hpow : 0<arity^k := pow_pos (by decide) _
  have hv : frames+2*returned≤volumeCoefficient*sh.active := path.volume_bound
  have hlevels : levels+1≤sh.active := by omega
  have hm := Nat.mul_le_mul_right R hlevels
  simp only [Nat.add_mul,Nat.one_mul] at hm
  rw [Nat.mul_comm sh.active R] at hm
  have haxis := Nat.mul_le_mul_left 2 (show arity^k≤sh.active by omega)
  simp only [Nat.add_mul]
  omega

/-- Actual scalar prefixes use the genuine complete finite-row count. -/
theorem actual_prefix (g : ℕ) : (CompactFramedScalarGrid.rows g).length≤scalarRows :=
  CompactRecursiveDependencyBudget.prefix_rows_le g

/-- The extra whole-child return policy and every actual scalar prefix fit
one fixed linear active-axis allowance. -/
theorem path_bound {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned) (R n usedRows : ℕ)
    (hp : usedRows≤R) :
    ledger R n levels frames returned usedRows+2*arity^k≤n+room R*sh.active :=
  path_bound_general path n usedRows R hp

/-- The original chunk reserve converts the actual dependency envelope into
capacity in the existing stored signed field. -/
theorem target_capacity {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (R n q usedRows current target : ℕ) (hn : n≤q) (hp : usedRows≤R)
    (hroom : room R≤sh.chunk)
    (hlive : current≤ledger R n levels frames returned usedRows)
    (htarget : target≤current+2*arity^k) : target≤half sh q := by
  have hb := path_bound path R n usedRows hp
  have hm := Nat.mul_le_mul_right sh.active hroom
  have hbits : room R*sh.active≤sh.bits := by exact hm.trans (by unfold Shape.bits; rw [Nat.mul_comm sh.active sh.chunk]; omega)
  unfold half ButterflyGuard.halfWidth
  omega

/-- A positive original coefficient count pays a whole field and hence the
certified target; this is actual encoded stream volume. -/
theorem target_volume {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (R n q usedRows current target rows ell : ℕ) (hn : n≤q) (hp : usedRows≤R)
    (hroom : room R≤sh.chunk) (hlive : current≤ledger R n levels frames returned usedRows)
    (htarget : target≤current+2*arity^k) (hr : 0<rows) :
    target≤ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2)) := by
  have hc := target_capacity path R n q usedRows current target hn hp hroom hlive htarget
  have hpos : 0<ButterflySpectatorGeometry.Size rows sh.bits (2^ell) := by
    rw [CompactSpectatorVisitGeometry.coefficient_count]
    positivity
  have hm := Nat.le_mul_of_pos_left (2*(half sh q+2)) hpos
  omega

/-- The genuine literal signed words have the same paid volume. -/
theorem target_words_volume {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (R n q usedRows current target rows ell : ℕ) (hn : n≤q) (hp : usedRows≤R)
    (hroom : room R≤sh.chunk) (hlive : current≤ledger R n levels frames returned usedRows)
    (htarget : target≤current+2*arity^k) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f) :
    target≤NativeSignedReturnStream.volume (CompactComplexStoppedGridHandoff.words f) := by
  rw [CompactComplexStoppedGridHandoff.words_volume sh rows ell q f hw]
  exact target_volume path R n q usedRows current target rows ell hn hp hroom hlive htarget hr

/-- Once the actual live-progress invariant is propagated, the complete
spectator promotion and live-commit cost is uniformly linear in native volume. -/
theorem promotion_commit_cost (count V current target : ℕ) (ht : target≤V)
    (hc : current≤target) :
    count*(130*V+8*target+360)+1+
      (2*(RecursiveChildQuotientsConstant.bits current).length+
        4*(RecursiveChildQuotientsConstant.bits target).length+15) ≤
      (138*count+6)*V+360*count+22 := by
  have h0 := CompactComplexControllerAlignedCommit.cost_le current target
  have hm := Nat.mul_le_mul_left count (show 130*V+8*target+360≤138*V+360 by omega)
  nlinarith

/-- Nonempty native streams absorb every fixed join and descriptor constant. -/
theorem promotion_commit_linear (count V current target : ℕ) (ht : target≤V)
    (hc : current≤target) (hV : 0<V) :
    count*(130*V+8*target+360)+1+
      (2*(RecursiveChildQuotientsConstant.bits current).length+
        4*(RecursiveChildQuotientsConstant.bits target).length+15) ≤
      (498*count+28)*V := by
  have hb := promotion_commit_cost count V current target ht hc
  have hm := Nat.mul_le_mul_left (360*count+22) (show 1≤V by omega)
  nlinarith

/-- The paid physical promotion/commit expression is linear in the actual
original role stream, with its target-volume premise derived from the Path. -/
theorem cost_from_path {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (R n q usedRows current target rows ell count : ℕ) (hn : n≤q) (hp : usedRows≤R)
    (hroom : room R≤sh.chunk) (hlive : current≤ledger R n levels frames returned usedRows)
    (htarget : target≤current+2*arity^k) (hle : current≤target) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f) :
    let V := NativeSignedReturnStream.volume (CompactComplexStoppedGridHandoff.words f)
    count*(130*V+8*target+360)+1+
      (2*(RecursiveChildQuotientsConstant.bits current).length+
        4*(RecursiveChildQuotientsConstant.bits target).length+15) ≤(498*count+28)*V := by
  have ht := target_words_volume path R n q usedRows current target rows ell hn hp hroom hlive htarget hr f hw
  have hpos : 0<NativeSignedReturnStream.volume (CompactComplexStoppedGridHandoff.words f) := by
    rw [CompactComplexStoppedGridHandoff.words_volume sh rows ell q f hw,
      CompactSpectatorVisitGeometry.coefficient_count]
    positivity
  exact promotion_commit_linear count _ current target ht hle hpos

/-- The original multiplier chunk eventually pays this fixed reserve. -/
theorem eventually_room (R : ℕ) : ∀ᶠ n : ℕ in Filter.atTop,room R≤Sizes.K n :=
  CompactComplexScalarPathGuard.eventually_chunk_room _

/-- Specialize the typed capacity rule to the actual finite scalar list.
The live-progress premise remains the recursive execution invariant. -/
theorem actual_target_capacity {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (n q usedRows current target : ℕ) (hn : n≤q) (hp : usedRows≤scalarRows)
    (hroom : room scalarRows≤sh.chunk)
    (hlive : current≤ledger scalarRows n levels frames returned usedRows)
    (htarget : target≤current+2*arity^k) : target≤half sh q :=
  target_capacity path scalarRows n q usedRows current target hn hp hroom hlive htarget

theorem eventually_actual_room : ∀ᶠ n : ℕ in Filter.atTop,room scalarRows≤Sizes.K n :=
  eventually_room scalarRows

end
end IntegerMultBounds.Machine.CompactComplexDenominatorCapacity
