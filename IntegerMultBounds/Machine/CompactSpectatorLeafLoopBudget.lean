import IntegerMultBounds.Machine.CompactSpectatorLeafAxisBudget
import IntegerMultBounds.Machine.CompactSpectatorLeafLoop
import IntegerMultBounds.Machine.CompactSpectatorInverseLeafLoop

/-! The real counted sparse interval and its final eleven-descriptor erasure
fit native serialized volume times the actual executed visit count. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafLoopBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorLeafAxisBudget (volume)
variable (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)

theorem volume_values (hr : 0<rows) :
    s.bits≤volume s rows ell p ∧ p≤volume s rows ell p ∧ 2^ell≤volume s rows ell p ∧
    ell≤volume s rows ell p ∧ rows≤volume s rows ell p := by
  have hb : 1≤2^s.bits := Nat.one_le_two_pow
  have he : 1≤2^ell := Nat.one_le_two_pow
  have hl : 1≤ButterflyAxisHeadersData.recordLength s.bits p := by
    unfold ButterflyAxisHeadersData.recordLength
    omega
  have hm : 1≤rows*2^s.bits*2^ell := by
    have h0 := Nat.mul_le_mul (show 1≤rows by omega) hb
    simpa using Nat.mul_le_mul h0 he
  have hv := Nat.mul_le_mul_right (ButterflyAxisHeadersData.recordLength s.bits p) hm
  have hbits : s.bits≤ButterflyAxisHeadersData.recordLength s.bits p := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width
    omega
  have hp : p≤ButterflyAxisHeadersData.recordLength s.bits p := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width
    omega
  have hpoly : 2^ell≤rows*2^s.bits*2^ell := Nat.le_mul_of_pos_left _ (by positivity)
  have hrow : rows≤rows*2^s.bits*2^ell :=
    (Nat.le_mul_of_pos_right rows (pow_pos (by decide) _)).trans
      (Nat.le_mul_of_pos_right _ (pow_pos (by decide) _))
  have hf := Nat.mul_le_mul_left (rows*2^s.bits*2^ell) hl
  have hel : ell≤2^ell := Nat.le_of_lt Nat.lt_two_pow_self
  have hv1 : ButterflyAxisHeadersData.recordLength s.bits p≤rows*2^s.bits*2^ell*ButterflyAxisHeadersData.recordLength s.bits p := by simpa using hv
  have hf1 : rows*2^s.bits*2^ell≤rows*2^s.bits*2^ell*ButterflyAxisHeadersData.recordLength s.bits p := by simpa using hf
  have heq : volume s rows ell p=rows*2^s.bits*2^ell*ButterflyAxisHeadersData.recordLength s.bits p := by
    unfold volume ButterflySpectatorBudget.volume ButterflyAxisHeadersBudget.logicalVolume
    ring
  rw [heq]
  exact ⟨hbits.trans hv1,hp.trans hv1,hpoly.trans hf1,hel.trans (hpoly.trans hf1),hrow.trans hf1⟩

theorem final_values (hr : 0<rows) :
    ∀ i,Counter.value (CompactSpectatorLeafLoop.values s rows ell p rho visit (left+arity^k) i)≤volume s rows ell p := by
  have hn : 0<arity^k := pow_pos (by decide) _
  have hfit := visit.fits
  have ho : left<s.active := by omega
  obtain ⟨hH,hB,hA,hK,hrho,hl,_,_⟩ := CompactSpectatorLeafAxisBudget.descriptors s rho.val left rho.isLt ho
  obtain ⟨hb,hp,hpoly,hell,hrows⟩ := volume_values s rows ell p hr
  intro i
  fin_cases i <;> simp [CompactSpectatorLeafLoop.values,RecursiveChildQuotientsConstant.bits_value]
  all_goals omega

theorem cleanup_cost (hr : 0<rows) :
    BinaryDescriptorCleanupList.cost CompactSpectatorLeafLoop.fields
      (CompactSpectatorLeafLoop.values s rows ell p rho visit (left+arity^k))≤99*volume s rows ell p := by
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell) p hr (pow_pos (by decide) _)
  change 0<volume s rows ell p at hV
  have hl (i : Fin 43) : (CompactSpectatorLeafLoop.values s rows ell p rho visit (left+arity^k) i).length≤volume s rows ell p+1 := by
    have hc : GrowingCounterData.Canonical (CompactSpectatorLeafLoop.values s rows ell p rho visit (left+arity^k) i) :=
      RecursiveChildQuotientsConstant.bits_canonical _
    exact (GrowingCounterData.canonical_width _ hc).trans
      (Nat.add_le_add_right ((Nat.log2_le_self _).trans (final_values s rows ell p rho visit hr i)) 1)
  have hh := BinaryDescriptorCleanupList.cost_le CompactSpectatorLeafLoop.fields
    (CompactSpectatorLeafLoop.values s rows ell p rho visit (left+arity^k)) (volume s rows ell p+1) (fun i _ => hl i)
  simp only [CompactSpectatorLeafLoop.fields,List.length_cons,List.length_nil] at hh ⊢
  omega

def constant := CompactSpectatorLeafAxisBudget.constant+163

theorem cost_linear (hr : 0<rows) :
    CompactSpectatorLeafLoop.cost s rows ell p rho visit≤constant*volume s rows ell p*(arity^k) := by
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell) p hr (pow_pos (by decide) _)
  change 0<volume s rows ell p at hV
  have hn : 0<arity^k := pow_pos (by decide) _
  have hf := visit.fits
  have hs : (∑ i ∈ Finset.range (arity^k),CompactSpectatorLeafAxis.cost s rows ell p rho.val (left+i) (arity^k))≤
      (arity^k)*(CompactSpectatorLeafAxisBudget.constant*volume s rows ell p) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (arity^k),CompactSpectatorLeafAxisBudget.constant*volume s rows ell p := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finset.mem_range.mp hi
        exact CompactSpectatorLeafAxisBudget.cost_linear s rows ell p rho.val (left+i) (arity^k) hr rho.isLt (by omega)
      _ = _ := by simp
  have hl := GrowingCounterData.canonical_width (RecursiveChildQuotientsConstant.bits (arity^k))
    (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [RecursiveChildQuotientsConstant.bits_value] at hl
  have hlog := Nat.log2_le_self (arity^k)
  have hc := cleanup_cost s rows ell p rho visit hr
  unfold CompactSpectatorLeafLoop.cost CompactSpectatorLeafLoop.loopCost CountedLoopHeaderClean.cost constant
  nlinarith only [hs,hl,hlog,hc,hV,hn]

theorem inverse_cost_linear (hr : 0<rows) :
    CompactSpectatorInverseLeafLoop.cost s rows ell p rho visit≤constant*volume s rows ell p*(arity^k) := by
  exact cost_linear s rows ell p rho visit hr

end
end IntegerMultBounds.Machine.CompactSpectatorLeafLoopBudget
