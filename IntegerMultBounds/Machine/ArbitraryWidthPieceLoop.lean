import IntegerMultBounds.Machine.ArbitraryWidthPieceCounter
import IntegerMultBounds.Machine.ArbitraryWidthPieces
import IntegerMultBounds.Machine.LoopChain

/-! A fixed runtime base-digit loop around actual quotient/remainder
extraction. A fixed continuation consumes each physically emitted digit and
advances the framed depth/power/offset/data bank. The continuation's concrete
piece dispatch remains a separate proof obligation. No list is a machine input. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceLoop
noncomputable section
variable {a t s : ℕ}
open RecursiveChildQuotientsConstant (bits)

def remaining (B N i : ℕ) := N/B^i
def digit (B N i : ℕ) := remaining B N i%B
def count (B N : ℕ) := if N = 0 then 0 else Nat.log B N+1

theorem remaining_succ (B N i : ℕ) : remaining B N i/B = remaining B N (i+1) := by
  simp only [remaining,Nat.div_div_eq_div_mul,pow_succ]

theorem before (B N i : ℕ) (hB : 2 ≤ B) (hi : i < count B N) : 0 < remaining B N i := by
  have hn : N ≠ 0 := by intro hn; simp [count,hn] at hi
  have hl : i ≤ Nat.log B N := by simpa [count,hn] using hi
  have hp := Nat.pow_le_of_le_log hn hl
  exact Nat.div_pos hp (pow_pos (by omega) _)

theorem exit (B N : ℕ) (hB : 2 ≤ B) : remaining B N (count B N) = 0 := by
  by_cases hn : N = 0
  · simp [remaining,count,hn]
  · exact Nat.div_eq_of_lt (by simpa [remaining,count,hn] using Nat.lt_pow_succ_log_self (by omega : 1 < B) N)

def state (B N i : ℕ) (payload : Tapes t a) : Tapes (14+t) a :=
  (ArbitraryWidthPieceCounter.input (bits (remaining B N i))).append payload

def emitted (B N i : ℕ) (payload : Tapes t a) : Tapes (14+t) a :=
  (ArbitraryWidthPieceCounter.ready (bits (remaining B N (i+1))) (bits (digit B N i))).append payload

def test (sy : Fin (14+t) → Fin (a+4)) : Bool := !(sy 0 == blank)

private theorem test_state (B N i : ℕ) (payload : Tapes t a) :
    test (state B N i payload).reads = decide (remaining B N i ≠ 0) := by
  change (!(BinaryDescriptorStack.descriptor (bits (remaining B N i)) 1 == blank)) = _
  have hv := RecursiveChildQuotientsConstant.bits_value (remaining B N i)
  have hc := RecursiveChildQuotientsConstant.bits_canonical (remaining B N i)
  cases he : bits (remaining B N i) with
  | nil =>
    rw [he] at hv
    have hz : remaining B N i = 0 := hv.symm
    simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty,hz]
  | cons b bs =>
    have hn : remaining B N i ≠ 0 := by
      intro hn
      have hempty := BinaryCanonicalData.zero_nil _ hc (hv.trans hn)
      rw [he] at hempty
      cases hempty
    change (!(bitSymbol b == blank)) = _
    cases b <;> simp [hn,bitSymbol,blank,Fin.ext_iff]

def body (B : ℕ) (consume : Program (14+t) s a) :=
  seq (extend (ArbitraryWidthPieceCounter.stage (a := a) B) t) consume

def loop (B : ℕ) (consume : Program (14+t) s a) := whileLoop (body B consume) test

/-- Actual runtime digit extraction drives the supplied fixed continuation.
The contract names intermediate tape boundaries; it supplies no data to the
program and does not allow a runtime-dependent transition table. -/
theorem loop_hoare (B N : ℕ) (hB : 2 ≤ B) (consume : Program (14+t) s a)
    (payload : ℕ → Tapes t a) (consumeCost : ℕ → ℕ)
    (hconsume : ∀ i < count B N,
      HoareTime consume (fun v => v = emitted B N i (payload i))
        (fun v => v = state B N (i+1) (payload (i+1))) (consumeCost i)) :
    HoareTime (loop B consume) (fun v => v = state B N 0 (payload 0))
      (fun v => v = state B N (count B N) (payload (count B N)))
      (∑ i ∈ Finset.range (count B N),
        (ArbitraryWidthPieceCounter.stageCost B (bits (remaining B N i))+consumeCost i+3)) := by
  apply (while_chain_hoare (body B consume) test (fun i => state B N i (payload i))
    (fun i => ArbitraryWidthPieceCounter.stageCost B (bits (remaining B N i))+consumeCost i+1)
    (count B N) ?_ ?_ ?_).consequence (fun _ h => h) (fun _ h => h) (by simp)
  · intro i hi
    have hx := hoare_extend_eq (ArbitraryWidthPieceCounter.stage_hoare (a := a) B hB
      (bits (remaining B N i))) (payload i)
    simp only [RecursiveChildQuotientsConstant.bits_value,remaining_succ] at hx
    exact (hx.seq (hconsume i hi)).consequence (fun _ h => h) (fun _ h => h) (by omega)
  · intro i hi
    rw [test_state]
    simp [show remaining B N i ≠ 0 from Nat.ne_of_gt (before B N i hB hi)]
  · rw [test_state,exit B N hB]
    rfl

/-- The emitted digit is exactly the digit occurring in the manuscript's
power-width partition, and the selected power is B^i. -/
theorem digit_partition (B N k : ℕ) :
    (List.range (k+1)).flatMap (fun i => List.replicate (digit B N i) i) =
      ArbitraryWidthPieces.depths B N k := rfl

theorem count_le (B N : ℕ) : count B N ≤ N := by
  by_cases hn : N = 0
  · simp [count,hn]
  · have hh := Nat.log_lt_self B hn
    simp only [count,ite_eq_right hn]
    omega

/-- Repeated quotient scans have a genuine geometric budget in the original
runtime width, rather than multiplying every scan by its original size. -/
theorem remaining_sum (B N r : ℕ) (hB : 2 ≤ B) :
    (∑ i ∈ Finset.range r, remaining B N i) ≤ 2*N := by
  induction r generalizing N with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ']
    have he : (∑ i ∈ Finset.range r, remaining B N (i+1)) =
        ∑ i ∈ Finset.range r, remaining B (N/B) i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [remaining,pow_succ,Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm]
    rw [he]
    have hh := ih (N/B)
    have hdiv := Nat.div_mul_le_self N B
    have htwo : 2*(N/B) ≤ N := by nlinarith
    have hzero : remaining B N 0 = N := by simp [remaining]
    rw [hzero]
    omega

def overheadConstant (B : ℕ) := 3*ArbitraryWidthPieceCounter.stageConstant B+3

theorem loop_linear (B N : ℕ) (hB : 2 ≤ B) (consume : Program (14+t) s a)
    (payload : ℕ → Tapes t a) (consumeCost : ℕ → ℕ)
    (hconsume : ∀ i < count B N,
      HoareTime consume (fun v => v = emitted B N i (payload i))
        (fun v => v = state B N (i+1) (payload (i+1))) (consumeCost i)) :
    HoareTime (loop B consume) (fun v => v = state B N 0 (payload 0))
      (fun v => v = state B N (count B N) (payload (count B N)))
      (overheadConstant B*(N+1)+(∑ i ∈ Finset.range (count B N), consumeCost i)) := by
  apply (loop_hoare B N hB consume payload consumeCost hconsume).consequence
    (fun _ h => h) (fun _ h => h)
  let C := ArbitraryWidthPieceCounter.stageConstant B
  have hsum : (∑ i ∈ Finset.range (count B N),
      (ArbitraryWidthPieceCounter.stageCost B (bits (remaining B N i))+consumeCost i+3)) ≤
      C*((∑ i ∈ Finset.range (count B N), remaining B N i)+count B N)+
        (∑ i ∈ Finset.range (count B N), consumeCost i)+3*count B N := by
    calc
      _ ≤ ∑ i ∈ Finset.range (count B N), (C*(remaining B N i+1)+consumeCost i+3) := by
        apply Finset.sum_le_sum
        intro i _
        have h := ArbitraryWidthPieceCounter.stageCost_linear B (bits (remaining B N i))
          (RecursiveChildQuotientsConstant.bits_canonical _)
        rw [RecursiveChildQuotientsConstant.bits_value] at h
        change _ ≤ C*(remaining B N i+1) at h
        omega
      _ = _ := by simp [Finset.sum_add_distrib,← Finset.mul_sum]; ring
  have hc := count_le B N
  have hr := remaining_sum B N (count B N) hB
  have hm := Nat.mul_le_mul_left C (show (∑ i ∈ Finset.range (count B N), remaining B N i)+count B N ≤ 3*N by omega)
  unfold overheadConstant
  change _ ≤ (3*C+3)*(N+1)+_
  nlinarith

def program (B : ℕ) (consume : Program (14+t) s a) := seq (loop B consume)
  (extend (BinaryDescriptorCleanupList.oneProgram (a := a) (0 : Fin 14)) t)

/-- The digit driver itself ends with all fourteen arithmetic/control tapes
blank at head zero. Only the continuation's explicitly specified payload is
retained. Concrete depth/power/offset updates belong to that continuation. -/
theorem runs_clean (B N : ℕ) (hB : 2 ≤ B) (consume : Program (14+t) s a)
    (payload : ℕ → Tapes t a) (consumeCost : ℕ → ℕ)
    (hconsume : ∀ i < count B N,
      HoareTime consume (fun v => v = emitted B N i (payload i))
        (fun v => v = state B N (i+1) (payload (i+1))) (consumeCost i)) :
    HoareTime (program B consume) (fun v => v = state B N 0 (payload 0))
      (fun v => v = (SharedBank.empty 14 a).append (payload (count B N)))
      ((overheadConstant B+5)*(N+1)+(∑ i ∈ Finset.range (count B N), consumeCost i)) := by
  have hc := BinaryDescriptorCleanupList.one_hoare (0 : Fin 14)
    (ArbitraryWidthPieceCounter.input (a := a) (bits 0)) [] rfl rfl
  have he : SharedPlacementAlphabet.setTape (ArbitraryWidthPieceCounter.input (a := a) (bits 0))
      (0 : Fin 14) (fun _ => blank) 0 = SharedBank.empty 14 a := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at hc
  have hc' := hoare_extend_eq hc (payload (count B N))
  have hx := loop_linear B N hB consume payload consumeCost hconsume
  have hstate : state B N (count B N) (payload (count B N)) =
      (ArbitraryWidthPieceCounter.input (bits 0)).append (payload (count B N)) := by
    rw [state,exit B N hB]
  rw [hstate] at hx
  exact (hx.seq hc').consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_nil]; nlinarith)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceLoop
