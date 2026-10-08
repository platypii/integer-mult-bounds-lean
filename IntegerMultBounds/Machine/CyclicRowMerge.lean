import IntegerMultBounds.Machine.CyclicRowMergeCycle
import IntegerMultBounds.Machine.CyclicRowSplit

/-! Actual runtime-many-group cyclic merge. It is the serialized inverse of
CyclicRowSplit: take successive rows from role tapes in the fixed cyclic order.
Input role heads must be positioned at their origins by charged caller code. -/
namespace IntegerMultBounds.Machine.CyclicRowMerge
open CyclicRowCycle (rowPrefix prefix_succ prefix_all)
open CyclicRowSplit (cycleWords sourceWord roleWord bank prefix_length cycle_length)
variable {a c n : ℕ}

def result (dest : ℤ → Fin (a+4)) (sources : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (rows : Fin n → Fin c → List (Fin (a+4)))
    (bs : List Bool) (k : ℕ) : Tapes ((1+c)+2) a :=
  CyclicRowCopy.bank (putWord dest p (rowPrefix (cycleWords rows) k))
    (fun j => putWord (sources j) (origins j) (roleWord rows j))
    (p+(rowPrefix (cycleWords rows) k).length)
    (fun j => origins j+(rowPrefix (fun i => rows i j) k).length) bs

private theorem result_step (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (bs : List Bool)
    (hb : ∀ i j, Counter.value bs = (rows i j).length) (i : Fin n) :
    HoareTime (CyclicRowMergeCycle.program c a)
      (fun v => v = result dest sources p origins rows bs i.val)
      (fun v => v = result dest sources p origins rows bs (i.val+1))
      (7*(cycleWords rows i).length+c*(7*bs.length+17)) := by
  have hh := CyclicRowMergeCycle.cycle_hoare (putWord dest p (rowPrefix (cycleWords rows) i.val))
    (fun j => putWord (sources j) (origins j) (roleWord rows j))
    (p+(rowPrefix (cycleWords rows) i.val).length)
    (fun j => origins j+(rowPrefix (fun k => rows k j) i.val).length) (rows i) bs (hb i)
  have hs (j : Fin c) := CyclicRowCycle.source_row (sources j) (origins j) (fun k => rows k j) i
  simp only [roleWord] at hh
  simp_rw [hs] at hh
  rw [putWord_append_forward] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold result
  simp only [prefix_succ,List.length_append,Nat.cast_add,← add_assoc,cycleWords,roleWord]

def program (c a : ℕ) := CountedLoopReuseAlphabet.program (CyclicRowMergeCycle.program c a)

/-- Literal whole-bank cyclic merge, with unchanged role streams and exact
advancing heads. All row/group count copying, countdowns, resets, and joins
are included in the transition bound. -/
theorem merge_hoare (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i j, (rows i j).length = B) (bs gs : List Bool)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n) :
    HoareTime (program c a)
      (fun v => v = bank (CyclicRowCopy.bank dest
        (fun j => putWord (sources j) (origins j) (roleWord rows j)) p origins bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank (putWord dest p (sourceWord rows))
        (fun j => putWord (sources j) (origins j) (roleWord rows j))
        (p+n*(c*B)) (fun j => origins j+n*B) bs) gs)
      (n*(7*(c*B)+c*(7*bs.length+17))+6*n+7*gs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (CyclicRowMergeCycle.program c a) gs n
    (result dest sources p origins rows bs) (fun _ => 7*(c*B)+c*(7*bs.length+17)) hg
    (by intro i hi
        have h := result_step dest sources p origins rows bs
          (by intro i j; rw [hb,hw]) ⟨i,hi⟩
        rw [cycle_length rows B hw] at h
        exact h)
  have hp := prefix_length (cycleWords rows) (c*B) (cycle_length rows B hw) n le_rfl
  have hr (j : Fin c) := prefix_length (fun i => rows i j) B (fun i => hw i j) n le_rfl
  simp only [result] at hh
  simp_rw [hp,hr] at hh
  simp only [prefix_all] at hh
  simpa only [program,bank,rowPrefix,List.take_zero,List.flatten_nil,putWord,List.length_nil,
    Nat.cast_zero,add_zero,sourceWord,Nat.cast_mul,Finset.sum_const,Finset.card_range,
    smul_eq_mul] using hh

/-- Exactly the same explicit linear-volume bound as cyclic splitting. -/
theorem cost_linear (B : ℕ) (bs gs : List Bool)
    (hc : 0 < c) (hn : 0 < n) (hB : 0 < B)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs) :
    n*(7*(c*B)+c*(7*bs.length+17))+6*n+7*gs.length+16 ≤ 74*(n*(c*B)) :=
  CyclicRowSplit.cost_linear B bs gs hc hn hB hb hg cb cg

end IntegerMultBounds.Machine.CyclicRowMerge
