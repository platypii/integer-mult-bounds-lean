import IntegerMultBounds.Machine.CyclicRowCycle

/-! Actual cyclic distribution of runtime-many groups of fixed-many roles.
The two supplied descriptors count row symbols and row groups. Every payload
symbol is transferred literally, and both binary loop workspaces are restored.
The machine depends on the role count and alphabet only. -/
namespace IntegerMultBounds.Machine.CyclicRowSplit
open CyclicRowCycle (rowPrefix prefix_succ prefix_all)
variable {a c n : ℕ}

def cycleWords (rows : Fin n → Fin c → List (Fin (a+4))) (i : Fin n) :=
  (List.ofFn (rows i)).flatten

def sourceWord (rows : Fin n → Fin c → List (Fin (a+4))) :=
  (List.ofFn (cycleWords rows)).flatten

def roleWord (rows : Fin n → Fin c → List (Fin (a+4))) (j : Fin c) :=
  (List.ofFn (fun i => rows i j)).flatten

def result (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (rows : Fin n → Fin c → List (Fin (a+4)))
    (bs : List Bool) (k : ℕ) : Tapes ((1+c)+2) a :=
  CyclicRowCopy.bank (putWord source p (sourceWord rows))
    (fun j => putWord (outputs j) (origins j) (rowPrefix (fun i => rows i j) k))
    (p+(rowPrefix (cycleWords rows) k).length)
    (fun j => origins j+(rowPrefix (fun i => rows i j) k).length) bs

theorem prefix_length {m : ℕ} (words : Fin m → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i, (words i).length = B) (k : ℕ) (hk : k ≤ m) :
    (rowPrefix words k).length = k*B := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [prefix_succ words ⟨k,by omega⟩,List.length_append,ih (by omega),hw]
    simp [Nat.add_mul]

theorem cycle_length (rows : Fin n → Fin c → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i j, (rows i j).length = B) (i : Fin n) : (cycleWords rows i).length = c*B := by
  have hh := prefix_length (rows i) B (hw i) c le_rfl
  simpa only [prefix_all,cycleWords] using hh

private theorem result_step (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (bs : List Bool)
    (hb : ∀ i j, Counter.value bs = (rows i j).length) (i : Fin n) :
    HoareTime (CyclicRowCycle.program c a)
      (fun v => v = result source outputs p origins rows bs i.val)
      (fun v => v = result source outputs p origins rows bs (i.val+1))
      (7*(cycleWords rows i).length+c*(7*bs.length+17)) := by
  have hh := CyclicRowCycle.cycle_hoare (putWord source p (sourceWord rows))
    (fun j => putWord (outputs j) (origins j) (rowPrefix (fun k => rows k j) i.val))
    (p+(rowPrefix (cycleWords rows) i.val).length)
    (fun j => origins j+(rowPrefix (fun k => rows k j) i.val).length) (rows i) bs (hb i)
  have hs := CyclicRowCycle.source_row source p (cycleWords rows) i
  change putWord (putWord source p (sourceWord rows))
    (p+(rowPrefix (cycleWords rows) i.val).length) (List.ofFn (rows i)).flatten = _ at hs
  rw [hs] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold result
  simp only [prefix_succ,putWord_append_forward,List.length_append,Nat.cast_add,
    ← add_assoc,cycleWords]
  rfl

def bank (v : Tapes ((1+c)+2) a) (gs : List Bool) : Tapes (((1+c)+2)+2) a :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary gs) 1 1

def program (c a : ℕ) := CountedLoopReuseAlphabet.program (CyclicRowCycle.program c a)

/-- The output tape for role j contains row j from each successive group, in
order. No sentinel, free seek, hidden tape copy, or dimension-dependent control
is used. The complete bank and every head are specified at both ends. -/
theorem split_hoare (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i j, (rows i j).length = B) (bs gs : List Bool)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n) :
    HoareTime (program c a)
      (fun v => v = bank (CyclicRowCopy.bank (putWord source p (sourceWord rows))
        outputs p origins bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank (putWord source p (sourceWord rows))
        (fun j => putWord (outputs j) (origins j) (roleWord rows j))
        (p+n*(c*B)) (fun j => origins j+n*B) bs) gs)
      (n*(7*(c*B)+c*(7*bs.length+17))+6*n+7*gs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (CyclicRowCycle.program c a) gs n
    (result source outputs p origins rows bs) (fun _ => 7*(c*B)+c*(7*bs.length+17)) hg
    (by intro i hi
        have h := result_step source outputs p origins rows bs
          (by intro i j; rw [hb,hw]) ⟨i,hi⟩
        rw [cycle_length rows B hw] at h
        exact h)
  have hp := prefix_length (cycleWords rows) (c*B) (cycle_length rows B hw) n le_rfl
  have hr (j : Fin c) := prefix_length (fun i => rows i j) B (fun i => hw i j) n le_rfl
  simp only [result] at hh
  simp_rw [hp,hr] at hh
  simp only [prefix_all] at hh
  simpa only [program,bank,rowPrefix,List.take_zero,List.flatten_nil,putWord,List.length_nil,
    Nat.cast_zero,add_zero,roleWord,Nat.cast_mul,Finset.sum_const,Finset.card_range,
    smul_eq_mul] using hh

/-- Canonical descriptors give an explicit volume-linear transition bound.
The fixed role count contributes no input-dependent machine structure. -/
theorem cost_linear (B : ℕ) (bs gs : List Bool)
    (hc : 0 < c) (hn : 0 < n) (hB : 0 < B)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs) :
    n*(7*(c*B)+c*(7*bs.length+17))+6*n+7*gs.length+16 ≤ 74*(n*(c*B)) := by
  have wb := GrowingCounterData.canonical_width bs cb
  have wg := GrowingCounterData.canonical_width gs cg
  have lb := Nat.log2_le_self (Counter.value bs)
  have lg := Nat.log2_le_self (Counter.value gs)
  have hb' : 7*bs.length+17 ≤ 31*B := by omega
  have hh := Nat.mul_le_mul_left c hb'
  have hinner : 7*(c*B)+c*(7*bs.length+17) ≤ 38*(c*B) := by nlinarith
  have houter := Nat.mul_le_mul_left n hinner
  have hv : n ≤ n*(c*B) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hc hB)
  have htail : 6*n+7*gs.length+16 ≤ 36*n := by omega
  nlinarith

end IntegerMultBounds.Machine.CyclicRowSplit
