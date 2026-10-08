import IntegerMultBounds.Machine.ScalingDescriptors

/-! Literal binary product-descriptor synthesis by nested counted loops. The
outer N descriptor need not be canonical; starting the growing output at zero
still gives the exact canonical N*B. All binary countdown setup/cleanup is charged. -/

namespace IntegerMultBounds.Machine.TranslationProduct

open CountedCopyReuse (empty binary)

private theorem totalCost_add (m n : ℕ) (bs : List Bool) :
    GrowingCounterData.totalCost (m+n) bs = GrowingCounterData.totalCost m bs+
      GrowingCounterData.totalCost n (GrowingCounterData.advance m bs) := by
  induction m generalizing bs with
  | zero => simp [GrowingCounterData.totalCost,GrowingCounterData.advance]
  | succ m ih =>
    simp only [Nat.succ_add,GrowingCounterData.totalCost,GrowingCounterData.advance,ih]
    omega

/-- The carries of the nested loops form one continuous amortized counter run. -/
theorem batch_cost (N B : ℕ) (ds : List Bool) :
    (∑ i ∈ Finset.range N, GrowingCounterData.totalCost B (GrowingCounterData.advance (i*B) ds)) =
      GrowingCounterData.totalCost (N*B) ds := by
  induction N with
  | zero => simp [GrowingCounterData.totalCost]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Nat.add_mul,Nat.one_mul,totalCost_add]

def bank {c : ℕ} (ds : Fin c → List Bool) (bs ns : List Bool) : Tapes (1+c+2+2) 0 :=
  CountedLoopReuse.bank (ScalingDescriptors.innerBank ds bs) empty (binary ns) 1 1

/-- A single fixed output-counter slot; N and B are ordinary tape data. -/
def program {c : ℕ} (j : Fin c) : Program (1+c+2+2) 35 0 :=
  CountedLoopReuse.program (ScalingDescriptors.innerProgram j)

/-- Exact accumulated carry costs, plus all nested countdown preparation,
physical head returns, joins and cleanup. Complement counts can be padded. -/
theorem product_hoare {c : ℕ} (ds : Fin c → List Bool) (j : Fin c)
    (bs ns : List Bool) (B N : ℕ) (hb : Counter.value bs = B) (hn : Counter.value ns = N) :
    HoareTime (program j) (fun v => v = bank ds bs ns)
      (fun v => v = bank (Function.update ds j (GrowingCounterData.advance (N*B) (ds j))) bs ns)
      (GrowingCounterData.totalCost (N*B) (ds j)+6*(N*B)+7*N*bs.length+22*N+7*ns.length+16) := by
  have hbody (i : ℕ) (_hi : i < N) : HoareTime (ScalingDescriptors.innerProgram j)
      (fun v => v = ScalingDescriptors.innerBank
        (Function.update ds j (GrowingCounterData.advance (i*B) (ds j))) bs)
      (fun v => v = ScalingDescriptors.innerBank
        (Function.update ds j (GrowingCounterData.advance ((i+1)*B) (ds j))) bs)
      (GrowingCounterData.totalCost B (GrowingCounterData.advance (i*B) (ds j))+6*B+7*bs.length+16) := by
    have hh := ScalingDescriptors.inner_hoare
      (Function.update ds j (GrowingCounterData.advance (i*B) (ds j))) j bs B hb
    simpa only [Function.update_self,Function.update_idem,Nat.add_mul,Nat.one_mul,
      ScalingDescriptorData.advance_add] using hh
  have hh := CountedLoopReuse.loop_hoare (ScalingDescriptors.innerProgram j) ns N
    (fun i => ScalingDescriptors.innerBank
      (Function.update ds j (GrowingCounterData.advance (i*B) (ds j))) bs)
    (fun i => GrowingCounterData.totalCost B (GrowingCounterData.advance (i*B) (ds j))+6*B+7*bs.length+16)
    hn hbody
  simp only [Nat.zero_mul,GrowingCounterData.advance,Function.update_eq_self] at hh
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,batch_cost]
  ring_nf
  omega

/-- Starting from the empty growing descriptor gives a canonical binary product. -/
theorem product_value (N B : ℕ) : Counter.value (GrowingCounterData.advance (N*B) []) = N*B :=
  GrowingCounterData.empty_value _

theorem product_canonical (N B : ℕ) : GrowingCounterData.Canonical (GrowingCounterData.advance (N*B) []) :=
  GrowingCounterData.advance_canonical _ [] (Or.inl rfl)

/-- Width-sensitive synthesis bound, also valid for a noncanonical outer count. -/
theorem product_empty_hoare {c : ℕ} (ds : Fin c → List Bool) (j : Fin c) (hj : ds j = [])
    (bs ns : List Bool) (B N : ℕ) (hb : Counter.value bs = B) (hn : Counter.value ns = N) :
    HoareTime (program j) (fun v => v = bank ds bs ns)
      (fun v => v = bank (Function.update ds j (GrowingCounterData.advance (N*B) [])) bs ns)
      (10*(N*B)+7*N*bs.length+22*N+7*ns.length+16) := by
  have hh := product_hoare ds j bs ns B N hb hn
  rw [hj] at hh
  have hc := GrowingCounterData.amortized_cost (N*B) []
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hc
  omega

/-- Canonical N and B descriptors give a uniform linear product bound. -/
theorem product_empty_hoare_linear {c : ℕ} (ds : Fin c → List Bool) (j : Fin c) (hj : ds j = [])
    (bs ns : List Bool) (B N : ℕ) (hB : 0 < B) (hb : Counter.value bs = B) (hn : Counter.value ns = N)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program j) (fun v => v = bank ds bs ns)
      (fun v => v = bank (Function.update ds j (GrowingCounterData.advance (N*B) [])) bs ns)
      (53*(N*B)+23) := by
  have wb := GrowingCounterData.canonical_width bs cb
  have wn := GrowingCounterData.canonical_width ns cn
  have lb := Nat.log2_le_self (Counter.value bs)
  have ln := Nat.log2_le_self (Counter.value ns)
  rw [hb] at wb lb
  rw [hn] at wn ln
  have hwb : bs.length ≤ B+1 := by omega
  have hwn : ns.length ≤ N+1 := by omega
  have hm := Nat.mul_le_mul_left N hwb
  have hNB : N ≤ N*B := by nlinarith
  apply (product_empty_hoare ds j hj bs ns B N hb hn).consequence
    (fun _ h => h) (fun _ h => h) _
  nlinarith

/-- A shared larger count bound also handles the padded subtraction descriptor
used for Q-a, without requiring that temporary descriptor to be canonical. -/
theorem product_empty_hoare_bounded {c : ℕ} (ds : Fin c → List Bool) (j : Fin c) (hj : ds j = [])
    (bs ns : List Bool) (B N Q : ℕ) (hB : 0 < B) (hb : Counter.value bs = B) (hn : Counter.value ns = N)
    (hN : N ≤ Q) (wb : bs.length ≤ B+1) (wn : ns.length ≤ Q+1) :
    HoareTime (program j) (fun v => v = bank ds bs ns)
      (fun v => v = bank (Function.update ds j (GrowingCounterData.advance (N*B) [])) bs ns)
      (53*(Q*B)+23) := by
  have hNB := Nat.mul_le_mul_right B hN
  have hm := Nat.mul_le_mul_left N wb
  have hQB : Q ≤ Q*B := by nlinarith
  apply (product_empty_hoare ds j hj bs ns B N hb hn).consequence
    (fun _ h => h) (fun _ h => h) _
  nlinarith

end IntegerMultBounds.Machine.TranslationProduct
