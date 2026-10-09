import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankHeaders

/-! Original geometry pays the complete physical repair-header preparation,
including measurement, arithmetic, record-count synthesis and metadata copies. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersAfterBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersSchedule
open ActiveRepairRankHeadersCommands
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

abbrev volume (s : Shape) (rows : ℕ) := rows*s.recordWidth

theorem geometry_bounds (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    ∀ i, ActivePrefixLayoutHeadersData.originalValues
      (ActivePrefixLayoutHeadersGeometry.inputs s p offset rows) i≤volume s rows := by
  have hpow : 2^s.bits≤volume s rows := by
    unfold volume Shape.recordWidth
    exact (Nat.le_mul_of_pos_right _ hp).trans (Nat.le_mul_of_pos_left _ hrows)
  have hbits : s.bits≤volume s rows := (Nat.lt_two_pow_self (n := s.bits)).le.trans hpow
  have hpay : s.payload≤volume s rows := by
    unfold volume Shape.recordWidth
    exact (Nat.le_mul_of_pos_left _ (by positivity : 0<2^s.bits)).trans (Nat.le_mul_of_pos_left _ hrows)
  have hrow : rows≤volume s rows := by
    unfold volume Shape.recordWidth
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hn : p.n≤p.n*p.b := by nlinarith [p.hb]
  have hq : p.q≤p.f*p.q := by nlinarith [p.hnf]
  have ha := p.activeSize
  have hw := p.compactFits
  have hbr := p.hbq
  have hr := p.hr
  intro i
  fin_cases i
  all_goals dsimp [ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs]
  all_goals unfold Shape.bits at hbits
  all_goals omega

theorem rowBits_bound (d : Inputs s p offset rows) (hp : 0<s.payload) :
    rowBits d≤volume s rows+1 := by
  have hr : rows≤volume s rows := by
    unfold volume Shape.recordWidth
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact (row_log d).trans (Nat.add_le_add_right ((Nat.log2_le_self rows).trans hr) 1)

theorem seeded_bound (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) : Bounded (seeded d) (volume s rows+1) := by
  have ho := geometry_bounds hrows hp hfit
  have hr := rowBits_bound d hp
  intro i
  fin_cases i
  all_goals simp [seeded,scanned,put,Function.update,initial]
  all_goals first | exact (ho _).trans (by omega) | omega

def constant := 3*(300*3^ActiveRepairLayoutRecordsHeadersSchedule.schedule.length)+
  FixedBasePowerDescriptor.constant 2+20000

theorem counted_bound (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    Bounded (ActiveRepairLayoutRecordsHeadersCount.counted d) (2*volume s rows+1) := by
  have ho := geometry_bounds hrows hp hfit
  have hr := rowBits_bound d hp
  have hn := ho 9
  have hq := ho 7
  have hm := ho 5
  dsimp [ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs] at hn hq hm
  have hpow : 2^s.bits≤volume s rows := by
    unfold volume Shape.recordWidth
    exact (Nat.le_mul_of_pos_right _ hp).trans (Nat.le_mul_of_pos_left _ hrows)
  have hbits : s.bits≤volume s rows := (Nat.lt_two_pow_self (n := s.bits)).le.trans hpow
  have hcount : rows*2^s.bits≤volume s rows := by
    unfold volume Shape.recordWidth
    rw [←Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ hp
  intro i
  fin_cases i
  all_goals simp [ActiveRepairLayoutRecordsHeadersCount.counted,ActiveRepairLayoutRecordsHeadersCount.powered,
    ActiveRepairLayoutRecordsHeadersCount.exponent,finished,scanned,put,Function.update,initial]
  all_goals first | exact (ho _).trans (by omega) | omega

theorem runtime_linear (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    ActiveRepairLayoutRecordsHeadersCount.runtime d≤constant*volume s rows := by
  have hv : 0<volume s rows := by unfold volume Shape.recordWidth; positivity
  have hs := scheduleCost_bounded schedule (seeded d) (volume s rows+1) (seeded_bound d hrows hp hfit)
  have hc := scheduleCost_bounded ActiveRepairLayoutRecordsHeadersCount.cleanup
    (ActiveRepairLayoutRecordsHeadersCount.counted d) (2*volume s rows+1) (counted_bound d hrows hp hfit)
  have hr := rowBits_bound d hp
  have hd : cost ActiveRepairLayoutRecordsHeadersCount.difference (finished d)≤200*(2*volume s rows+1)+100 := by
    have hb := counted_bound d hrows hp hfit 18
    have hb' := counted_bound d hrows hp hfit 14
    simp [ActiveRepairLayoutRecordsHeadersCount.counted,ActiveRepairLayoutRecordsHeadersCount.powered,
      ActiveRepairLayoutRecordsHeadersCount.exponent,finished,scanned,put,Function.update] at hb hb'
    simp [cost,ActiveRepairLayoutRecordsHeadersCount.difference,finished,scanned,put,Function.update]
    omega
  have hpow : 2^s.bits≤volume s rows := by
    unfold volume Shape.recordWidth
    exact (Nat.le_mul_of_pos_right _ hp).trans (Nat.le_mul_of_pos_left _ hrows)
  have hcount : rows*2^s.bits≤volume s rows := by
    unfold volume Shape.recordWidth
    rw [←Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ hp
  have hpower := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hpow
  simp only [ActiveRepairLayoutRecordsHeadersCount.cleanup,List.length_cons,List.length_nil] at hc
  norm_num at hc
  unfold ActiveRepairLayoutRecordsHeadersCount.runtime ActiveRepairLayoutRecordsHeadersRun.cost constant
  simp only [ActiveRepairLayoutRecordsHeadersCount.cleanup]
  nlinarith

theorem runs_linear {a : ℕ} (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    HoareTime (ActiveRepairLayoutRecordsHeadersCount.program (a := a))
      (fun v => v=bank (initial d)) (fun v => v=bank (ActiveRepairLayoutRecordsHeadersCount.ready d))
      (constant*volume s rows) :=
  (ActiveRepairLayoutRecordsHeadersCount.prepares d).consequence (fun _ h => h) (fun _ h => h)
    (runtime_linear d hrows hp hfit)

theorem words_canonical (d : Inputs s p offset rows) :
    ∀ i, GrowingCounterData.Canonical (ActiveRepairLayoutRecordsBankHeaders.words d i) := by
  intro i
  fin_cases i
  · exact d.hc 0
  · exact d.hc 1
  · exact d.hc 2
  · exact d.hc 3
  · exact d.hc 4
  · exact d.hc 5
  · exact d.hc 6
  · exact d.hc 11
  · exact RecursiveChildQuotientsConstant.bits_canonical (p.n*p.q+p.q)
  · exact RecursiveChildQuotientsConstant.bits_canonical (s.bits+rowBits d)
  · exact d.hc 7
  · exact d.hc 9
  · exact d.hc 10
  · exact RecursiveChildQuotientsConstant.bits_canonical (p.n+1)
  · exact d.hc 8

theorem words_bound (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    ∀ i, Counter.value (ActiveRepairLayoutRecordsBankHeaders.words d i)≤2*volume s rows+1 := by
  have ho := geometry_bounds hrows hp hfit
  have hn := ho 9
  have hq := ho 7
  have hm := ho 5
  dsimp [ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs] at hn hq hm
  have hr := rowBits_bound d hp
  have hpow : 2^s.bits≤volume s rows := by
    unfold volume Shape.recordWidth
    exact (Nat.le_mul_of_pos_right _ hp).trans (Nat.le_mul_of_pos_left _ hrows)
  have hbits : s.bits≤volume s rows := (Nat.lt_two_pow_self (n := s.bits)).le.trans hpow
  intro i
  fin_cases i
  · change Counter.value (d.hs 0)≤_
    rw [d.hv]
    exact (ho 0).trans (by omega)
  · change Counter.value (d.hs 1)≤_
    rw [d.hv]
    exact (ho 1).trans (by omega)
  · change Counter.value (d.hs 2)≤_
    rw [d.hv]
    exact (ho 2).trans (by omega)
  · change Counter.value (d.hs 3)≤_
    rw [d.hv]
    exact (ho 3).trans (by omega)
  · change Counter.value (d.hs 4)≤_
    rw [d.hv]
    exact (ho 4).trans (by omega)
  · change Counter.value (d.hs 5)≤_
    rw [d.hv]
    exact (ho 5).trans (by omega)
  · change Counter.value (d.hs 6)≤_
    rw [d.hv]
    exact (ho 6).trans (by omega)
  · change Counter.value (d.hs 11)≤_
    rw [d.hv]
    exact (ho 11).trans (by omega)
  · change Counter.value (RecursiveChildQuotientsConstant.bits (p.n*p.q+p.q))≤_
    rw [RecursiveChildQuotientsConstant.bits_value]
    omega
  · change Counter.value (RecursiveChildQuotientsConstant.bits (s.bits+rowBits d))≤_
    rw [RecursiveChildQuotientsConstant.bits_value]
    omega
  · change Counter.value (d.hs 7)≤_
    rw [d.hv]
    exact (ho 7).trans (by omega)
  · change Counter.value (d.hs 9)≤_
    rw [d.hv]
    exact (ho 9).trans (by omega)
  · change Counter.value (d.hs 10)≤_
    rw [d.hv]
    exact (ho 10).trans (by omega)
  · change Counter.value (RecursiveChildQuotientsConstant.bits (p.n+1))≤_
    rw [RecursiveChildQuotientsConstant.bits_value]
    omega
  · change Counter.value (d.hs 8)≤_
    rw [d.hv]
    exact (ho 8).trans (by omega)

theorem copies_runtime_linear (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    ActiveRepairLayoutRecordsBankHeaders.runtime d≤(constant+451)*volume s rows := by
  have hv : 0<volume s rows := by unfold volume Shape.recordWidth; positivity
  have hh := FixedHeaderBankCopy.cost_linear (ActiveRepairLayoutRecordsBankHeaders.words d)
    (2*volume s rows+1) (by omega) (words_canonical d) (words_bound d hrows hp hfit)
  have hc := runtime_linear d hrows hp hfit
  unfold ActiveRepairLayoutRecordsBankHeaders.runtime
  nlinarith

theorem copies_runs_linear {a : ℕ} (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    HoareTime (ActiveRepairLayoutRecordsBankHeaders.program (a := a))
      (fun v => v=ActiveRepairLayoutRecordsBankHeaders.input d)
      (fun v => v=ActiveRepairLayoutRecordsBankHeaders.output d)
      ((constant+451)*volume s rows) :=
  (ActiveRepairLayoutRecordsBankHeaders.runs d).consequence (fun _ h => h) (fun _ h => h)
    (copies_runtime_linear d hrows hp hfit)

theorem original_runs_linear {a : ℕ} (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    HoareTime (ActiveRepairLayoutRecordsHeadersCount.program (a := a))
      (fun v => v=ActiveRepairLayoutRecordsHeadersRun.originalInput d)
      (fun v => v=bank (ActiveRepairLayoutRecordsHeadersCount.ready d))
      (constant*volume s rows) := by
  have h := runs_linear (a := a) d hrows hp hfit
  rw [ActiveRepairLayoutRecordsHeadersRun.input_eq] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersAfterBudget
