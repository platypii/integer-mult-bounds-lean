module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedLeafRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodParentSetup
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

/-! Charge weighted leaves at their actual terminal widths and volumes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine RecursiveInterchangeLayout M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def weightedLeafRate [M8.Machine.Net] (tapes push : ℕ) (L : ℝ) : ℝ :=
  (1+186*(push : ℝ))*((3*(210*(2*((prime.size : ℝ)+1)^2)+16120+100)+387)+
    2*(|LeafCore.C| * L*((tapes : ℝ)+5)))+(12000*(1+186*(push : ℝ))+125+550)

theorem weightedLeafCost_le [M8.Machine.Net] (N width tapes push : ℕ) {L : ℝ}
    (widthBound : ((max 1 width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L) :
    (weightedLeafCost N width tapes push : ℝ) ≤ weightedLeafRate tapes push L*N := by
  have core := RevBudget.coreCost_le N width widthBound
  unfold weightedLeafCost weightedLeafBodyCost weightedLeafRate
  push_cast
  calc
    _ ≤ (1+186*(push : ℝ))*((3*(210*(2*((prime.size : ℝ)+1)^2)+16120+100)+387)*N+
        2*((|LeafCore.C| * N*L)*((tapes : ℝ)+5)))+(12000*(1+186*(push : ℝ))+125)*N + 550*N := by gcongr
    _ = _ := by ring

/-- The packed leaf pays the archive charge from a single radix factor.
The terminal recurrence can use its usual descriptor volume. -/
theorem packedWeightedLeafCost_le [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (tapes push rate : ℕ) {L : ℝ}
    (widthBound : ((max 1 v.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L) :
    ((weightedLeafCost (volume prime v) v.width tapes push + rate*prime^v.width : ℕ) : ℝ) ≤
      (weightedLeafRate tapes push L+rate)*volume prime v := by
  have qpos := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos
  have pre := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have radix : prime^v.width ≤ volume prime v :=
    (Nat.le_mul_of_pos_left _ pre).trans ((Nat.le_mul_of_pos_right _ positive.2.2.2.1).trans
      ((Nat.le_mul_of_pos_right _ (pow_pos qpos _)).trans (Nat.le_mul_of_pos_right _ positive.2.2.2.2)))
  rw [Nat.cast_add,add_mul]
  exact add_le_add (weightedLeafCost_le _ _ _ _ widthBound) (by exact_mod_cast Nat.mul_le_mul_left rate radix)

private theorem weightedLeafRate_linear [M8.Machine.Net] (tapes push rate : ℕ) {w : ℝ}
    (one : 1 ≤ w) : weightedLeafRate tapes push w + rate ≤ (weightedLeafRate tapes push 1 + rate)*w := by
  let base := weightedLeafRate tapes push 0 + rate
  have hb : 0 ≤ base := by dsimp [base,weightedLeafRate]; positivity
  have linear : (weightedLeafRate tapes push 1 + rate)*w =
      (weightedLeafRate tapes push w + rate) + base*(w-1) := by
    unfold base weightedLeafRate
    ring
  rw [linear]
  exact le_add_of_nonneg_right (mul_nonneg hb (sub_nonneg.mpr one))

/-- Successive good records retain the parent's volume. Their linear overheads
add, and the terminal interchange pays for the width left after all gaps. -/
private theorem chainCost_of_terminal {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (rate : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    (time [] child : ℝ) ≤ rate*volume prime child →
    (time records v : ℝ) ≤ (rate+(records.map overhead).sum)*(volume prime v : ℝ) := by
  intro child terminal
  have same : volume prime child = volume prime v := rankDescriptor_volume v (Nat.sub_add_cancel fits).symm
  have chain := rankDescriptor_chain_time gap overhead time step records v fits
  calc
    (time records v : ℝ) ≤ ((time [] child + (records.map overhead).sum * volume prime v : ℕ) : ℝ) :=
      Nat.cast_le.mpr chain
    _ ≤ _ := by
      push_cast
      rw [add_mul]
      apply add_le_add_left
      rw [← same]
      exact terminal

theorem weightedLeaf_chain_cost [M8.Machine.Net] {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (tapes push : ℕ) (L : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    time [] child ≤ weightedLeafCost (volume prime child) child.width tapes push →
    ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
    (time records v : ℝ) ≤ (weightedLeafRate tapes push L+(records.map overhead).sum)*(volume prime v : ℝ) := by
  intro child terminal widthBound
  exact chainCost_of_terminal gap overhead time step records v fits _
    ((Nat.cast_le.mpr terminal).trans (weightedLeafCost_le _ _ _ _ widthBound))

/-- A good record reads the same active coordinate from both archives.
The rank bounds both offsets, uniformly in the coordinate and terminal width. -/
theorem packedWeightedLeaf_chain_cost [M8.Machine.Net] {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (positive : v.Positive) {rank : ℕ} (i : Fin rank) (tapes push : ℕ) (L : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    let factor := 2*(prime.size+1)^2
    let rate := (1000*(prime+1)+16*(rank-1))*factor
    time [] child ≤ weightedLeafCost (volume prime child) child.width tapes push+
      ((1000*(prime+1)+8*(i.val+i.val))*factor)*prime^child.width →
    ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
    (time records v : ℝ) ≤ (weightedLeafRate tapes push L+rate+(records.map overhead).sum)*
      (volume prime v : ℝ) := by
  intro child factor rate terminal widthBound
  have power := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos (records.map gap).sum
  have childPos : child.Positive := ⟨positive.1,positive.2.1,positive.2.2.1,
    Nat.mul_pos (Nat.mul_pos power positive.2.2.2.1) power,positive.2.2.2.2⟩
  have indexBound : 8*(i.val+i.val) ≤ 16*(rank-1) := by have := i.isLt; omega
  have bounded := terminal.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (prime^child.width)
    (Nat.mul_le_mul_right factor (Nat.add_le_add_left indexBound _))) _)
  exact chainCost_of_terminal gap overhead time step records v fits _
    ((Nat.cast_le.mpr bounded).trans (packedWeightedLeafCost_le child childPos tapes push rate widthBound))

/-- One nonterminal good record pays its child's actual budget plus a
linear toll on the parent volume, uniformly in the atom width. -/
theorem goodRecord_descriptor_step {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Host.Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (r g digits : ℕ) (positiveRank : 0 < r+g) :
    ∃ overhead : ℕ, ∀ (time : Descriptor → ℕ) (v : Descriptor) w,
      v.Positive → v.width = (r+g)*(w+1) →
      let gap := g*(w+1)
      let child := rankDescriptor prime (v.width-gap) gap v
      let M := prime^(w+1)
      let H := M.size
      let W := v.beforeRows*v.rows*v.beforeH*v.between*v.afterD
      let K := digits*H+1
      let middle := (((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1+
        dimensionTime H K (g+g))+(time child+2+(2*(r*H+r*H+((g+g)*H+K))+7))
      1+goodIncomingTime body machine prime w W H W.size r (Nat.le_add_right r g)+middle+
        (1+goodOutgoingTime body machine prime w W H W.size r (Nat.le_add_right r g)) ≤
          time child+overhead*volume prime v := by
  obtain ⟨c,record⟩ := goodRecordTime_volume_le body machine r g digits rfl positiveRank (Nat.le_add_right r g)
  refine ⟨c,?_⟩
  intro time v w pos split gap child M H W K middle
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1)
    pos.2.2.1) pos.2.2.2.1) pos.2.2.2.2
  have size : M^((r+g)+(r+g))*W = volume prime v := by
    simp only [volume,split,M,W,pow_add]
    ring
  exact size ▸ record w W (time child) hW

/-- Exact nested good-record budget, with gaps counted in atoms. -/
noncomputable def goodRecordChainTime {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Host.Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (digits d w : ℕ) (terminal : Descriptor → ℕ) : List ℕ → Descriptor → ℕ
  | [], v => terminal v
  | g :: gs, v =>
    let r := d+gs.sum
    let H := (prime^(w+1)).size
    let K := digits*H+1
    let W := v.beforeRows*v.rows*v.beforeH*v.between*v.afterD
    let gap := g*(w+1)
    let child := rankDescriptor prime (v.width-gap) gap v
    let budget := goodRecordChainTime body machine digits d w terminal gs child
    let middle := (((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1+
      dimensionTime H K (g+g))+(budget+2+(2*(r*H+r*H+((g+g)*H+K))+7))
    1+goodIncomingTime body machine prime w W H W.size r (Nat.le_add_right r g)+middle+
      (1+goodOutgoingTime body machine prime w W H W.size r (Nat.le_add_right r g))

/-- All setup and return tolls in the concrete chain are linear in the
original volume. At the terminal call exactly d atoms remain. -/
theorem goodRecordChainTime_le {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Host.Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (digits d : ℕ) (gaps : List ℕ)
    (valid : ∀ pre g rest, gaps = pre ++ g :: rest → 0 < d+rest.sum+g) :
    ∃ overhead : ℕ, ∀ (v : Descriptor) w (terminal : Descriptor → ℕ),
      v.Positive → v.width = (d+gaps.sum)*(w+1) →
      goodRecordChainTime body machine digits d w terminal gaps v ≤
        terminal (rankDescriptor prime (d*(w+1)) (gaps.sum*(w+1)) v) + overhead*volume prime v := by
  induction gaps with
  | nil =>
    refine ⟨0,?_⟩
    intro v w terminal pos width
    have eq : rankDescriptor prime (d*(w+1)) 0 v = v := by
      have h : d*(w+1) = v.width := by simpa using width.symm
      cases v
      simp [rankDescriptor,h]
    simp [goodRecordChainTime,eq]
  | cons g gs ih =>
    have hp := valid [] g gs rfl
    obtain ⟨a,first⟩ := goodRecord_descriptor_step body machine (d+gs.sum) g digits hp
    obtain ⟨b,tail⟩ := ih (fun pre k rest h => valid (g::pre) k rest (by simp [h]))
    refine ⟨a+b,?_⟩
    intro v w terminal pos width
    let gap := g*(w+1)
    let child := rankDescriptor prime (v.width-gap) gap v
    have split : v.width = (d+gs.sum+g)*(w+1) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using width
    have cw : v.width-gap = (d+gs.sum)*(w+1) := by rw [split,Nat.add_mul]; simp [gap]
    have power := pow_pos Networks.Shared50ModularControl.prime_prime.pos gap
    have childPos : child.Positive := ⟨pos.1,pos.2.1,pos.2.2.1,Nat.mul_pos (Nat.mul_pos power pos.2.2.2.1) power,pos.2.2.2.2⟩
    have same : volume prime child = volume prime v := rankDescriptor_volume v (by rw [cw,split,Nat.add_mul])
    have endEq : rankDescriptor prime (d*(w+1)) (gs.sum*(w+1)) child =
        rankDescriptor prime (d*(w+1)) ((g::gs).sum*(w+1)) v := by
      simp [child,rankDescriptor,gap,List.sum_cons,Nat.add_mul,pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    have inner := tail child w terminal childPos cw
    rw [same,endEq] at inner
    have outer := first (goodRecordChainTime body machine digits d w terminal gs) v w pos split
    exact outer.trans ((Nat.add_le_add_right inner _).trans_eq (by rw [Nat.add_mul]; omega))

/-- For a rank-one terminal child the quotient atom has the full remaining
width. Both packed archive indices are zero. Price the incoming word, child
setup, packed leaf and outgoing word together on the parent descriptor. -/
theorem rankOneRecordLeaf_cost [M8.Machine.Net] {T A : ℕ} {U : Type}
    (machine : Fin 55 ↪ Fin T) (g digits tapes push : ℕ) :
    ∃ overhead : ℕ, ∀ (v : Descriptor) w (L : ℝ), v.Positive → v.width = (1+g)*(w+1) →
      let child := rankDescriptor prime (w+1) (g*(w+1)) v
      let M := prime^(w+1)
      let H := Nat.size M
      let W := v.beforeRows*v.rows*v.beforeH*v.between*v.afterD
      let K := digits*H+1
      let budget := weightedLeafCost (volume prime child) child.width tapes push+
        (1000*(prime+1)*(2*(prime.size+1)^2))*M
      let middle := (((List.finRange 1).map fun i => childWeightTime prime w H i.val).sum+1+
        dimensionTime H K (g+g))+(budget+2+(2*(1*H+1*H+((g+g)*H+K))+7))
      ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
      ((1+goodIncomingTime (P := Empty) (U := U) (A := A) Empty.elim machine prime w W H W.size 1
        (Nat.le_add_right 1 g)+middle+(1+goodOutgoingTime (P := Empty) (U := U) (A := A) Empty.elim
          machine prime w W H W.size 1 (Nat.le_add_right 1 g)) : ℕ) : ℝ) ≤
        (weightedLeafRate tapes push L+overhead)*volume prime v := by
  obtain ⟨c,adapter⟩ := goodRecord_descriptor_step (P := Empty) (U := U) (A := A) Empty.elim machine
    1 g digits (by omega)
  let rate := 1000*(prime+1)*(2*(prime.size+1)^2)
  refine ⟨rate+c,?_⟩
  intro v w L pos split child M H W K budget middle widthBound
  have same : volume prime child = volume prime v := rankDescriptor_volume v (by rw [split,Nat.add_mul,one_mul])
  have power := pow_pos Networks.Shared50ModularControl.prime_prime.pos (g*(w+1))
  have childPos : child.Positive := ⟨pos.1,pos.2.1,pos.2.2.1,Nat.mul_pos (Nat.mul_pos power pos.2.2.2.1) power,pos.2.2.2.2⟩
  have leaf := packedWeightedLeafCost_le child childPos tapes push rate widthBound
  change (budget : ℝ) ≤ _ at leaf
  rw [same] at leaf
  have parent := adapter (fun _ => budget) v w pos split
  apply (Nat.cast_le.mpr parent).trans
  push_cast
  linarith only [leaf]

/-- Uniform terminal cost on the original payload volume. -/
noncomputable def packedCoordinatesTime [M8.Machine.Net] (d V w tapes push entryTapes returnTapes : ℕ) : ℕ :=
  d*(weightedLeafCost V (w+1) tapes push+
    ((1000*(prime+1)+16*(d-1))*(2*(prime.size+1)^2))*prime^(w+1)+
    (1800*(entryTapes+5)+200*(returnTapes+5)+15)*V)+1

noncomputable def packedCoordinatesRate [M8.Machine.Net] (D tapes push entryTapes returnTapes : ℕ) : ℝ :=
  let scans := (1000*(prime+1)+16*(D-1))*(2*(prime.size+1)^2)
  let frame := 1800*(entryTapes+5)+200*(returnTapes+5)+15
  weightedLeafRate tapes push 1 + (scans+frame+1 : ℕ)

/-- The full coordinate loop, including the return frames and final instruction,
costs at most a constant times active width times payload volume. -/
theorem packedCoordinates_linear [M8.Machine.Net] (d D V w tapes push entryTapes returnTapes : ℕ)
    (active : 0 < d) (rankBound : d ≤ D) (radix : prime^(w+1) ≤ V) :
    let scans := (1000*(prime+1)+16*(D-1))*(2*(prime.size+1)^2)
    let frame := 1800*(entryTapes+5)+200*(returnTapes+5)+15
    (packedCoordinatesTime d V w tapes push entryTapes returnTapes : ℝ) ≤
      (weightedLeafRate tapes push 1 + (scans+frame+1 : ℕ))*(d*(w+1) : ℕ)*V := by
  intro scans frame
  let atom : ℝ := (w+1 : ℕ)
  have one : 1 ≤ atom := by dsimp [atom]; exact_mod_cast Nat.succ_pos w
  have exp : ((max 1 (w+1) : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ atom := by
    rw [max_eq_right (Nat.succ_pos w)]
    simpa [atom] using Real.rpow_le_rpow_of_exponent_le one M8.Machine.BudgetBound.exponent_range.2.le
  have leaf := weightedLeafCost_le V (w+1) tapes push exp
  have scan : (1000*(prime+1)+16*(d-1))*(2*(prime.size+1)^2)*prime^(w+1) ≤ scans*V := by
    dsimp [scans]
    gcongr
  have last : (1 : ℝ) ≤ d*(V : ℝ) := by
    exact_mod_cast Nat.mul_pos active ((pow_pos Networks.Shared50ModularControl.prime_prime.pos _).trans_le radix)
  change ((d*(_+_+frame*V)+1 : ℕ) : ℝ) ≤ _
  push_cast
  calc
    _ ≤ (d : ℝ)*(weightedLeafRate tapes push atom*V + (scans*V : ℕ) + frame*(V : ℝ)) + d*V := by
      gcongr <;> exact_mod_cast scan
    _ = ((weightedLeafRate tapes push atom + (scans+frame+1 : ℕ))*d)*V := by push_cast; ring
    _ ≤ (((weightedLeafRate tapes push 1 + (scans+frame+1 : ℕ))*atom)*d)*V := by
      gcongr
      exact weightedLeafRate_linear tapes push (scans+frame+1) one
    _ = _ := by dsimp [atom]; push_cast; ring

/-- Apply the coordinate execution budget in the units of the descriptor
recurrence. All dependence on the active rank is bounded by the rank cap. -/
theorem packedCoordinates_steps_linear [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (d D w tapes push entryTapes returnTapes steps : ℕ) (active : 0 < d) (rankBound : d ≤ D)
    (width : v.width = d*(w+1))
    (run : steps ≤ packedCoordinatesTime d (volume prime v) w tapes push entryTapes returnTapes) :
    (steps : ℝ) ≤ packedCoordinatesRate D tapes push entryTapes returnTapes*v.width*volume prime v := by
  have qpos := Networks.Shared50ModularControl.prime_prime.pos
  have atom : w+1 ≤ v.width := width ▸ Nat.le_mul_of_pos_left _ active
  have pre := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have radix : prime^(w+1) ≤ volume prime v := (Nat.pow_le_pow_right qpos atom).trans
    ((Nat.le_mul_of_pos_left _ pre).trans ((Nat.le_mul_of_pos_right _ positive.2.2.2.1).trans
      ((Nat.le_mul_of_pos_right _ (pow_pos qpos _)).trans (Nat.le_mul_of_pos_right _ positive.2.2.2.2))))
  exact (Nat.cast_le.mpr run).trans (width ▸ packedCoordinates_linear d D _ w tapes push
    entryTapes returnTapes active rankBound radix)

/-- Install the verified packed coordinate budget at the end of the record
list. Only the parent volume occurs in the resulting bound. -/
theorem goodRecordChain_packedTime [M8.Machine.Net] {P U : Type} [Fintype P] {T A : ℕ}
    (body : P → Host.Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (digits d : ℕ) (gaps : List ℕ)
    (valid : ∀ pre g rest, gaps = pre ++ g :: rest → 0 < d+rest.sum+g) :
    ∃ overhead : ℕ, ∀ (v : Descriptor) w tapes push entryTapes returnTapes, v.Positive →
      v.width = (d+gaps.sum)*(w+1) →
      let budget := fun child => packedCoordinatesTime d (volume prime child) w tapes push entryTapes returnTapes
      goodRecordChainTime body machine digits d w budget gaps v ≤ budget v + overhead*volume prime v := by
  obtain ⟨c,chain⟩ := goodRecordChainTime_le body machine digits d gaps valid
  refine ⟨c,?_⟩
  intro v w tapes push entryTapes returnTapes pos width budget
  have same := rankDescriptor_volume (M := prime) v (width.trans (Nat.add_mul ..))
  simpa only [budget,same] using chain v w budget pos width

/-- The terminal loop pays a linear-volume toll per active coordinate.
Apply the stopped-chain bound at the atom width left in each coordinate. -/
theorem packedCoordinates_chain_cost [M8.Machine.Net] {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (d w tapes push entryTapes returnTapes : ℕ) (L : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    let V := volume prime child
    let scans : ℕ := (1000*(prime+1)+16*(d-1))*(2*(prime.size+1)^2)
    let frame := 1800*(entryTapes+5)+200*(returnTapes+5)+15
    child.Positive → child.width = d*(w+1) →
    ((max 1 (w+1) : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
    time [] child ≤ packedCoordinatesTime d V w tapes push entryTapes returnTapes →
    (time records v : ℝ) ≤ (d*(weightedLeafRate tapes push L+scans+frame)+1+(records.map overhead).sum)*
      (volume prime v : ℝ) := by
  intro child V scans frame positive width widthBound terminal
  apply chainCost_of_terminal gap overhead time step records v fits
  apply (Nat.cast_le.mpr terminal).trans
  have volPos : 1 ≤ V := RecursiveAffinePrepare.volume_positive
    Networks.Shared50ModularControl.prime_prime.two_le child positive
  have one : (1 : ℝ) ≤ V := by exact_mod_cast volPos
  by_cases zero : d = 0
  · simpa only [packedCoordinatesTime,zero,Nat.zero_mul,Nat.zero_add,Nat.cast_zero,Nat.cast_one,zero_mul,zero_add,one_mul] using one
  have atom : w+1 ≤ child.width := width ▸ Nat.le_mul_of_pos_left _ (by omega)
  have pre := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have powPos := pow_pos Networks.Shared50ModularControl.prime_prime.pos child.width
  have radix : prime^(w+1) ≤ V := (Nat.pow_le_pow_right Networks.Shared50ModularControl.prime_prime.pos atom).trans
    ((Nat.le_mul_of_pos_left _ pre).trans ((Nat.le_mul_of_pos_right _ positive.2.2.2.1).trans
      ((Nat.le_mul_of_pos_right _ powPos).trans (Nat.le_mul_of_pos_right _ positive.2.2.2.2))))
  have scan : ((scans*(prime^(w+1)) : ℕ) : ℝ) ≤ scans*(V : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left scans radix
  have leaf := weightedLeafCost_le V (w+1) tapes push widthBound
  change ((d*(weightedLeafCost V (w+1) tapes push+scans*prime^(w+1)+frame*V)+1 : ℕ) : ℝ) ≤ _
  push_cast
  calc
    _ ≤ (d : ℝ)*(weightedLeafRate tapes push L*V+scans*V+frame*V)+V := by
      push_cast at scan
      gcongr
    _ = _ := by ring

/-- Every coordinate call sees the full payload volume at one atom's width.
Charge both host frame changes, the packed archive scans at their actual indices, and the empty
instruction ending the sequence once. -/
theorem weightedCoordinates_cost [M8.Machine.Net] {r : ℕ} (v : Descriptor) (width : v.width = r)
    (positive : v.Positive) (w tapes push entryTapes returnTapes : ℕ) :
    let M := prime^(w+1)
    let view := fun i : Fin r => {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w+1}
    let factor := 2*(prime.size+1)^2
    let V := volume M v
    let frame := 1800*(entryTapes+5)+200*(returnTapes+5)+15
    let cost := fun i : Fin r => (1+(1800*V*(entryTapes+5)+6))+(1+(weightedLeafCost (volume prime (view i)) (w+1) tapes push+
      ((1000*(prime+1)+8*(i.val+i.val))*factor)*M))+(1+(200*V*(returnTapes+5)+6))
    ((List.finRange r).map cost).sum+1 ≤
      packedCoordinatesTime r V w tapes push entryTapes returnTapes := by
  intro M view factor V frame cost
  let bound := weightedLeafCost (volume M v) (w+1) tapes push+((1000*(prime+1)+16*(r-1))*factor)*M+frame*V
  have volPos : 0 < V := by
    dsimp [V,volume,M]
    obtain ⟨_,_,_,_,_⟩ := positive
    have := Networks.Shared50ModularControl.prime_prime.pos
    positivity
  have each (i : Fin r) : cost i ≤ bound := by
    have same := RecursiveInterchangeLayout.child_volume_div M 1 1 v i i.rev
      (by simpa using width) (by decide) (one_dvd _)
    have vol : volume prime (view i) = volume M v := by
      simpa [view,M,volume,RecursiveInterchangeLayout.child] using same
    have indexBound : 8*(i.val+i.val) ≤ 16*(r-1) := by have := i.isLt; omega
    dsimp only [cost,bound]
    rw [vol]
    have scans := Nat.mul_le_mul_right M (Nat.mul_le_mul_right factor (Nat.add_le_add_left indexBound (1000*(prime+1))))
    dsimp only [frame]
    simp only [Nat.add_mul,Nat.mul_assoc,Nat.mul_comm V] at *
    nlinarith only [scans,volPos]
  have total (is : List (Fin r)) : (is.map cost).sum ≤ is.length*bound := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
        Nat.add_le_add (each i) ih
  change _ ≤ r*bound+1
  simpa only [List.length_finRange] using Nat.add_le_add_right (total (List.finRange r)) 1

end IntegerMultBounds.MathlibTM2.Cover.Fallback
