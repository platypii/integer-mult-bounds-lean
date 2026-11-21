module

public import IntegerMultBounds.MathlibTM2.M6.BitHosting
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Charts

/-!
# One class run of an invocation on the parent's roles

The parent node has `5W = 142080` roles (`Role`, `card_role`): a replica, a bank (`2·pair + side`),
a port and one of five row classes. The class-`d` run of the invocation at stage `n` in replica `r`
(`invoke n r d`) runs the word on 661 registers:
* data register `j < 222` is the role of its pair side and port in class `d`, read through the
  port's stage route;
* helper `h` is hosted on the role of its slot's family in class `hostClass σ d`, read through the
  slot's helper chart;
* the private register 661 starts and ends at zero.
It reads each register through its chart, runs the framed word (forward at even stages, the
reflected call at odd ones) and writes each register back through the inverse chart. The 661
owners are distinct (`owner_injective`).

On arbitrary dirty roles:
* `invoke_side_zero`, `invoke_side_one`: both sides of the active pair change between their
  stage frames, and the receiving side (side one forward, side zero reverse) also receives the
  other side;
* `invoke_host`: a hosted helper's role changes by the exchange on its slot, the helper's restored
  value in its final frame;
* `invoke_other`: every other role is unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitOccurrences
open IntegerMultBounds.MathlibTM2.M6.BitSchedule
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

/-- A role of the parent node: replica, bank `2·pair + side`, port and row class. -/
structure Role where
  replica : Fin 32
  bank : Fin 8
  port : Fin 111
  cls : Fin 5
  deriving DecidableEq, Fintype

def roleEquiv : Role ≃ Fin 32 × Fin 8 × Fin 111 × Fin 5 where
  toFun ρ := (ρ.replica, ρ.bank, ρ.port, ρ.cls)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The node has `5W = 142080` roles. -/
theorem card_role : Fintype.card Role = 142080 := by
  rw [Fintype.card_congr roleEquiv]
  simp

/-- The streams of all roles. -/
abbrev State := Role → Stream

/-- A coordinate change on both address halves. -/
def bar (R : Matrix Axis Axis ℚ) : Matrix (Axis ⊕ Axis) (Axis ⊕ Axis) ℚ := fromBlocks R 0 0 R

/-! ### Slots by stage and helper -/

def noSlot : Slot := ⟨0, 0, 0, 0, 0⟩

/-- The slot that hosts helper `h` at stage `n`. -/
def slotOf (n h : ℕ) : Slot := (slots.filter (·.stage = n)).getD h noSlot

theorem slotOf_spec (n : ℕ) (hn : n < 9) (h : ℕ) (hh : h < 439) :
    slotOf n h ∈ slots ∧ (slotOf n h).stage = n ∧ (slotOf n h).helper = h := by
  have hL := slot_helpers n hn
  have hlen : (slots.filter (·.stage = n)).length = 439 := by
    have := congrArg List.length hL
    simpa using this
  have hget : slotOf n h = (slots.filter (·.stage = n))[h]'(by omega) := by
    rw [slotOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hmem := List.getElem_mem (l := slots.filter (·.stage = n)) (n := h) (by omega)
  rw [← hget, List.mem_filter] at hmem
  refine ⟨hmem.1, by simpa using hmem.2, ?_⟩
  have := congrArg (fun l => l[h]?) hL
  simp only [List.getElem?_map, List.getElem?_range hh] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [hget, this]

theorem pairOf_lt : ∀ i < 10, pairOf i < 4 := by
  decide +kernel

theorem activePair_lt (n : Fin 9) : activePair n.val < 4 := by
  have := n.isLt
  simp only [activePair]
  omega

/-! ### Owners and charts -/

/-- The side holding word register `j < 222`: the source on side zero forward and side one
reverse. -/
def regSide (n j : ℕ) : ℕ := if j < 111 then n % 2 else 1 - n % 2

/-- The role of a pair side and port in a class. -/
def sideRole (n : Fin 9) (r : Fin 32) (d : Fin 5) (side : ℕ) (t : Fin 111) : Role :=
  ⟨r, ⟨(2 * activePair n.val + side) % 8, Nat.mod_lt _ (by norm_num)⟩, t, d⟩

/-- The host role of helper `h` in the class-`d` run. -/
def hostRole (n : Fin 9) (r : Fin 32) (d : Fin 5) (h : ℕ) : Role :=
  ⟨r, ⟨(2 * pairOf (slotOf n h).idle + (slotOf n h).copy / 111) % 8, Nat.mod_lt _ (by norm_num)⟩,
    ⟨(slotOf n h).copy % 111, Nat.mod_lt _ (by norm_num)⟩,
    ⟨hostClass (slotOf n h) d.val, Nat.mod_lt _ (by norm_num)⟩⟩

def owner (n : Fin 9) (r : Fin 32) (d : Fin 5) (j : ℕ) : Role :=
  if j < 222 then sideRole n r d (regSide n j) ⟨j % 111, Nat.mod_lt _ (by norm_num)⟩
  else hostRole n r d (j - 222)

theorem slotPos_le (n : ℕ) (hn : n < 9) (h : ℕ) (hh : h < 439) : slotPos (slotOf n h) ≤ 55 := by
  have := slot_in_pending _ (slotOf_spec n hn h hh).1
  simp only [slotPos]
  omega

/-- The chart of register `j` at stage `n`. -/
noncomputable def chart (n : Fin 9) (j : ℕ) : Matrix Axis Axis ℚ :=
  if j < 222 then (port (j % 111)).stageRoute n
  else if hx : slotPos (slotOf n (j - 222)) ≤ 55 then
    (port ((slotOf n (j - 222)).copy % 111)).helperChart _ hx
  else 1

/-- The registers of the class-`d` run, read through their charts. -/
noncomputable def registers (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State) (j : ℕ) : Stream :=
  if j < 661 then along (bar (chart n j)) (X (owner n r d j)) else 0

/-- The framed word at stage `n`: forward at even stages, the reflected call at odd ones. -/
noncomputable def runWord (n : Fin 9) (v : ℕ → Stream) : ℕ → Stream :=
  if n.val % 2 = 1 then reverseRun n v else Framed.execute (forwardFrame n) v

private theorem windowChange (n : ℕ) (U V : Matrix (Fin 8) (Fin 8) ℚ) :
    exchange (windowProj n U) * exchange (windowProj n V) =
      exchange (Matrix.fromBlocks (U+V-(U*V+U*V)) 0 0 (0 : Matrix Exterior Exterior ℚ)) := by
  have product (A B : Matrix Axis Axis ℚ) :
      exchange A * exchange B = exchange (A+B-(A*B+A*B)) := by
    simp only [exchange,Matrix.fromBlocks_multiply,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
    rw [Matrix.fromBlocks_inj]
    exact ⟨by abel,by abel,by abel,by abel⟩
  rw [product]
  congr 1
  simp only [windowProj,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
    zero_add,add_zero,lower_mul_self]
  ext (i|i) (j|j) <;> simp

/-- In register order the reflected call has the same endpoint as the
forward word. Stage parity is already accounted for by the side owners. -/
theorem runWord_forward (n : Fin 9) (v : ℕ → Stream) (high : ∀ j, 661 ≤ j → v j = 0) :
    runWord n v = Framed.execute (forwardFrame n) v := by
  unfold runWord
  split
  · funext j
    have changes (t : Fin 111) :
        let P := (port t.val).lineProj
        exchange (windowProj n P) * exchange (windowProj n 1) =
            exchange (windowProj n 0) * exchange (windowProj n (1-P)) ∧
        exchange (windowProj n P) * exchange (windowProj n (1-P)) =
            exchange (windowProj n 0) * exchange (windowProj n 1) := by
      intro P
      have idem : P*P = P := PortCertificate.lineProj_mul_self (port_checked _ t.isLt)
      simp only [windowChange,Matrix.zero_mul,Matrix.mul_one,Matrix.mul_sub,idem,sub_self,zero_add,sub_zero]
      constructor <;> congr 2 <;> abel
    by_cases src : j < 111
    · rw [reverse_source n v j src,forward_source n v high j src,(changes ⟨j,src⟩).1]
    by_cases dst : j < 222
    · let t : Fin 111 := ⟨j-111,by omega⟩
      have idx : j = 111+t.val := by dsimp [t]; omega
      rw [idx,reverse_target n v t.val t.isLt,forward_target n v high t.val t.isLt,(changes t).1,(changes t).2]
    by_cases live : j < 661
    · let h := j-222
      have idx : j = 222+h := by dsimp [h]; omega
      have bound : h < 439 := by dsimp [h]; omega
      rw [idx,reverse_helper n v h bound,forward_helper n v high h bound]
    · rw [reverse_high n v j (by omega),forward_high n v high j (by omega)]
  · rfl

/-- The register a role owns in the class-`d` run, if any. -/
def ownerIndex (n : Fin 9) (r : Fin 32) (d : Fin 5) (ρ : Role) : Option ℕ :=
  (List.range 661).find? (fun j => owner n r d j = ρ)

/-- The class-`d` run of the invocation at stage `n` in replica `r`. -/
noncomputable def invoke (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State) : State := fun ρ =>
  match ownerIndex n r d ρ with
  | some j => along (bar (chart n j)ᵀ) (runWord n (registers n r d X) j)
  | none => X ρ

/-! ### Distinct owners -/

theorem owner_injective (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    ∀ j < 661, ∀ k < 661, owner n r d j = owner n r d k → j = k := by
  intro j hj k hk hjk
  have hap := activePair_lt n
  have hhost : ∀ h < 439, (slotOf n h) ∈ slots ∧ (slotOf n h).stage = n.val ∧
      (slotOf n h).helper = h := fun h hh => slotOf_spec n.val n.isLt h hh
  by_cases hj2 : j < 222 <;> by_cases hk2 : k < 222
  · simp only [owner, hj2, hk2, ite_true, sideRole, Role.mk.injEq, Fin.mk.injEq] at hjk
    obtain ⟨-, hb, hp, -⟩ := hjk
    simp only [regSide] at hb
    split_ifs at hb <;> omega
  · exfalso
    obtain ⟨hσ, hst, -⟩ := hhost (k - 222) (by omega)
    have hf := slot_fits _ hσ
    have hq := pairOf_lt _ (by omega : (slotOf n (k - 222)).idle < 10)
    have hoff := slot_off_active _ hσ
    simp only [owner, hj2, hk2, ite_true, ite_false, sideRole, hostRole, Role.mk.injEq,
      Fin.mk.injEq] at hjk
    obtain ⟨-, hb, -, -⟩ := hjk
    rw [hst] at hoff
    simp only [regSide] at hb
    split_ifs at hb <;> omega
  · exfalso
    obtain ⟨hσ, hst, -⟩ := hhost (j - 222) (by omega)
    have hf := slot_fits _ hσ
    have hq := pairOf_lt _ (by omega : (slotOf n (j - 222)).idle < 10)
    have hoff := slot_off_active _ hσ
    simp only [owner, hj2, hk2, ite_true, ite_false, sideRole, hostRole, Role.mk.injEq,
      Fin.mk.injEq] at hjk
    obtain ⟨-, hb, -, -⟩ := hjk
    rw [hst] at hoff
    simp only [regSide] at hb
    split_ifs at hb <;> omega
  · simp only [owner, hj2, hk2, ite_false, hostRole, Role.mk.injEq, Fin.mk.injEq] at hjk
    obtain ⟨-, hb, hp, hc⟩ := hjk
    obtain ⟨hσ, hst, hhe⟩ := hhost (j - 222) (by omega)
    obtain ⟨hσ', hst', hhe'⟩ := hhost (k - 222) (by omega)
    have hf := slot_fits _ hσ
    have hf' := slot_fits _ hσ'
    have hq := pairOf_lt _ (by omega : (slotOf n (j - 222)).idle < 10)
    have hq' := pairOf_lt _ (by omega : (slotOf n (k - 222)).idle < 10)
    have hpair : pairOf (slotOf n (j - 222)).idle = pairOf (slotOf n (k - 222)).idle := by omega
    have hcopy : (slotOf n (j - 222)).copy = (slotOf n (k - 222)).copy := by omega
    by_cases hs : slotOf n (j - 222) = slotOf n (k - 222)
    · have := congrArg Slot.helper hs
      rw [hhe, hhe'] at this
      omega
    · exact absurd (congrArg Fin.val hc)
        (hostClass_distinct _ _ hσ hσ' (hst.trans hst'.symm) hpair hcopy hs d.val)

theorem find_owner (n : Fin 9) (r : Fin 32) (d : Fin 5) (j : ℕ) (hj : j < 661) :
    ownerIndex n r d (owner n r d j) = some j := by
  unfold ownerIndex
  cases hf : (List.range 661).find? (fun k => owner n r d k = owner n r d j) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf j (List.mem_range.mpr hj))
  | some k =>
    have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [owner_injective n r d k hk j hj hp]

theorem invoke_owner (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State) (j : ℕ) (hj : j < 661) :
    invoke n r d X (owner n r d j) = along (bar (chart n j)ᵀ) (runWord n (registers n r d X) j) := by
  unfold invoke
  rw [find_owner n r d j hj]

/-- Roles that own no register are unchanged. -/
theorem invoke_other (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State) (ρ : Role)
    (hρ : ∀ j < 661, owner n r d j ≠ ρ) : invoke n r d X ρ = X ρ := by
  have hnone : ownerIndex n r d ρ = none := by
    rw [ownerIndex, List.find?_eq_none]
    intro j hj
    simpa using hρ j (List.mem_range.mp hj)
  unfold invoke
  rw [hnone]

/-! ### Coordinate conjugation -/

theorem bar_mul_self {R : Matrix Axis Axis ℚ} (hR : R * R = 1) : bar R * bar R = 1 := by
  rw [bar, fromBlocks_multiply, hR, ← fromBlocks_one]
  simp

theorem bar_transpose (R : Matrix Axis Axis ℚ) : bar Rᵀ = (bar R)ᵀ := by
  simp only [bar, fromBlocks_transpose, transpose_zero]

/-- Reading through an involutive chart, changing frames, and writing back. -/
theorem along_route (R : Matrix Axis Axis ℚ) (hR : R * R = 1) (U V : Matrix Axis Axis ℚ)
    (f : Stream) :
    along (bar R) (along (exchange U * exchange V) (along (bar R) f)) =
      along (exchange (R * U * R) * exchange (R * V * R)) f := by
  rw [← along_mul, ← along_mul]
  congr 1
  have hb : fromBlocks R 0 0 R * fromBlocks R 0 0 R = 1 := bar_mul_self hR
  rw [← exchange_conj R R U hR, ← exchange_conj R R V hR, bar]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (fromBlocks R 0 0 R) (fromBlocks R 0 0 R), hb, Matrix.one_mul]

/-- Reading through an orthogonal chart, changing frames, and writing back. -/
theorem along_chart (Φ : Matrix Axis Axis ℚ) (hΦ : Φ * Φᵀ = 1) (U : Matrix Axis Axis ℚ) (f : Stream) :
    along (bar Φᵀ) (along (exchange U) (along (bar Φ) f)) = along (exchange (Φ * U * Φᵀ)) f := by
  rw [← along_mul, ← along_mul, ← Matrix.mul_assoc]
  simp only [bar]
  rw [exchange_conj Φ Φᵀ U hΦ]

/-! ### The data sides -/

section Data

variable (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State) (t : Fin 111)

theorem owner_source : owner n r d t.val = sideRole n r d (n.val % 2) t := by
  simp [owner, regSide, show t.val < 222 by omega, t.isLt, Nat.mod_eq_of_lt t.isLt]

theorem owner_target : owner n r d (111 + t.val) = sideRole n r d (1 - n.val % 2) t := by
  simp only [owner, show 111 + t.val < 222 by omega, ite_true, regSide,
    show ¬111 + t.val < 111 by omega, ite_false]
  congr 1
  apply Fin.ext
  simp only
  omega

theorem chart_data (j : ℕ) (hj : j < 222) : chart n j = (port (j % 111)).stageRoute n := by
  simp [chart, hj]

theorem registers_high : ∀ j, 661 ≤ j → registers n r d X j = 0 := by
  intro j hj
  simp [registers, show ¬j < 661 by omega]

/-- Write-back of a data register: read, frame change, write. -/
theorem data_writeback (j : ℕ) (hj : j < 222) (U V : Matrix Axis Axis ℚ) (f : Stream) :
    along (bar (chart n j)ᵀ) (along (exchange U * exchange V) (along (bar (chart n j)) f)) =
      along (exchange ((port (j % 111)).stageRoute n * U * (port (j % 111)).stageRoute n) *
        exchange ((port (j % 111)).stageRoute n * V * (port (j % 111)).stageRoute n)) f := by
  rw [chart_data n j hj, PortCertificate.stageRoute_transpose]
  exact along_route _ (PortCertificate.stageRoute_mul_self (port_checked _ (Nat.mod_lt _ (by norm_num))) n) U V f

end Data

noncomputable def ownerTape (n : Fin 9) (r : Fin 32) (d : Fin 5) (j : Fin 661) : Fin 142081 :=
  ((Fin.cast card_role) (Fintype.equivFin Role (owner n r d j))).castSucc

theorem ownerTape_injective (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    Function.Injective (ownerTape n r d) := by
  intro i j eq
  apply Fin.ext
  apply owner_injective n r d i i.isLt j j.isLt
  exact (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))

end IntegerMultBounds.MathlibTM2.M6.BitNode
