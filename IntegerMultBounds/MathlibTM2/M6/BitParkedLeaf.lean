module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners
public import IntegerMultBounds.MathlibTM2.M6.BitStoppedOwnerRows

/-! Placement of the stopped leaf beside the parked parent tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

/-- Append the leaf workspace behind the caller’s descriptor and owner
tapes. The helper at zero and the shifted owner ports keep their addresses. -/
def parkedLeafPlace (T work : ℕ) :
    Fin ((T+1)+work) ↪ Fin ((T+work)+1) :=
  Fin.castLEEmb (by omega)

theorem parkedLeafFan {c T : ℕ} (fan : Fin (c+2) ↪ Fin T) (work : ℕ) :
    ((withHelperPort fan).trans (Fin.castAddEmb work)).trans
      (parkedLeafPlace T work) =
    withHelperPort (fan.trans (Fin.castAddEmb work)) := by
  ext i
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.lastCases with
    | last => simp [withHelperPort,parkedLeafPlace]
    | cast i => simp [withHelperPort,parkedLeafPlace]
  | right i => simp [withHelperPort,parkedLeafPlace]

theorem parkedLeafSplit {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (work : ℕ) :
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext)
      (fun i j => ext.injective.ne (apart i j))
    ∀ i, (bank i).val ≤ T := by
  intro ext bank i
  induction i using Fin.cases with
  | zero => exact Nat.zero_le _
  | succ i =>
    rw [show bank i.succ = _ from ownerSplitBank_succ ..]
    induction i using Fin.addCases (m := (1+c)+2) (n := 2) with
    | right j =>
      simp [returnedMergeBank,ext]
    | left i =>
      induction i using Fin.addCases (m := 1+c) (n := 2) with
      | right j =>
        simp [returnedMergeBank,ext]
      | left i =>
        induction i using Fin.addCases <;> simp [returnedMergeBank,ext]

theorem splitAvoids {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (j : Fin T)
    (hs : ∀ i, saved i ≠ j) (hf : ∀ i, fan i ≠ j) :
    ∀ k, ownerSplitBank saved fan apart k ≠ j.succ := by
  intro k
  induction k using Fin.cases with
  | zero => exact (Fin.succ_ne_zero _).symm
  | succ k =>
    rw [ownerSplitBank_succ]
    apply (Fin.succ_injective _).ne
    induction k using Fin.addCases (m := (1+c)+2) (n := 2) with
    | right i => simpa [returnedMergeBank] using hf (i.natAdd c)
    | left k =>
      induction k using Fin.addCases (m := 1+c) (n := 2) with
      | right i => simpa [returnedMergeBank] using hs i.succ
      | left k =>
        induction k using Fin.addCases with
        | left i => simpa [returnedMergeBank] using hs 0
        | right i => simpa [returnedMergeBank] using hf (i.castAdd 2)

theorem parkedLeafReady [M8.Machine.Net] {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (fields : Fin 6 → Fin T)
    (hs : ∀ i j, saved i ≠ fields j) (hf : ∀ i j, fan i ≠ fields j) (lane : Descriptor) :
    let work := LeafCore.small
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext) (fun i j => ext.injective.ne (apart i j))
    let place := parkedLeafPlace T work
    let ready := fun S : Stacks ((T+work)+1) prime =>
      (∀ i : Fin 6, S.R (place ((fields i).succ.castAdd work)) = (Routines.hdr lane i).map bitSymbol) ∧
      ∀ j : Fin work, let t := place (j.natAdd (T+1))
        S.L t = [] ∧ S.R t = []
    ∀ (S D : Stacks ((T+work)+1) prime), ready S → (∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) → ready D := by
  intro work ext bank place ready S D initial frame
  have keep (j) (high : T < j.val) := frame j (fun i eq => by
    have low := parkedLeafSplit saved fan apart work i
    change (bank i).val ≤ T at low
    rw [eq] at low
    omega)
  constructor
  · intro i
    have h := splitAvoids (saved.trans ext) (fan.trans ext) (fun a b => ext.injective.ne (apart a b))
      (ext (fields i)) (fun a => ext.injective.ne (hs a i)) (fun a => ext.injective.ne (hf a i))
    exact ((frame _ h).2).trans (initial.1 i)
  · intro j
    have h := keep (place (j.natAdd (T+1))) (by change T < T+1+j.val; omega)
    exact ⟨h.1.trans (initial.2 j).1,h.2.trans (initial.2 j).2⟩

theorem parkedLeafRows [M8.Machine.Net] {c T Q : ℕ} {P U : Type}
    (fan : Fin (c+2) ↪ Fin T) (fields : Fin 6 → Fin T) (hf : ∀ i j, fan i ≠ fields j)
    (capacity : columnCapacity ≤ Q) :
    let work := LeafCore.small
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let full := withHelperPort (fan.trans ext)
    let place := parkedLeafPlace T work
    ∃ code : Pr P ((T+work)+1) Q prime U, ∀ body (lane : Descriptor)
      (data : Fin c → Fin (volume prime lane) → ZMod 2) helper u S, 0 < volume prime lane →
      HelperFan full (Fin.lastCases helper data) S →
      (∀ i : Fin 6, S.R (place ((fields i).succ.castAdd work)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin work, let t := place (j.natAdd (T+1))
        S.L t = [] ∧ S.R t = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ c*stoppedRowCost lane+1 ∧
        z.user = u.user ∧ HelperFan full (Fin.lastCases helper (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r))) F ∧
        ∀ j, (∀ r : Fin c, full (r.castSucc.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro work ext full place
  let localFan := withHelperPort fan
  let src := fun i => (fields i).succ
  have apart (i : Fin 6) (r : Fin (c+1)) : src i ≠ localFan (r.castAdd 2) := by
    induction r using Fin.lastCases with
    | last => simpa [localFan,withHelperPort,src] using Fin.succ_ne_zero (fields i)
    | cast r => simpa [localFan,withHelperPort,src] using (hf (r.castAdd 2) i).symm
  obtain ⟨code,run⟩ := placedStoppedMoveRows (P := P) (U := U) localFan src apart capacity place
  refine ⟨code,?_⟩
  have ports : (localFan.trans (Fin.castAddEmb work)).trans place = full := parkedLeafFan fan work
  rw [← ports]
  exact run

private theorem stoppedBill {n rows overhead : ℕ} {core power : ℝ} {header : ℕ}
    (live : 0 < n) (nonempty : 0 < rows) (headers : header ≤ 110*n)
    (unit : 1 ≤ power) (rate : 0 ≤ core) :
    ((⌊rows*((header : ℝ)+core*(n*power))+1⌋₊+overhead*(n*rows) : ℕ) : ℝ) ≤
      (111+core+overhead)*((n*rows : ℕ)*power) := by
  have floorBill := Nat.floor_le (show 0 ≤ (rows : ℝ)*(header+core*(n*power))+1 by positivity)
  have h : (header : ℝ) ≤ 110*n := by exact_mod_cast headers
  have size : (1 : ℝ) ≤ (n : ℝ)*rows := by exact_mod_cast Nat.mul_pos live nonempty
  have scaled := le_mul_of_one_le_right (show 0 ≤ (n : ℝ)*rows by positivity) unit
  push_cast
  nlinarith only [floorBill,mul_le_mul_of_nonneg_left h (Nat.cast_nonneg rows),
    size,scaled,mul_le_mul_of_nonneg_left scaled (Nat.cast_nonneg overhead)]

noncomputable def parkedStoppedRate [M8.Machine.Net] : ℝ :=
  111+((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))+
    ((298*(intervalSplitTapes+5)+37 : ℕ) : ℝ)

/-- A stopped MOVE on the serialized word, including its named child call. -/
theorem parkedStoppedMove [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (fields : Fin 6 → Fin T) (hs : ∀ i j, saved i ≠ fields j) (hf : ∀ i j, fan i ≠ fields j)
    (capacity : columnCapacity ≤ Q)
    (splitCapacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let work := LeafCore.small
    let H := (T+work)+1
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext) (fun i j => ext.injective.ne (apart i j))
    let place := parkedLeafPlace T work
    ∃ leaf : Pr P H Q prime U, ∀ (body : P → Pr P H Q prime U) (entry : P), body entry = leaf →
    ∃ code : Pr P H Q prime U, ∀ (lane : Descriptor),
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      ∀ (x : Fin (volume prime wide) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime), 0 < m →
      S.R (ext (saved 0)).succ = List.ofFn (fun i : Fin (m*142080) => SparseRoleCircuit.encode (x (i.cast size))) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      (∀ i : Fin 6, S.R (ext (fields i)).succ = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin work, let t := place (j.natAdd (T+1)); S.L t = [] ∧ S.R t = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ parkedStoppedRate*((volume prime wide : ℝ)*((max 1 lane.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        z.user = u.user ∧ RecordPayload (ext (saved 0)).succ (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro work H ext bank place
  obtain ⟨leaf,child⟩ := parkedLeafRows (P := P) (U := U) fan fields hf capacity
  refine ⟨leaf,?_⟩
  intro body entry installed
  have separate i j := ext.injective.ne (apart i j)
  obtain ⟨wrap,run⟩ := parkedMoveTranspose body (saved.trans ext) (fan.trans ext) separate splitCapacity
  refine ⟨wrap entry,?_⟩
  intro lane m wide size x u S pos source left empty headers free
  obtain ⟨z,F,t,exec,paid,user,out,frame⟩ := run entry ⌊142080*stoppedRowCost lane+1⌋₊ lane x (fun _ => 0) u S pos source left empty (by
    intro v D live off
    obtain ⟨hdr,clean⟩ := parkedLeafReady saved fan apart fields hs hf lane S D ⟨headers,free⟩ off
    obtain ⟨z,F,n,exec,paid,user,out,keep⟩ := child body lane _ _ v D pos live hdr clean
    refine ⟨z,F,n,installed ▸ exec,Nat.le_floor paid,user,out,?_,?_⟩
    · intro j
      apply keep
      intro r
      simp only [withHelperPort,Function.Embedding.coeFn_mk,Fin.addCases_left,Fin.lastCases_castSucc]
      change (ext (fan (r.castAdd 2))).succ ≠ (ext (saved j)).succ
      exact Fin.succ_injective _ |>.ne (ext.injective.ne (apart j _).symm)
    · intro j outside
      apply keep
      intro r
      have ports := DFunLike.congr_fun (ownerSplitBank_fan (saved.trans ext) (fan.trans ext) separate)
        (r.castSucc.castAdd 2)
      exact ports ▸ outside _)
  refine ⟨z,F,t,exec,?_,user,out,frame⟩
  apply (Nat.cast_le.mpr paid).trans
  rw [← size]
  unfold parkedStoppedRate stoppedRowCost
  have coreNonneg (k : ℕ) (C : ℝ) : 0 ≤ ((k+5 : ℕ) : ℝ)*|C|+8+k*(16+8*|C|) := by positivity
  exact stoppedBill (n := volume prime lane) (rows := 142080)
    (overhead := 298*(intervalSplitTapes+5)+37)
    (core := ((LeafCore.small+5 : ℕ) : ℝ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))
    (power := ((max 1 lane.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) pos (by decide) (descriptorHeaderCost_le lane (LeafCore.positive_of_volume pos))
    (Real.one_le_rpow (by exact_mod_cast le_max_left 1 lane.width) M8.Machine.BudgetBound.exponent_range.1.le)
    (coreNonneg LeafCore.small LeafCore.C)

end IntegerMultBounds.MathlibTM2.M6.BitNode
