module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners
public import IntegerMultBounds.MathlibTM2.M6.BitStoppedOwnerRows

/-! Placement of the stopped leaf beside the parked parent tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

/-- Append six descriptor headers and the leaf workspace behind the original
tapes. The helper at zero and the shifted owner ports keep their addresses. -/
def parkedLeafPlace (T work : ℕ) :
    Fin (((T+1)+6)+work) ↪ Fin (((T+6)+work)+1) :=
  Fin.castLEEmb (by omega)

theorem parkedLeafFan {c T : ℕ} (fan : Fin (c+2) ↪ Fin T) (work : ℕ) :
    (((withHelperPort fan).trans (Fin.castAddEmb 6)).trans (Fin.castAddEmb work)).trans
      (parkedLeafPlace T work) =
    withHelperPort ((fan.trans (Fin.castAddEmb 6)).trans (Fin.castAddEmb work)) := by
  ext i
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.lastCases with
    | last => simp [withHelperPort,parkedLeafPlace]
    | cast i => simp [withHelperPort,parkedLeafPlace]
  | right i => simp [withHelperPort,parkedLeafPlace]

theorem parkedLeafSplit {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (work : ℕ) :
    let ext := (Fin.castAddEmb 6 : Fin T ↪ Fin (T+6)).trans (Fin.castAddEmb work)
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
        induction i using Fin.addCases <;> simp [returnedMergeBank,ext] <;> omega

theorem parkedLeafReady [M8.Machine.Net] {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (lane : Descriptor) :
    let work := LeafCore.small
    let ext := (Fin.castAddEmb 6 : Fin T ↪ Fin (T+6)).trans (Fin.castAddEmb work)
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext) (fun i j => ext.injective.ne (apart i j))
    let place := parkedLeafPlace T work
    let ready := fun S : Stacks (((T+6)+work)+1) prime =>
      (∀ i : Fin 6, S.R (place ((i.natAdd (T+1)).castAdd work)) = (Routines.hdr lane i).map bitSymbol) ∧
      ∀ j : Fin work, let t := place (j.natAdd ((T+1)+6))
        S.L t = [] ∧ S.R t = []
    ∀ (S D : Stacks (((T+6)+work)+1) prime), ready S → (∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) → ready D := by
  intro work ext bank place ready S D initial frame
  have keep (j) (high : T < j.val) := frame j (fun i eq => by
    have low := parkedLeafSplit saved fan apart work i
    change (bank i).val ≤ T at low
    rw [eq] at low
    omega)
  constructor
  · intro i
    exact ((keep _ (by change T < T+1+i.val; omega)).2).trans (initial.1 i)
  · intro j
    have h := keep (place (j.natAdd ((T+1)+6))) (by change T < T+1+6+j.val; omega)
    exact ⟨h.1.trans (initial.2 j).1,h.2.trans (initial.2 j).2⟩

theorem parkedLeafRows [M8.Machine.Net] {c T Q : ℕ} {P U : Type}
    (fan : Fin (c+2) ↪ Fin T) (capacity : columnCapacity ≤ Q) :
    let work := LeafCore.small
    let ext := (Fin.castAddEmb 6 : Fin T ↪ Fin (T+6)).trans (Fin.castAddEmb work)
    let full := withHelperPort (fan.trans ext)
    let place := parkedLeafPlace T work
    ∃ code : Pr P (((T+6)+work)+1) Q prime U, ∀ body (lane : Descriptor)
      (data : Fin c → Fin (volume prime lane) → ZMod 2) helper u S, 0 < volume prime lane →
      HelperFan full (Fin.lastCases helper data) S →
      (∀ i : Fin 6, S.R (place ((i.natAdd (T+1)).castAdd work)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin work, let t := place (j.natAdd ((T+1)+6))
        S.L t = [] ∧ S.R t = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ c*stoppedRowCost lane+1 ∧
        z.user = u.user ∧ HelperFan full (Fin.lastCases helper (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r))) F ∧
        ∀ j, (∀ r : Fin c, full (r.castSucc.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro work ext full place
  let localFan := (withHelperPort fan).trans (Fin.castAddEmb 6)
  let src := Fin.natAddEmb (T+1) (m := 6)
  have apart (i : Fin 6) (r : Fin (c+1)) : src i ≠ localFan (r.castAdd 2) := by
    intro eq
    have val := congrArg Fin.val eq
    change T+1+i.val = (withHelperPort fan (r.castAdd 2)).val at val
    have := (withHelperPort fan (r.castAdd 2)).isLt
    omega
  obtain ⟨code,run⟩ := placedStoppedMoveRows (P := P) (U := U) localFan src apart capacity place
  refine ⟨code,?_⟩
  have ports : (localFan.trans (Fin.castAddEmb work)).trans place = full := parkedLeafFan fan work
  rw [← ports]
  exact run

/-- A stopped MOVE on the serialized word, including its named child call. -/
theorem parkedStoppedMove [M8.Machine.Net] {T Q : ℕ} {U : Type}
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (capacity : columnCapacity ≤ Q)
    (splitCapacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let work := LeafCore.small
    let H := ((T+6)+work)+1
    let ext := (Fin.castAddEmb 6 : Fin T ↪ Fin (T+6)).trans (Fin.castAddEmb work)
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext) (fun i j => ext.injective.ne (apart i j))
    let place := parkedLeafPlace T work
    ∃ (leaf code : Pr Unit H Q prime U), ∀ (lane : Descriptor),
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      ∀ (x : Fin (volume prime wide) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime), 0 < m →
      S.R (ext (saved 0)).succ = List.ofFn (fun i : Fin (m*142080) => SparseRoleCircuit.encode (x (i.cast size))) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      (∀ i : Fin 6, S.R (place ((i.natAdd (T+1)).castAdd work)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin work, let t := place (j.natAdd ((T+1)+6)); S.L t = [] ∧ S.R t = []) →
      ∃ z F t, Exec (fun _ => leaf) code (mk u S) t (mk z F) ∧
        t ≤ ⌊142080*stoppedRowCost lane+1⌋₊+(298*(intervalSplitTapes+5)+37)*volume prime wide ∧
        z.user = u.user ∧ RecordPayload (ext (saved 0)).succ (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro work H ext bank place
  obtain ⟨leaf,child⟩ := parkedLeafRows (P := Unit) (U := U) fan capacity
  let body := fun _ : Unit => leaf
  have separate i j := ext.injective.ne (apart i j)
  obtain ⟨wrap,run⟩ := parkedMoveTranspose body (saved.trans ext) (fan.trans ext) separate splitCapacity
  refine ⟨leaf,wrap (),?_⟩
  intro lane m wide size x u S pos source left empty headers free
  apply run () _ lane x (fun _ => 0) u S pos source left empty
  intro v D live off
  obtain ⟨hdr,clean⟩ := parkedLeafReady saved fan apart lane S D ⟨headers,free⟩ off
  obtain ⟨z,F,n,exec,paid,user,out,keep⟩ := child body lane _ _ v D pos live hdr clean
  refine ⟨z,F,n,exec,Nat.le_floor paid,user,out,?_,?_⟩
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
    exact ports ▸ outside _

end IntegerMultBounds.MathlibTM2.M6.BitNode
