module

public import IntegerMultBounds.MathlibTM2.M6.BitSuspendedStack
public import IntegerMultBounds.MathlibTM2.M6.BitPackedMoveCaller

/-! A packed MOVE may leave its borrowed bank dirty. Clear it before unwinding
the frame and charge the erasure to the MOVE's existing cleanup budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

noncomputable def clearSlots {T : ℕ} (slots : List (Fin T)) (S : Stacks T prime) :=
  replaceBank slots S {S with L := fun _ => [], R := fun _ => []}

/-- Reinstating the same caller words on entry and exit preserves the change
in cleanup charge, for every observed set. -/
private theorem restoredCharge {T : ℕ} (slots js : List (Fin T)) (S F : Stacks T prime) :
    tapeCharge cleanupWeight js (replaceBank slots F S) + tapeCharge cleanupWeight js (clearSlots slots S) =
      tapeCharge cleanupWeight js (clearSlots slots F) + tapeCharge cleanupWeight js S := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [tapeCharge,List.map_cons,List.sum_cons] at ih ⊢
    by_cases h : j ∈ slots <;> simp only [clearSlots,replaceBank,h,ite_true,ite_false] at * <;> omega

/-- Execute a packed MOVE on a borrowed bank with arbitrary incoming words.
The transposed payload survives erasure and every borrowed tape is restored. -/
theorem suspendedMove_run {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (move entry : Pr P T Q prime U) (slots : List (Fin T)) (distinct : slots.Nodup)
    (installed : SuspendedBank body (move.seq (clearWorkTapes slots)) slots entry)
    (payload : Fin T) (external : payload ∉ slots) (v : HS T Q prime U) (S : Stacks T prime)
    {N : ℕ} (y : Fin N → ZMod 2) (price : ℕ)
    (keep : Fin T → Prop) (worker : ∀ u : HS T Q prime U, ∃ a F m, Exec body move (mk u (clearSlots slots S)) m (mk a F) ∧
      a.user = u.user ∧ CleanupBound (clearSlots slots S) F m price ∧
      RecordPayload payload (fun _ => blank) 0 y F ∧ ∀ j, keep j → j ∉ slots → F.L j = S.L j ∧ F.R j = S.R j) :
    ∃ z F n, Exec body entry (mk v S) n (mk z F) ∧ z.user = v.user ∧
      CleanupBound S F n (price+4*slots.length+1+
        (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
      RecordPayload payload (fun _ => blank) 0 y F ∧
      ∀ j, j ∈ slots ∨ keep j → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨a,D,m,run,user,cost,out,frame⟩ := worker (if slots.isEmpty then v else {v with sym := none})
  obtain ⟨z,same,clear⟩ := clearWorkTapes_exec body slots distinct a D
  let G := clearSlots slots D
  have clean (j) (h : j ∈ slots) : G.L j = [] ∧ G.R j = [] := by simp [G,clearSlots,replaceBank,h]
  have bill := cleanupBound_clearBank slots distinct cost (Nat.le_refl (tapeCharge cleanupWeight slots D+1))
    (F := G) clean (fun j => by by_cases h : j ∈ slots <;> simp [G,clearSlots,replaceBank,h])
  have initial : tapeCharge cleanupWeight slots (clearSlots slots S) = 4*slots.length := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j h => by simp [cleanupWeight,clearSlots,replaceBank,h])]
    simp [List.map_const',Nat.mul_comm]
  rw [initial] at bill
  obtain ⟨n,paid,exec⟩ := installed.replay S G distinct clean _ v z (run.seq clear)
  refine ⟨z,replaceBank slots G S,n,exec,same.trans (by split at user <;> exact user),?_,?_,?_⟩
  · intro js nd
    have bound := bill js nd
    have eq := restoredCharge slots js S D
    change n+tapeCharge cleanupWeight js _ ≤ tapeCharge cleanupWeight js S+_
    change _+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js (clearSlots slots S)+_ at bound
    have restored : replaceBank slots G S = replaceBank slots D S := by
      unfold G clearSlots replaceBank
      congr 1 <;> funext j <;> by_cases h : j ∈ slots <;> simp [h]
    rw [restored]
    change n ≤ m+(tapeCharge cleanupWeight slots D+1)+_ at paid
    dsimp only [G] at bound
    omega
  · intro j
    simpa [G,clearSlots,replaceBank,external] using out j
  · intro j h
    by_cases mem : j ∈ slots
    · simp [replaceBank,mem]
    · simpa [replaceBank,G,clearSlots,mem] using frame j (h.resolve_left mem) mem

/-- The physical split and merge can borrow occupied source and return tapes
from a suspended parent. All preparation hypotheses refer to the remaining seed. -/
theorem suspendedRowsOnChildBank {P R U : Type} {T H Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (srcOff : ∀ i j, ret i ≠ src j) (dstOff : ∀ i j, ret i ≠ childReturnFan dst j)
    (tmp buf : Fin T) (srcTmp : ∀ i, src i ≠ tmp) (srcBuf : ∀ i, src i ≠ buf)
    (retTmp : ∀ i, ret i ≠ tmp) (retBuf : ∀ i, ret i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (ret 0),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ move : Pr R H Q prime U, ∀ slots wrapper, slots.Nodup → payload ∉ slots →
      SuspendedBank host (move.seq (clearWorkTapes slots)) slots wrapper →
      (∀ i, place (src i) ∈ slots) → (∀ i, place (ret i) ∈ slots) →
      ∀ (child : Descriptor) (atom price : ℕ) seed, child.width = 64*atom → 142080 ∣ child.rows →
      let lane := packedDescriptor (64*atom) (CopyChildLayout.spectators child / 142080)
      let m := volume prime lane
      let wide := packedDescriptor child.width (CopyChildLayout.spectators child)
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) src dst seed price →
      0 < m → ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
      let D := clearSlots slots S
      let B := embStk place D
      RecordPayload payload (fun _ => blank) 0 x S →
      D.R count = [] → D.R saved = [] → D.L aux = [] → D.R aux = [] →
      B.L tmp = [] → B.R tmp = [] → B.R buf = [] →
      (∀ i, seed.L (ret i) = [] ∧ seed.R (ret i) = []) →
      (∀ j, (∀ i, src i ≠ j) → (∀ i, ret i ≠ j) → B.L j = seed.L j ∧ B.R j = seed.R j) →
      ∃ z F n, Exec host wrapper (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (price+1000000034*volume prime wide+49+4*slots.length+1+
          (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
        RecordPayload payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ∈ slots ∨ (j ≠ payload ∧ ∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨move,execute⟩ := packedRowsOnChildBank body entry src dst ret srcOff dstOff tmp buf
    srcTmp srcBuf retTmp retBuf distinct place label host installed payload count saved aux outside separate capacity
  refine ⟨move,?_⟩
  intro slots wrapper nd off chain sources returns child atom price seed width rows lane m wide
    handoff pos x u S D B input countAt savedAt al ar tl tr br vacant rest
  refine suspendedMove_run host move wrapper slots nd chain payload off u S
    (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) (price+1000000034*volume prime wide+49)
    (fun j => j ≠ payload ∧ ∀ i, place i ≠ j) ?_
  intro v
  obtain ⟨a,F,n,run,user,paid,out,frame⟩ := execute child atom price seed width rows handoff pos x v D
    (fun j => by simpa [D,clearSlots,replaceBank,off] using input j) countAt savedAt al ar
    (fun i => by simp [embStk,D,clearSlots,replaceBank,sources]) (fun i => by simp [embStk,D,clearSlots,replaceBank,returns])
    tl tr br vacant rest
  refine ⟨a,F,n,run,user,paid,out,?_⟩
  intro j h mem
  simpa [D,clearSlots,replaceBank,mem] using frame j h.1 h.2

end IntegerMultBounds.MathlibTM2.M6.BitNode
