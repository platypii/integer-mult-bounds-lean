module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalPack
public import IntegerMultBounds.MathlibTM2.M6.BitCopyRecordSetup

/-! Initialize and pack an inherited interval using the caller's dimension tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The three shared binary operands and the width used to initialize every row. -/
def IntervalHeaderInputs {T : ℕ} (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (w W : ℕ) (S : Stacks T prime) : Prop :=
  (∀ i : Fin 3, ∀ z, readAt blank (S.L (headers (copyRecordSources i)))
    (S.R (headers (copyRecordSources i))) (z-1) =
      RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (![prime^(w+1),W,1] i)) z) ∧
  S.R width = binSyms (w+1).size (w+1)

omit [M8.Machine.Net] in
theorem IntervalHeaderInputs.of_frame {B T w W : ℕ} {headers : Fin 6 ↪ Fin T}
    {width : Fin T} {S F : Stacks T prime} (inputs : IntervalHeaderInputs headers width w W S)
    (ports : Fin B ↪ Fin T) (apart : ∀ i j, headers i ≠ ports j)
    (outside : ∀ j, width ≠ ports j)
    (frame : ∀ j, (∀ k, ports k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) :
    IntervalHeaderInputs headers width w W F := by
  refine ⟨?_, (frame width (fun k => (outside k).symm)).2.trans inputs.2⟩
  intro i z
  obtain ⟨left,right⟩ := frame _ (fun k => (apart (copyRecordSources i) k).symm)
  rw [left,right]
  exact inputs.1 i z

theorem initializePackRow_exec {T Q : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (ports : Fin (N+35) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (apart : ∀ i j, headers i ≠ ports j) (outside : ∀ i, width ≠ ports i)
    (body : P → Pr P T Q prime U) (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    ∀ w W, 0 < W →
      let M := prime^(w+1)
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let bank := small.trans ports
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (u : HS T Q prime U) (S : Stacks T prime)
        (input : Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      IntervalHeaderInputs headers width w W S →
      (∀ k, k ≠ small 24 → S.L (ports k) = [] ∧ S.R (ports k) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 (fun i => input (i.cast size.symm)) S →
      ∃ z F n, Exec body ((copyRecordSetup headers bank width).seq
        (statePlacedNormalized ports capacity swapStates_pos Empty.elim
          (packSchedule 128 (intervalPackSchedule lo (hi-lo) (64-hi+lo))))) (mk u S) n (mk z F) ∧
        n ≤ (16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58) +
          (intervalPassTime U lo hi w W) ∧ z.user = u.user ∧
        RecordReady (b := prime) (w := w) (W := W) (d := 128) bank M.size W.size []
          SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 (input ∘ position.symm) F ∧
        (∀ k : Fin (N+35), 35 ≤ k.val → F.L (ports k) = [] ∧ F.R (ports k) = []) ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have pack := intervalForward_exec capacity ports body lo hi ordered fits
  intro w W hW M small bank size position u S input headersReady free payload
  obtain ⟨v,D,t,user,cost,init,ready,keep⟩ := intervalRecordSetup_exec body headers bank
    (fun i j => apart i (small j)) width (fun j => outside (small j)) 128 w W u S headersReady.1 headersReady.2
    (fun i ne => free _ (small.injective.ne ne)) (fun i => input (i.cast size.symm))
    (fun z => by simpa only [sub_zero,List.map_ofFn] using payload z)
  obtain ⟨z,F,n,same,paid,ran,result,clear,off⟩ := pack w W hW v D [] (fun _ => blank) 0 input ready (by
    intro k hk
    have ne (i : Fin 35) : small i ≠ k := by
      intro eq
      have h := congrArg Fin.val eq
      change i.val = k.val at h
      omega
    have frame := keep (ports k) (fun i => ports.injective.ne (ne i))
    exact ⟨frame.1.trans (free k (ne 24).symm).1,frame.2.trans (free k (ne 24).symm).2⟩)
  refine ⟨z,F,t+n,.seq init ran,Nat.add_le_add cost paid,same.trans user,result,clear,?_⟩
  intro j hj
  have frame := keep j (fun i => hj (small i))
  exact ⟨(off j hj).1.trans frame.1,(off j hj).2.trans frame.2⟩

/-- Initialize the private records and pack the owner rows, reading a common
dimension bank throughout the pass. -/
theorem initializePackBank_exec {T Q : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (ports : Fin 142080 → Fin (N+35) ↪ Fin T)
    (apart : ∀ i j, i ≠ j → ∀ a b, ports i a ≠ ports j b)
    (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (disjoint : ∀ r i j, headers i ≠ ports r j) (outside : ∀ r i, width ≠ ports r i)
    (body : P → Pr P T Q prime U) (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    ∀ w W, 0 < W →
      let M := prime^(w+1)
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (u : HS T Q prime U) (S : Stacks T prime)
        (input : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      ∀ fan : Fin (142080+2) ↪ Fin T,
      (∀ r : Fin 142080, ports r (small 24) = fan (r.castAdd 2)) →
      (∀ j : Fin 2, ∀ r k, ports r k ≠ fan (j.natAdd 142080)) →
      let inherited := fun r (i : Fin (M^128*W)) => input r (i.cast size.symm)
      let packedRows := fun r => input r ∘ position.symm
      let packed := fun r F => RecordReady (b := prime) (w := w) (W := W) (d := 128)
        (small.trans (ports r)) M.size W.size [] SparseRoleCircuit.encode (fun _ => blank)
        (fun _ => blank) 0 0 (input r ∘ position.symm) F ∧
        ∀ k : Fin (N+35), 35 ≤ k.val → F.L (ports r k) = [] ∧ F.R (ports r k) = []
      let code := fun r => (copyRecordSetup headers (small.trans (ports r)) width).seq
        (statePlacedNormalized (ports r) capacity swapStates_pos Empty.elim
          (packSchedule 128 (intervalPackSchedule lo (hi-lo) (64-hi+lo))))
      IntervalHeaderInputs headers width w W S → HelperFan fan inherited S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      ∃ z F n, Exec body (Prog.seqList ((List.finRange 142080).map code)) (mk u S) n (mk z F) ∧
        n ≤ ((List.finRange 142080).map (fun _ =>
          (16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58) +
          (intervalPassTime U lo hi w W))).sum+1 ∧
        z.user = u.user ∧ HelperFan fan packedRows F ∧ (∀ r, packed r F) ∧
        ∀ j, (∀ r k, ports r k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have run := fun r => initializePackRow_exec capacity (ports r) headers width
    (disjoint r) (outside r) body lo hi ordered fits
  intro w W hW M small size position u S input fan shared counters inherited packedRows packed code common live free
  let ready := fun r (D : Stacks T prime) => (∀ k, k ≠ small 24 → D.L (ports r k) = [] ∧ D.R (ports r k) = []) ∧
        RecordPayload (ports r (small 24)) (fun _ => blank) 0 (fun i => input r (i.cast size.symm)) D
  have inputs r : ready r S := by
    refine ⟨free r,?_⟩
    rw [shared]
    exact fanPayload live r
  obtain ⟨z,F,n,exec,paid,user,rows,frame⟩ := returnRows_exec body ports apart code _
    ready packed (fun r D F keep row => by
      refine ⟨fun k hk => ⟨(keep k).1.trans (row.1 k hk).1,(keep k).2.trans (row.1 k hk).2⟩,?_⟩
      intro z
      rw [(keep _).1,(keep _).2]
      exact row.2 z) (fun r D F keep row => by
      refine ⟨row.1.returnPayload (fun i _ => keep (small i)) (fun z => ?_),?_⟩
      · change _ = readAt blank (F.L (ports r (small 24))) (F.R (ports r (small 24))) _
        rw [(keep _).1,(keep _).2]
        exact (row.1.src z).symm
      · intro k hk
        exact ⟨(keep k).1.trans (row.2 k hk).1,(keep k).2.trans (row.2 k hk).2⟩)
    (IntervalHeaderInputs headers width w W)
    (fun r _ _ keep h => h.of_frame (ports r) (disjoint r) (outside r) keep)
    (fun r v D h row => by
      obtain ⟨z,F,n,exec,paid,user,result,free,frame⟩ :=
        run r w W hW v D (input r) h row.1 row.2
      exact ⟨z,F,n,exec,paid,user,⟨result,free⟩,frame⟩)
    (List.finRange 142080) (List.nodup_finRange _) u S common (fun r _ => inputs r)
  refine ⟨z,F,n,exec,paid,user,?_,fun r => rows r (List.mem_finRange r),fun j h => frame j (fun r _ => h r)⟩

  apply helperFan_of_payloads live
  · intro r z
    rw [← shared]
    simpa only [Function.Embedding.trans_apply,sub_zero,List.map_ofFn] using
      (rows r (List.mem_finRange r)).1.src z
  · intro j
    exact frame _ (fun r _ k => counters j r k)

omit [M8.Machine.Net] in
private theorem liftFan {c T B V : ℕ} (e : Fin T ↪ Fin B) (dst : Fin (c+2) ↪ Fin T)
    (output : Fin c → Fin V → ZMod 2) (D : Stacks B prime) (F : Stacks T prime)
    (view : embStk e D = F) (owners : HelperFan dst output F) :
    HelperFan (dst.trans e) output D := by
  subst F
  exact owners

omit [M8.Machine.Net] in
/-- Lift a child running on the caller tapes past the private row records.
The returned fan is visible on the enlarged host and every private record
stack is preserved, regardless of its contents. -/
theorem liftIntervalChild_exec {c B T Q V : ℕ} (payload : Fin B) (body : P → Pr P T Q prime U)
    (code : Pr P T Q prime U) (src dst : Fin (c+2) ↪ Fin T)
    (output : Fin c → Fin V → ZMod 2) :
    let extend := Fin.castAddEmb (n := T) (c*B)
    let ports := intervalRecordBank src payload
    ∀ u S z F n,
    Exec body code (mk (embDn extend u) (embStk extend S)) n (mk z F) →
    HelperFan dst output F →
    ∃ v D, Exec (fun p => embProg extend id (body p)) (embProg extend id code) (mk u S) n (mk v D) ∧
      v.user = z.user ∧ HelperFan (dst.trans extend) output D ∧
      (∀ r k, k ≠ payload → D.L (ports r k) = S.L (ports r k) ∧ D.R (ports r k) = S.R (ports r k)) ∧
      ∀ j, D.L (extend j) = F.L j ∧ D.R (extend j) = F.R j := by
  intro extend ports u S z F n run owners
  obtain ⟨v,D,exec,_,user,view,frame⟩ := exec_emb (ι := id)
    (body' := fun p => embProg extend id (body p)) extend.injective (fun _ => rfl) run u rfl S rfl
  refine ⟨v,D,exec,user,?_,?_,?_⟩
  · exact liftFan extend dst output D F view owners
  · intro r k ne
    apply frame
    intro j eq
    change finSumFinEquiv (Sum.inl j) = finSumFinEquiv _ at eq
    have same := finSumFinEquiv.injective eq
    simp [ne] at same
  · intro j
    exact ⟨congrArg (fun E => E.L j) view,congrArg (fun E => E.R j) view⟩

/-- Execute both layout passes around a child on the extended host. The child
can return its owners on a different fan while leaving private records intact. -/
theorem withIntervalBank_exec {T Q : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (src dst : Fin (142080+2) ↪ Fin T)
    (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (separate : ∀ r : Fin 142080, ∀ i, src (r.castAdd 2) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, src (r.castAdd 2) ≠ width)
    (body : P → Pr P (T+142080*(N+35)) Q prime U)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    let extend := Fin.castAddEmb (142080*(N+35)) (n := T)
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank src (small 24)
    ∃ enter leave : Pr P (T+142080*(N+35)) Q prime U,
    ∀ w W, 0 < W →
      let M := prime^(w+1)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (input output : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2)
        (child : Pr P (T+142080*(N+35)) Q prime U) (price : ℕ) (preserved : Fin T → Prop) u S,
      (∀ j, preserved j → ∀ r : Fin 142080, src (r.castAdd 2) ≠ j ∧ dst (r.castAdd 2) ≠ j) →
      IntervalHeaderInputs (headers.trans extend) (extend width) w W S →
      HelperFan (src.trans extend) (fun r i => input r (i.cast size.symm)) S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ v D, HelperFan (src.trans extend) (fun r => input r ∘ position.symm) D →
        (∀ j, (∀ r k, ports r k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F n, Exec body child (mk v D) n (mk z F) ∧ n ≤ price ∧ z.user = v.user ∧
          HelperFan (dst.trans extend) (fun r => output r ∘ position.symm) F ∧
          (∀ r k, k ≠ small 24 → F.L (ports r k) = D.L (ports r k) ∧ F.R (ports r k) = D.R (ports r k)) ∧
          ∀ j, preserved j → F.L (extend j) = D.L (extend j) ∧ F.R (extend j) = D.R (extend j)) →
      ∃ z F n, Exec body ((enter.seq child).seq leave) (mk u S) n (mk z F) ∧
        n ≤ ((List.finRange 142080).map (fun _ =>
          (16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58)+intervalPassTime U lo hi w W)).sum+1
          + price + (((List.finRange 142080).map (fun _ => intervalPassTime U lo hi w W)).sum+1) ∧
        z.user = u.user ∧ HelperFan (dst.trans extend) (fun r i => output r (i.cast size.symm)) F ∧
        ∀ j, preserved j → F.L (extend j) = S.L (extend j) ∧ F.R (extend j) = S.R (extend j) := by
  intro extend small ports
  have pack := initializePackBank_exec capacity ports
    (fun _ _ ne => intervalRecordBank_apart src _ ne) (headers.trans extend) (extend width)
    (fun r i k => (intervalRecordBank_outside src _ _ (fun s => separate s i) r k).symm)
    (fun r k => (intervalRecordBank_outside src _ _ widthFree r k).symm) body lo hi ordered fits
  have unpack := placedIntervalPass_exec capacity dst body lo hi ordered fits true
  let schedule := intervalPackSchedule lo (hi-lo) (64-hi+lo)
  let enter : Fin 142080 → Pr P (T+142080*(N+35)) Q prime U := fun r => (copyRecordSetup (headers.trans extend) (small.trans (ports r)) (extend width)).seq
    (statePlacedNormalized (ports r) capacity swapStates_pos Empty.elim (packSchedule 128 schedule))
  let leave : Fin 142080 → Pr P (T+142080*(N+35)) Q prime U := fun r => statePlacedNormalized (intervalRecordBank dst (small 24) r) capacity
    swapStates_pos Empty.elim (packSchedule 128 schedule.reverse)
  refine ⟨Prog.seqList ((List.finRange 142080).map enter),
    Prog.seqList ((List.finRange 142080).map leave),?_⟩
  intro w W hW M size position input output child price preserved u S off dimensions live free call
  obtain ⟨v,D,t,entry,first,user,packed,records,keep⟩ :=
    pack w W hW u S input (src.trans extend) (intervalRecordBank_payload src _)
      (fun j r k => intervalRecordBank_outside src _ _ (fun i => src.injective.ne (by
        intro eq
        have h := congrArg Fin.val eq
        change i.val = 142080+j.val at h
        omega)) r k) dimensions live free
  obtain ⟨z,F,n,ran,paid,same,returned,frame,childKeep⟩ := call v D packed keep
  obtain ⟨y,G,m,exit,last,after,owners,_,leaveKeep⟩ := unpack w W hW z F (fun _ => [])
    (fun _ _ => blank) (fun _ => 0) output returned (fun r => by
      refine ⟨_,F,intervalReturnedRecord src dst r D F _ _ (records r) returned (frame r),?_⟩
      exact fun _ _ => ⟨rfl,rfl⟩)
  refine ⟨y,G,t+n+m,(entry.seq ran).seq exit,Nat.add_le_add (Nat.add_le_add first paid) last,
    after.trans (same.trans user),owners,?_⟩
  intro j hj
  have before := keep (extend j) (intervalRecordBank_outside src _ j (fun r => (off j hj r).1))
  have middle := childKeep j hj
  have afterCall := leaveKeep j (fun r => (off j hj r).2)
  exact ⟨afterCall.1.trans (middle.1.trans before.1),afterCall.2.trans (middle.2.trans before.2)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
