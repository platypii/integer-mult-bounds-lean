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
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
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
          (1+(setup+swaps*swapVolumeRate w)*(M^128*W)) ∧ z.user = u.user ∧
        RecordReady (b := prime) (w := w) (W := W) (d := 128) bank M.size W.size []
          SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 (input ∘ position.symm) F ∧
        (∀ k : Fin (N+35), 35 ≤ k.val → F.L (ports k) = [] ∧ F.R (ports k) = []) ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨setup,swaps,pack⟩ := intervalForward_exec capacity ports body lo hi ordered fits
  refine ⟨setup,swaps,?_⟩
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
    ∃ setup swaps : Fin 142080 → ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (u : HS T Q prime U) (S : Stacks T prime)
        (input : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      let ready := fun r (D : Stacks T prime) => (∀ k, k ≠ small 24 → D.L (ports r k) = [] ∧ D.R (ports r k) = []) ∧
        RecordPayload (ports r (small 24)) (fun _ => blank) 0 (fun i => input r (i.cast size.symm)) D
      let packed := fun r F => RecordReady (b := prime) (w := w) (W := W) (d := 128)
        (small.trans (ports r)) M.size W.size [] SparseRoleCircuit.encode (fun _ => blank)
        (fun _ => blank) 0 0 (input r ∘ position.symm) F ∧
        ∀ k : Fin (N+35), 35 ≤ k.val → F.L (ports r k) = [] ∧ F.R (ports r k) = []
      let code := fun r => (copyRecordSetup headers (small.trans (ports r)) width).seq
        (statePlacedNormalized (ports r) capacity swapStates_pos Empty.elim
          (packSchedule 128 (intervalPackSchedule lo (hi-lo) (64-hi+lo))))
      IntervalHeaderInputs headers width w W S → (∀ r, ready r S) →
      ∃ z F n, Exec body (Prog.seqList ((List.finRange 142080).map code)) (mk u S) n (mk z F) ∧
        n ≤ ((List.finRange 142080).map (fun r =>
          (16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58) +
          (1+(setup r+swaps r*swapVolumeRate w)*(M^128*W)))).sum+1 ∧
        z.user = u.user ∧ (∀ r, packed r F) ∧
        ∀ j, (∀ r k, ports r k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  choose setup swaps run using fun r => initializePackRow_exec capacity (ports r) headers width
    (disjoint r) (outside r) body lo hi ordered fits
  refine ⟨setup,swaps,?_⟩
  intro w W hW M small size position u S input ready packed code common inputs
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
  exact ⟨z,F,n,exec,paid,user,fun r => rows r (List.mem_finRange r),fun j h => frame j (fun r _ => h r)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
