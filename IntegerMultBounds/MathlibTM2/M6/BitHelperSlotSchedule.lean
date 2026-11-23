module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperPacking
public import IntegerMultBounds.MathlibTM2.M6.OrthogonalInvocation

/-! The packed slot changes between successive uses of a PR589 helper owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open BitHosting

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def helperPosition (entry : Fin 9 × Fin 439) : Fin 56 :=
  ⟨slotPos (IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf entry.1 entry.2),Nat.lt_succ_of_le (slotPos_le _ entry.1.isLt _ entry.2.isLt)⟩

open IntegerMultBounds.Swap.Modular M8.Exchange in
/-- The invocation exchanges the scheduled parent span when its helper word
is read at the flat packing address, with the actual local port encoding. -/
theorem OrthogonalPortReads.packedHelper {V W : ℕ} (n : Fin 9) (h : Fin 439) (w : ℕ)
    [NeZero (prime^w)] (pos : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w)) →
      Fin ((prime^w)^112*W) → Fin V)
    (input output : Fin 661 → Fin V → ZMod 2) (read : OrthogonalPortReads w pos input output) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let c := port (slot.copy % 111)
    let readAt := fun (i : Fin ((prime^w)^128*W)) =>
      let a := copyAddress (i.cast (by rw [← Nat.mul_assoc,← pow_add]))
      pos a.1 a.2
    let address := fun s (j : Fin W) => readAt (FlatCoordinateLayout.index
      (helperSlotField c (some (helperPosition (n,h))) w s) j)
    let reg : Fin 661 := ⟨222+h.val,by omega⟩
    ∀ s j, output reg (address (exchange (reduce (prime^w) (helperSpan n h)) s) j) =
      input reg (address s j) := by
  intro slot c readAt address reg s j
  let H := (reduce (prime^w) (c.helperChart (slotPos slot) (slotPos_le n n.isLt h h.isLt))).transpose
  have cell (a : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
      address a j = pos (copyAddress (chartAddress (transform H H a,j))).1
        (copyAddress (chartAddress (transform H H a,j))).2 := by
    dsimp only [address,readAt]
    rw [helperSlotField_some]
    apply congrArg (fun i => pos (copyAddress i).1 (copyAddress i).2)
    exact Fin.ext (helperDigits_index (transform H H a) j)
  rw [cell,cell]
  exact read.helperSlot n h w pos input output s j

/-- The invocation reads data in place and reads each helper in the inherited
order of its own scheduled slot. -/
noncomputable def invocationOwnerAddress {M W : ℕ} [NeZero M] (n : Fin 9) (i : Fin 661) :
    Equiv.Perm (Fin (M^128*W)) :=
  if h : 222 ≤ i.val then inheritedHelperAddress (helperPosition (n,⟨i.val-222,by omega⟩))
  else Equiv.refl _

open IntegerMultBounds.Swap.Modular M8.Exchange in
theorem OrthogonalPortReads.inheritedHelper {w W : ℕ} [NeZero (prime^w)] (n : Fin 9)
    (input output : Fin 661 → Fin ((prime^w)^128*W) → ZMod 2) :
    let size : (prime^w)^16*((prime^w)^112*W) = (prime^w)^128*W := by
      rw [← Nat.mul_assoc,← pow_add]
    let pos := fun s j => (copyAddress.symm (s,j)).cast size
    let view := fun (word : Fin 661 → Fin ((prime^w)^128*W) → ZMod 2) i =>
      word i ∘ invocationOwnerAddress n i
    OrthogonalPortReads w pos (view input) (view output) →
    ∀ (h : Fin 439) s (j : Fin W),
      let c := port ((IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val).copy % 111)
      let reg : Fin 661 := ⟨222+h.val,by omega⟩
      let addr := fun a => FlatCoordinateLayout.index (helperSlotField c none w a) j
      output reg (addr (exchange (reduce (prime^w) (helperSpan n h)) s)) = input reg (addr s) := by
  intro size pos view read h s j c reg addr
  have run := read.packedHelper n h w pos (view input) (view output) s j
  let packed := fun a => FlatCoordinateLayout.index (helperSlotField c (some (helperPosition (n,h))) w a) j
  have atCell (a) : invocationOwnerAddress n reg (packed a) = addr a := by
    have hit : 222 ≤ reg.val := Nat.le_add_right _ _
    simp only [invocationOwnerAddress,dite_eq_left hit,reg,Nat.add_sub_cancel_left]
    exact inheritedHelperAddress_index c (helperPosition (n,h)) a j
  have cancel (i : Fin ((prime^w)^128*W)) :
      pos (copyAddress (i.cast size.symm)).1 (copyAddress (i.cast size.symm)).2 = i := by
    simp only [pos,Prod.mk.eta,Equiv.symm_apply_apply,Fin.cast_cast,Fin.cast_refl,id_eq]
  change output reg (invocationOwnerAddress n reg (pos _ _)) = input reg (invocationOwnerAddress n reg (pos _ _)) at run
  rw [cancel,cancel] at run
  let b := exchange (reduce (prime^w) (helperSpan n h)) s
  change output reg (invocationOwnerAddress n reg (packed b)) = input reg (invocationOwnerAddress n reg (packed s)) at run
  rwa [atCell b,atCell s] at run

noncomputable def helperSlotChange (n : Fin 9) (run : Fin 32 × Fin 5)
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) (h : Fin 439) : Fin 142081 × Option (Fin 56) × Option (Fin 56) :=
  let t := ownerTape n run.1 run.2 ⟨222+h.val,by omega⟩
  (t,(before t).map helperPosition,some (helperPosition (n,h)))

/-- Enter first-use slots from the port descriptor and skip repeated slots already in place. -/
noncomputable def scheduledSlotChanges (n : Fin 9) (run : Fin 32 × Fin 5)
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) : List (Fin 142081 × Option (Fin 56) × Option (Fin 56)) :=
  let change := helperSlotChange n run before
  ((List.finRange 439).filter fun h => (change h).2.1 != (change h).2.2).map change

/-- Every recorded slot in the sweep prefix was installed by an invocation
on that same physical owner. -/
theorem helperChart_origin (n : Fin 9) (prefixRuns : List (Fin 32 × Fin 5)) (t : Fin 142081)
    (entry : Fin 9 × Fin 439)
    (recorded : (prefixRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)) t = some entry) :
    ∃ p ∈ prefixRuns, entry.1 = n ∧ ownerTape n p.1 p.2 ⟨222+entry.2.val,by omega⟩ = t := by
  induction prefixRuns using List.reverseRecOn with
  | nil => cases recorded
  | append_singleton ps p ih =>
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil,helperChartsAfter] at recorded
    split at recorded
    next hit =>
      obtain rfl := Option.some.inj recorded
      exact ⟨p,by simp,rfl,hit.choose_spec⟩
    next =>
      obtain ⟨q,mem,origin⟩ := ih recorded
      exact ⟨q,List.mem_append_left _ mem,origin⟩

theorem scheduledSlotChanges_unique (n : Fin 9) (run : Fin 32 × Fin 5) (before) :
    ((scheduledSlotChanges n run before).map Prod.fst).Nodup := by
  unfold scheduledSlotChanges
  rw [List.map_map]
  apply List.Nodup.map _ ((List.nodup_finRange _).filter _)
  intro h k same
  have eqn := congrArg Fin.val (ownerTape_injective n run.1 run.2 same)
  exact Fin.ext (Nat.add_left_cancel eqn)

private theorem trace_off {k w W : ℕ} (ls : List (Fin k × Option (Fin 56) × Option (Fin 56))) (a b)
    (trace : HelperSlotTrace w W ls a b) (t : Fin k) (off : ∀ p ∈ ls, p.1 ≠ t) : b t = a t := by
  induction ls generalizing a with
  | nil => exact congrFun trace.symm t
  | cons p ps ih =>
    obtain ⟨word,_,tail⟩ := trace
    rw [ih _ tail (fun q hq => off q (List.mem_cons_of_mem _ hq)),Function.update_of_ne
      (Ne.symm (off p List.mem_cons_self))]

private theorem trace_slot {k w W : ℕ} (ls : List (Fin k × Option (Fin 56) × Option (Fin 56))) (a b)
    (trace : HelperSlotTrace w W ls a b) (unique : (ls.map Prod.fst).Nodup)
    (t : Fin k) (x y : Option (Fin 56)) (hit : (t,x,y) ∈ ls) (c : PortCertificate) s j :
    b t (FlatCoordinateLayout.index (helperSlotField c y (w+1) s) j) =
      a t (FlatCoordinateLayout.index (helperSlotField c x (w+1) s) j) := by
  induction ls generalizing a with
  | nil => simp at hit
  | cons p ps ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨word,read,tail⟩ := trace
    rcases List.mem_cons.mp hit with eqn | mem
    · subst p
      rw [trace_off ps _ _ tail t (fun q hq eq => fresh (List.mem_map.mpr ⟨q,hq,eq⟩)),
        Function.update_self]
      exact read c s j
    · rw [ih _ tail nd mem,Function.update_of_ne]
      intro eqn
      exact fresh (eqn ▸ List.mem_map_of_mem mem)

/-- Read any returning helper at its scheduled position, including a call
that reuses the previous slot without touching the owner. -/
theorem scheduledSlotRead (n : Fin 9) (run : Fin 32 × Fin 5) (before) {w W : ℕ} (a b)
    (trace : HelperSlotTrace w W (scheduledSlotChanges n run before) a b) (h : Fin 439) :
    let change := helperSlotChange n run before h
    ∀ c s j, b change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
      a change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro change c s j
  by_cases same : change.2.1 = change.2.2
  · let pos := fun i : Option (Fin 56) => FlatCoordinateLayout.index (helperSlotField c i (w+1) s) j
    change b change.1 (pos change.2.2) = a change.1 (pos change.2.1)
    rw [same]
    apply congrFun
    apply trace_off _ _ _ trace
    intro p hp eqn
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    have ij := congrArg Fin.val (ownerTape_injective n run.1 run.2 eqn)
    have kh : k = h := Fin.ext (Nat.add_left_cancel ij)
    subst k
    exact (bne_iff_ne.mp (List.mem_filter.mp hk).2) same
  · apply trace_slot _ _ _ trace (scheduledSlotChanges_unique ..)
    apply List.mem_map.mpr
    exact ⟨h,List.mem_filter.mpr ⟨List.mem_finRange _,bne_iff_ne.mpr same⟩,rfl⟩

open Stack Host Cover.Fallback in
/-- The physical batch selected by the incoming chart history works for
all parent widths with one charge coefficient per scheduled invocation. -/
theorem scheduledSlotPack_exec [M8.Machine.Net] {P U : Type} (n : Fin 9) (run : Fin 32 × Fin 5)
    (prefixRuns : List (Fin 32 × Fin 5))
    (body : P → Pr P ((rowSwapBlock.tapes+35)+142081) rowSwapBlock.states prime U) :
    let before := prefixRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)
    ∃ code C, ∀ w W : ℕ, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ v (owners : Stacks 142081 prime) (data : Fin 142081 → Fin V → ZMod 2),
      (∀ t z, readAt blank (owners.L t) (owners.R t) z = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data t) z) →
      ∃ z F, ∃ time : ℕ, ∃ result : Fin 142081 → Fin V → ZMod 2, z.user = v.user ∧
        (time : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        Exec body code (mk v (helperPackInput w W owners)) time (mk z F) ∧
        (∀ t : Fin 142081, ∀ j, readAt blank (F.L (t.natAdd (rowSwapBlock.tapes+35)))
          (F.R (t.natAdd (rowSwapBlock.tapes+35))) j = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ result t) j) ∧
        (∀ t, (∀ h : Fin 439, (helperSlotChange n run before h).1 ≠ t) → result t = data t) ∧
        ∀ h : Fin 439, let change := helperSlotChange n run before h
          ∀ c s j, result change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro before
  obtain ⟨code,C,batch⟩ := helperSlotBatch_fromOwners (scheduledSlotChanges n run before) body
  refine ⟨code,C,?_⟩
  intro w W live M V v owners data input
  obtain ⟨z,F,time,result,user,cost,exec,reads,trace⟩ := batch w W live v owners data input
  refine ⟨z,F,time,result,user,cost,exec,reads,?_,scheduledSlotRead n run before _ _ trace⟩
  intro t off
  apply trace_off _ _ _ trace
  rintro p hp
  obtain ⟨h,_,rfl⟩ := List.mem_map.mp hp
  exact off h

end IntegerMultBounds.MathlibTM2.M6.BitNode
