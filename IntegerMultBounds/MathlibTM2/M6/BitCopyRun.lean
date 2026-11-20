module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalRun
public import IntegerMultBounds.MathlibTM2.M6.ModularScatter
public import IntegerMultBounds.MathlibTM2.M6.BitInvocation
public import IntegerMultBounds.Machine.ExactFrame
public import IntegerMultBounds.Networks.AffineFieldBijective
public import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
public import IntegerMultBounds.Networks.AffineFieldCoordinates
public import IntegerMultBounds.Machine.SparseRoleCircuit

/-! Copy, fan out, and clear the PR589 temporary on the scheduled owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
variable {a : ℕ}

noncomputable def ownerTape (n : Fin 9) (r : Fin 32) (d : Fin 5) (j : Fin 661) : Fin 142081 :=
  ((Fin.cast card_role) (Fintype.equivFin Role (owner n r d j))).castSucc

theorem ownerTape_injective (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    Function.Injective (ownerTape n r d) := by
  intro i j eq
  apply Fin.ext
  apply owner_injective n r d i i.isLt j j.isLt
  exact (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))

private theorem fanout {t N : ℕ} (src : Fin t) (targets : List (Fin t)) (fresh : src ∉ targets)
    (unique : targets.Nodup) (data : Fin t → Fin N → ZMod 2) :
    let gates := targets.attach.map fun dst => (⟨src,dst.val,fun h => fresh (h ▸ dst.property)⟩ : PointwiseRoleGate.Gate t)
    PointwiseRoleCircuit.execute (PointwiseBinary.xorSymbol (a := a)) gates (SparseRoleCircuit.encoded data) =
      SparseRoleCircuit.encoded (fun j i => if j ∈ targets then data j i + data src i else data j i) := by
  induction targets generalizing data with
  | nil => rfl
  | cons j js ih =>
    have off : src ≠ j := fun eq => fresh (eq ▸ List.mem_cons_self)
    have tail : src ∉ js := fun mem => fresh (List.mem_cons_of_mem _ mem)
    let next := Function.update data j (fun i => data j i + data src i)
    have step : PointwiseRoleGate.applyGate ⟨src,j,off⟩ PointwiseBinary.xorSymbol
        (SparseRoleCircuit.encoded (a := a) data) = SparseRoleCircuit.encoded next := by
      funext k i
      by_cases h : k = j
      · subst k
        simp [PointwiseRoleGate.applyGate,SparseRoleCircuit.encoded,next,SparseRoleCircuit.encode_add]
      · simp [PointwiseRoleGate.applyGate,SparseRoleCircuit.encoded,next,h]
    simp only [List.attach_cons,List.map_cons,List.map_map,PointwiseRoleCircuit.execute,step]
    trans SparseRoleCircuit.encoded (fun k i => if k ∈ js then next k i + next src i else next k i)
    · exact ih tail unique.of_cons next
    congr 1
    funext k i
    by_cases eq : k = j
    · subst k
      simp [next,unique.notMem]
    · simp [next,eq,off]

/-- Fan out the common-frame temporary to every target of a selected COPY
window. All retained owners outside that window keep their original streams. -/
theorem copyAdds_hoare (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) :
    let regs := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let tapes := regs.map (ownerTape n r d)
    ∃ (states : ℕ) (program : Program (142081+2) states a), ∀ {N : ℕ} (data : Fin 142081 → Fin N → ZMod 2)
      (background : Fin 142081 → ℤ → Fin (a+4)) (origins : Fin 142081 → ℤ)
      (bs : List Bool), Counter.value bs = N →
      HoareTime program (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded data) bs)
        (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded
          (fun j i => if j ∈ tapes then data j i + data (Fin.last 142080) i else data j i)) bs)
        (life.targets.length*(14*N+14*bs.length+34)) := by
  intro regs tapes
  have unique : regs.Nodup := by
    apply List.Nodup.of_map (f := Fin.val)
    simpa [regs,List.map_map,Function.comp_def] using (Copy.wellformed life scheduled).1
  have nodup := unique.map (ownerTape_injective n r d)
  have fresh : Fin.last 142080 ∉ tapes := by
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    exact Fin.castSucc_ne_last _ eq
  let gates := tapes.attach.map fun dst => (⟨Fin.last 142080,dst.val,fun h => fresh (h ▸ dst.property)⟩ : PointwiseRoleGate.Gate 142081)
  refine ⟨_,PointwiseRoleCircuit.program (PointwiseBinary.xorSymbol (a := a)) gates,?_⟩
  intro N data background origins bs count
  have exec := PointwiseRoleCircuit.circuit_hoare PointwiseBinary.xorSymbol gates background origins
    (SparseRoleCircuit.encoded data) bs count
  have action := fanout (a := a) _ tapes fresh nodup data
  change PointwiseRoleCircuit.execute _ gates _ = _ at action
  rw [action] at exec
  simpa only [gates,tapes,regs,List.length_map,List.length_attach] using exec

/-- Row-major tape address used by the flat coordinate stages, with the
spectator record following the two field halves. -/
noncomputable def copyAddress {Q W : ℕ} [NeZero Q] :
    Fin (Q^16*W) ≃ Swap.Shear.State (Fin 8) (ZMod Q) × Fin W :=
  let halves : Swap.Shear.State (Fin 8) (ZMod Q) ≃ (Fin 16 → ZMod Q) :=
    { toFun := AffineFieldCoordinates.embed
      invFun := fun x => (fun i => x (Fin.castAdd 8 i), fun i => x (Fin.natAdd 8 i))
      left_inv := fun s => Prod.ext (funext (AffineFieldCoordinates.embed_h s)) (funext (AffineFieldCoordinates.embed_d s))
      right_inv := fun x => by
        funext i
        exact Fin.addCases (fun _ => Fin.addCases_left _)
          (fun _ => Fin.addCases_right _) i }
  (((halves.trans FlatCoordinateLayout.rankEquiv).prodCongr (Equiv.refl (Fin W))).trans
    finProdFinEquiv).symm

@[simp] theorem copyAddress_index {Q W : ℕ} [NeZero Q]
    (s : Swap.Shear.State (Fin 8) (ZMod Q)) (j : Fin W) :
    copyAddress.symm (s,j) = FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j := rfl

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateLayout (rank)
open RecursiveInterchangeLayout (Descriptor volume)

/-- The two seven-coordinate prefixes form the H and D fields of one child. -/
noncomputable def copyChild (w W : ℕ) : Descriptor := ⟨1,1,1,7*w,prime^w,prime^w*W⟩

theorem copyChild_volume (w W : ℕ) : volume prime (copyChild w W) = (prime^w)^16*W := by
  simp only [volume, copyChild, one_mul, ← pow_mul, Nat.mul_comm w 16]
  rw [show 16*w = 7*w+w+7*w+w by omega]
  simp only [pow_add]
  ring

section
variable {w W : ℕ}
local instance : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

open M8.Machine.Segments in
/-- A basis-change segment starts and ends in the same binary payload encoding
as the COPY child. Its fixed program charges one linear pass constant. -/
theorem copySegment_runs (ops : List (AffineFieldProgram.Op (Fin 8) ℚ)) (good : Good ops)
    (hW : 0 < W) (x : Fin ((prime^w)^16*W) → ZMod 2) :
    let q := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    (∀ op ∈ q, AffineFieldProgram.Legal op) →
    let stages := description ops good
    let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
        (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
    ∃ y, HoareTime (FlatCoordinateCleanSchedule.program stages) (fun z => z = bank x)
      (fun z => z = bank y) (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
      ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (AffineFieldProgram.run q s)) j) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro q legal stages bank
  let perm := Equiv.ofBijective _ (AffineFieldBijective.run_bijective q legal)
  let addr := copyAddress (Q := prime^w) (W := W)
  let y := fun i => x (addr.symm (perm.symm (addr i).1,(addr i).2))
  have moves (s) (j : Fin W) : y (addr.symm (perm s,j)) = x (addr.symm (s,j)) := by
    simp only [y,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  let encoded := fun i => SparseRoleCircuit.encode (a := 0) (x i)
  have exactArray : FlatCoordinateInitializedSchedule.array stages w W hW encoded =
      fun i => SparseRoleCircuit.encode (y i) := by
    funext i
    obtain ⟨⟨s,j⟩,rfl⟩ := addr.symm.surjective i
    obtain ⟨s,rfl⟩ := perm.surjective s
    rw [moves]
    exact array_entry ops good w W hW encoded s j
  refine ⟨y, ?_, moves⟩
  apply (realizes ops good w W hW encoded).consequence (fun _ h => h) _ le_rfl
  intro z hz
  exact hz.1.trans (congrArg (fun a => SharedBankStageInput.raw
    (FlatCoordinateShiftSharedBank.common a) (FlatCoordinateCleanSchedule.tapeCount stages)) exactArray)

noncomputable def copyChildAddress (h d : Fin 7 → ZMod (prime^w))
    (u v : Fin 1 → ZMod (prime^w)) (j : Fin W) : RecursiveInterchangeScaling.Address (copyChild w W) :=
  let field (x : Fin 7 → ZMod (prime^w)) : Fin (prime^(7*w)) := Fin.cast (by rw [← pow_mul, Nat.mul_comm w 7])
    (rank x)
  let low (x : Fin 1 → ZMod (prime^w)) := Fin.cast (pow_one _) (rank x)
  ⟨(0 : Fin 1),(0 : Fin 1),(0 : Fin 1),field h,low u,field d,finProdFinEquiv (low v,j)⟩

theorem copyChild_index (h d : Fin 7 → ZMod (prime^w)) (u v : Fin 1 → ZMod (prime^w)) (j : Fin W) :
    Fin.cast (copyChild_volume w W) (RecursiveInterchangeScaling.index (copyChildAddress h d u v j)) =
      FlatCoordinateLayout.index (AffineFieldCoordinates.embed (Fin.addCases h u, Fin.addCases d v)) j := by
  apply Fin.ext
  rw [Fin.val_cast, RecursiveInterchangeScaling.index_val, FlatCoordinateLayout.index_val]
  simp only [copyChildAddress, copyChild, RecursiveInterchangeLayout.index, Fin.val_zero,
    zero_mul, zero_add, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  have packed := ArbitraryWidthSliceTranspose.rank_append (Fin.addCases h u) (Fin.addCases d v)
  change (rank (AffineFieldCoordinates.embed (Fin.addCases h u,Fin.addCases d v))).val = _ at packed
  rw [packed, ArbitraryWidthSliceTranspose.rank_append h u, ArbitraryWidthSliceTranspose.rank_append d v]
  have pack (q H D U V t z : ℕ) :
      ((H*q^w+U)*q^(7*w)+D)*(q^w*t)+(z+t*V) =
      ((H*(q^w)^1+U)*(q^w)^(7+1)+(D*(q^w)^1+V))*t+z := by
    have power : (q^w)^(7+1) = q^(7*w)*q^w :=
      (pow_succ _ 7).trans (congrArg (· * q^w) ((pow_mul q w 7).symm.trans
        (congrArg (q^·) (Nat.mul_comm w 7))))
    rw [power,pow_one]
    ring
  exact pack _ _ _ _ _ _ _

/-- One transpose on the child sends both prefixes to the opposite halves and
preserves the low coordinates and trailing record in the original array. -/
theorem copyChild_transpose {α : Type*} (x : Fin ((prime^w)^16*W) → α)
    (h d : Fin 7 → ZMod (prime^w)) (u v : Fin 1 → ZMod (prime^w)) (j : Fin W) :
    Shared50RecursiveNodeRows.transpose (v := copyChild w W) (one_dvd _)
      (fun i => x (Fin.cast (copyChild_volume w W) i))
      (RecursiveInterchangeScaling.index (copyChildAddress d h u v j)) =
      x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (Fin.addCases h u, Fin.addCases d v)) j) := by
  rw [← copyChild_index]
  exact Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) _ _ (copyChildAddress h d u v j)

private theorem copyInterval_run {R : Type*} [CommRing R]
    (h d : Fin 7 → R) (u v : Fin 1 → R) :
    IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) (Fin.append h u, Fin.append d v) =
      (Fin.append d u, Fin.append h v) := by
  rw [intervalSwaps_run]
  apply Prod.ext <;> funext k <;> refine Fin.addCases (m := 7) (n := 1) (fun i => ?_) (fun i => ?_) k
  all_goals simp [M8.Exchange.exchange, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_diagonal,
    Fin.append, Fin.val_castAdd, Fin.val_natAdd, i.isLt]

/-- The one child transpose realizes the selected interval instruction at every
address of the original temporary, including its spectator record. -/
theorem copyChild_interval {α : Type*} (x : Fin ((prime^w)^16*W) → α)
    (s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w))) (j : Fin W) :
    let atState := fun t => FlatCoordinateLayout.index (AffineFieldCoordinates.embed t) j
    Shared50RecursiveNodeRows.transpose (v := copyChild w W) (one_dvd _)
      (fun i => x (Fin.cast (copyChild_volume w W) i))
      (Fin.cast (copyChild_volume w W).symm
        (atState (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) s))) = x (atState s) := by
  intro atState
  obtain ⟨h,d⟩ := s
  obtain ⟨h,u,rfl⟩ : ∃ (a : Fin 7 → _) (b : Fin 1 → _), h = Fin.append a b :=
    ⟨_,_,(Fin.append_castAdd_natAdd (m := 7) (n := 1)).symm⟩
  obtain ⟨d,v,rfl⟩ : ∃ (a : Fin 7 → _) (b : Fin 1 → _), d = Fin.append a b :=
    ⟨_,_,(Fin.append_castAdd_natAdd (m := 7) (n := 1)).symm⟩
  rw [copyInterval_run]
  dsimp only [atState, Fin.append]
  rw [← copyChild_index d h u v j, Fin.cast_cast, Fin.cast_eq_self]
  exact copyChild_transpose x h d u v j

open M8.Machine.ArbitraryWidthOriginalRun (input program cost)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

/-- Execute the middle of COPY on the designated caller tape, with the
descriptor headers at their binary words and the private bank clean. -/
theorem copyChild_runs [M8.Machine.Net] {t : ℕ} (caller : Tapes t prime)
    (headers : Fin 6 → Fin t) (source : Fin t) (hw : 0 < w) (hW : 0 < W)
    (hs : Fin 6 → List Bool) (valid : RecursiveDimensionBank.Headers (copyChild w W) hs)
    (tapes : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (heads : ∀ i, caller.head (headers i) = 1)
    (x : Fin ((prime^w)^16*W) → ZMod 2)
    (payload : caller.tape source = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i)))
    (origin : caller.head source = 0) :
    ∃ y : Fin (volume prime (copyChild w W)) → ZMod 2,
      HoareTime (program headers source) (fun z => z = input caller)
        (fun z => z = input (SharedPlacementAlphabet.setTape caller source (sourceWord y) 0))
        (cost (copyChild w W) hs) ∧
      ∀ s j, y (Fin.cast (copyChild_volume w W).symm (FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) s)) j)) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  have pos := pow_pos Shared50ModularControl.prime_prime.pos w
  have hp : (copyChild w W).Positive := ⟨Nat.zero_lt_one, Nat.zero_lt_one, Nat.zero_lt_one, pos, Nat.mul_pos pos hW⟩
  exact ⟨_, M8.Machine.ArbitraryWidthOriginalRun.runs caller headers source _ hs hp
    (Nat.mul_pos (by decide) hw) valid tapes heads _ payload origin, copyChild_interval x⟩

private theorem sourceWord_cast {v : Descriptor} {N : ℕ} (size : volume prime v = N)
    (x : Fin N → ZMod 2) :
    sourceWord (fun i => x (Fin.cast size i)) =
      putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)) := by
  subst N
  rw [M8.Machine.ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq]
  unfold RadixHighBlockJoinLoop.word
  congr 2

def segmentSource (stages : List (FlatCoordinateSchedule.Op 16)) :
    Fin (FlatCoordinateCleanSchedule.tapeCount stages) :=
  ⟨0, by
    have h := FlatCoordinateInitializedSchedule.skeleton_tapes_ge stages
    unfold FlatCoordinateCleanSchedule.tapeCount
    omega⟩

/-- Slot zero of a clean basis-change bank is exactly the child's payload
tape, including its head position and its blank exterior. -/
theorem copySegment_source (stages : List (FlatCoordinateSchedule.Op 16))
    (x : Fin ((prime^w)^16*W) → ZMod 2) :
    let n := FlatCoordinateCleanSchedule.tapeCount stages
    let bank := SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common
      (d := 16) (b := w) (W := W) (fun i => SparseRoleCircuit.encode (x i))) n
    let slot := segmentSource stages
    bank.head slot = 0 ∧ bank.tape slot = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i)) := by
  intro n bank slot
  refine ⟨rfl,?_⟩
  apply congrArg (fun xs => FlatRepeatedControlNormalize.encoded (radix := prime)
    (putWord (fun _ => blank) 0 xs))
  exact List.ofFn_congr (copyChild_volume w W).symm (fun i => SparseRoleCircuit.encode (a := 0) (x i))


private theorem segmentWorkspace_eq (stages : List (FlatCoordinateSchedule.Op 16))
    (x y : Fin ((prime^w)^16*W) → ZMod 2) :
    let bank := fun (z : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
        (fun i => SparseRoleCircuit.encode (z i))) (FlatCoordinateCleanSchedule.tapeCount stages)
    let spare := fun z => SharedPlacementAlphabet.setTape (bank z) (segmentSource stages) (fun _ => blank) 0
    spare x = spare y := by
  intro bank spare
  apply congrArg₂ Tapes.mk
  · rfl
  · funext k
    by_cases eq : k = segmentSource stages
    · simp [eq]
    · simp only [Function.update_of_ne eq, bank, SharedBankStageInput.raw]
      split
      next h =>
        have nz : k.val ≠ 0 := fun zero => eq (Fin.ext zero)
        have i : (⟨k.val,h⟩ : Fin 4) = 1 ∨ (⟨k.val,h⟩ : Fin 4) = 2 ∨ (⟨k.val,h⟩ : Fin 4) = 3 := by
          simp only [Fin.ext_iff]; omega
        rcases i with e | e | e <;> rw [e] <;> rfl
      next => rfl

open M8.Machine.Segments SharedPlacementAlphabet in
/-- Place the basis change on a caller's selected tape, leaving all other
caller tapes stationary and the segment's original source slot blank. -/
theorem copySegment_placed {t : ℕ} (src : Fin t) (ops : List (AffineFieldProgram.Op (Fin 8) ℚ))
    (good : Good ops) (hW : 0 < W) (caller : Tapes t prime) (x : Fin ((prime^w)^16*W) → ZMod 2)
    (head : caller.head src = 0)
    (payload : caller.tape src = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i))) :
    let q := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    (∀ op ∈ q, AffineFieldProgram.Legal op) →
    let stages := description ops good
    let slot := segmentSource stages
    let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
      (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
        (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
    let workspace := fun y => setTape (bank y) slot (fun _ => blank) 0
    ∃ y : Fin ((prime^w)^16*W) → ZMod 2, HoareTime (Placement.placed (FlatCoordinateCleanSchedule.program stages) (sharedPlacement src slot))
      (fun z => z = caller.append (workspace x))
      (fun z => z = (setTape caller src
        (sourceWord (fun i => y (Fin.cast (copyChild_volume w W) i))) 0).append (workspace x))
      (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
      ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (AffineFieldProgram.run q s)) j) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro q legal stages slot bank workspace
  obtain ⟨y,run,moves⟩ := copySegment_runs ops good hW x legal
  have hx := copySegment_source stages x
  have hy := copySegment_source stages y
  change (bank x).head slot = 0 ∧ (bank x).tape slot = _ at hx
  change (bank y).head slot = 0 ∧ (bank y).tape slot = _ at hy
  have placed := shared_hoare run caller src slot (fun _ => blank) 0 (payload.trans hx.2.symm) (head.trans hx.1.symm)
  refine ⟨y,?_,moves⟩
  have same : workspace x = workspace y := segmentWorkspace_eq stages x y
  rw [← hy.2, ← hy.1]
  apply placed.consequence (fun _ h => h) _ le_rfl
  intro z hz
  exact hz.trans (congrArg _ same.symm)

open M8.Machine.Segments SharedPlacementAlphabet M8.Machine.ArbitraryWidthOriginalRun in
/-- Run one basis pass followed by the grouped child on the same caller tape.
The six prepared header tapes are outside the payload slot. -/
theorem copyEnterChild_runs [M8.Machine.Net] {t : ℕ} (src : Fin t) (headers : Fin 6 → Fin t)
    (distinct : ∀ i, headers i ≠ src) (ops : List (AffineFieldProgram.Op (Fin 8) ℚ))
    (good : Good ops) (hw : 0 < w) (hW : 0 < W) (caller : Tapes t prime)
    (x : Fin ((prime^w)^16*W) → ZMod 2) (hs : Fin 6 → List Bool)
    (valid : RecursiveDimensionBank.Headers (copyChild w W) hs)
    (tapes : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (heads : ∀ i, caller.head (headers i) = 1) (head : caller.head src = 0)
    (payload : caller.tape src = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i))) :
    let q := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    (∀ op ∈ q, AffineFieldProgram.Legal op) →
    let stages := description ops good
    let n := FlatCoordinateCleanSchedule.tapeCount stages
    let slot := segmentSource stages
    let work := setTape (SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common
      (d := 16) (b := w) (W := W) (fun i => SparseRoleCircuit.encode (x i))) n) slot (fun _ => blank) 0
    let basis := Placement.placed (FlatCoordinateCleanSchedule.program stages) (sharedPlacement src slot)
    let enter := extendBanks (extend (extend basis 16) 19)
    let child := program (fun i => Fin.castAdd n (headers i)) (Fin.castAdd n src)
    ∃ y : Fin (volume prime (copyChild w W)) → ZMod 2,
      HoareTime (seq enter child) (fun z => z = input (caller.append work))
        (fun z => z = input ((setTape caller src (sourceWord y) 0).append work))
        (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W) + 1 + cost (copyChild w W) hs) ∧
      ∀ s j, y (Fin.cast (copyChild_volume w W).symm (FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7)
          (AffineFieldProgram.run q s))) j)) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro q legal stages n slot work basis enter child
  obtain ⟨loaded,pass,move⟩ := copySegment_placed src ops good hW caller x head payload legal
  let next := setTape caller src (sourceWord (fun i => loaded (Fin.cast (copyChild_volume w W) i))) 0
  have lifted := extend_banks_hoare (hoare_extend_eq (hoare_extend_eq pass (FixedHeaderBankCopy.empty 16))
    M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  change HoareTime enter (fun z => z = input (caller.append work)) (fun z => z = input (next.append work)) _ at lifted
  obtain ⟨y,swap,action⟩ := copyChild_runs (next.append work) (fun i => Fin.castAdd n (headers i))
    (Fin.castAdd n src) hw hW hs valid (x := loaded)
    (by intro i; simpa [Tapes.append,next,setTape,distinct] using tapes i)
    (by intro i; simpa [Tapes.append,next,setTape,distinct] using heads i)
    (by simp [Tapes.append,next,setTape]) (by simp [Tapes.append,next,setTape])
  rw [setTape_append_left] at swap
  simp only [next,setTape_setTape] at swap
  exact ⟨y,lifted.seq swap,fun s j => (action _ j).trans (move s j)⟩

noncomputable def basisWorkspace (stages : List (FlatCoordinateSchedule.Op 16))
    (x : Fin ((prime^w)^16*W) → ZMod 2) :=
  SharedPlacementAlphabet.setTape (SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common
    (d := 16) (b := w) (W := W) (fun i => SparseRoleCircuit.encode (x i)))
    (FlatCoordinateCleanSchedule.tapeCount stages)) (segmentSource stages) (fun _ => blank) 0

open M8.Machine.Segments SharedPlacementAlphabet M8.Machine.ArbitraryWidthOriginalRun in
/-- Both fixed basis passes surround one child call on the same payload tape.
Only the designated tape changes in the prepared caller bank. -/
theorem copyMove_runs [M8.Machine.Net] {t : ℕ} (src : Fin t) (headers : Fin 6 → Fin t)
    (distinct : ∀ i, headers i ≠ src) (C : Matrix (Fin 8) (Fin 8) ℚ)
    (rev : CopyBasisPass C.adjugate)
    (fwd : CopyBasisPass C)
    (hw : 0 < w) (hW : 0 < W) (caller : Tapes t prime)
    (x : Fin ((prime^w)^16*W) → ZMod 2) (hs : Fin 6 → List Bool)
    (valid : RecursiveDimensionBank.Headers (copyChild w W) hs)
    (tapes : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (heads : ∀ i, caller.head (headers i) = 1) (head : caller.head src = 0)
    (payload : caller.tape src = sourceWord (fun i => x (Fin.cast (copyChild_volume w W) i))) :
    let spec := List.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (prime^w)))
    let A := description _ rev.good
    let B := description _ fwd.good
    let n := FlatCoordinateCleanSchedule.tapeCount A
    let m := FlatCoordinateCleanSchedule.tapeCount B
    let bank := fun v : Tapes t prime => input ((v.append (basisWorkspace B x)).append (basisWorkspace A x))
    let source := Fin.castAdd m src
    let enter := Placement.placed (FlatCoordinateCleanSchedule.program A) (sharedPlacement source (segmentSource A))
    let child := program (fun i => Fin.castAdd n (Fin.castAdd m (headers i))) (Fin.castAdd n source)
    let leave := Placement.placed (FlatCoordinateCleanSchedule.program B) (sharedPlacement src (segmentSource B))
    let machine := seq (seq (extendBanks (extend (extend enter 16) 19)) child)
      (extendBanks (extend (extend (extend leave n) 16) 19))
    ∃ y : Fin ((prime^w)^16*W) → ZMod 2,
      HoareTime machine (fun z => z = bank caller)
        (fun z => z = bank (setTape caller src (sourceWord (fun i => y (Fin.cast (copyChild_volume w W) i))) 0))
        ((FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant B) *
          ((prime^w)^16*W) + cost (copyChild w W) hs + 2) ∧
      ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (AffineFieldProgram.run (spec (rationalMoveWord 0 7 C)) s)) j) =
        x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro spec A B n m bank source enter child leave machine
  obtain ⟨mid,first,action⟩ := copyEnterChild_runs source (fun i => Fin.castAdd m (headers i))
    (fun i eq => distinct i (Fin.ext (congrArg (fun k : Fin (t+m) => k.val) eq))) _ rev.good hw hW (caller.append (basisWorkspace B x))
    x hs valid (by intro i; simpa [Tapes.append] using tapes i)
    (by intro i; simpa [Tapes.append] using heads i) (by simpa [source,Tapes.append] using head)
    (by simpa [source,Tapes.append] using payload) (rev.legal w)
  let next := setTape caller src (sourceWord mid) 0
  let bits := fun i => mid (Fin.cast (copyChild_volume w W).symm i)
  obtain ⟨y,last,move⟩ := copySegment_placed src _ fwd.good hW next bits
    (by simp [next,setTape]) (by simp [next,setTape,bits]) (fwd.legal w)
  have same : basisWorkspace B bits = basisWorkspace B x := segmentWorkspace_eq B bits x
  change HoareTime leave (fun z => z = next.append (basisWorkspace B bits))
    (fun z => z = (setTape next src _ 0).append (basisWorkspace B bits)) _ at last
  rw [same] at last
  simp only [next,setTape_setTape] at last
  have lifted := extend_banks_hoare (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq last
    (basisWorkspace A x)) (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  change HoareTime _ (fun z => z = bank caller)
    (fun z => z = input ((setTape (caller.append (basisWorkspace B x)) (Fin.castAdd m src) (sourceWord mid) 0).append
      (basisWorkspace A x))) _ at first
  rw [setTape_append_left] at first
  refine ⟨y, ?_, ?_⟩
  · have bill (a b N c : ℕ) : (a+b)*N+c+2 = (a*N+1+c)+1+b*N := by ring
    rw [bill]
    exact first.seq lifted
  · intro s j
    rw [rationalMoveWord_run, move]
    exact action s j

/-- The child starts directly on the pointwise gate's temporary. Its source
word and head already have the required representation on the owner bank. -/
theorem copyChild_bank_runs [M8.Machine.Net] {t : ℕ} (tmp : Fin t) (hw : 0 < w) (hW : 0 < W)
    (bs : List Bool) (data : Fin t → Fin ((prime^w)^16*W) → ZMod 2)
    (hs : Fin 6 → List Bool) (valid : RecursiveDimensionBank.Headers (copyChild w W) hs) :
    let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded X) bs
    let headerBank : Tapes 6 prime := ⟨fun _ => 1, fun i => RadixZeroFill.encodedBinary (hs i)⟩
    let caller := (bank data).append headerBank
    let src := Fin.castAdd 6 (Fin.castAdd 2 tmp)
    ∃ y : Fin ((prime^w)^16*W) → ZMod 2,
      HoareTime (program (Fin.natAdd (t+2)) src) (fun z => z = input caller)
        (fun z => z = input ((bank (Function.update data tmp y)).append headerBank))
        (cost (copyChild w W) hs) ∧
      ∀ s j, y (FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps 0 7) s)) j) =
        data tmp (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  intro bank headerBank caller src
  obtain ⟨changed,run,action⟩ := copyChild_runs caller (Fin.natAdd (t+2)) src hw hW hs valid
    (x := data tmp) (by intro i; simp [caller,Tapes.append,headerBank])
    (by intro i; simp [caller,Tapes.append,headerBank]) (by
      rw [sourceWord_cast]
      simp [caller,src,bank,PointwiseRoleGate.bank,Tapes.append]
      rfl) (by simp [caller,src,bank,PointwiseRoleGate.bank,Tapes.append])
  let y := fun i => changed (Fin.cast (copyChild_volume w W).symm i)
  refine ⟨y, ?_, action⟩
  have wordEq : sourceWord changed = putWord (fun _ => blank) 0
      (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (y i)) := by
    simpa only [y,Fin.cast_cast,Fin.cast_eq_self] using sourceWord_cast (copyChild_volume w W) y
  have updated : SharedPlacementAlphabet.setTape caller src (sourceWord changed) 0 =
      (bank (Function.update data tmp y)).append headerBank := by
    simp only [caller,src,bank,PointwiseRoleGate.bank,SharedPlacementAlphabet.setTape_append_left]
    congr 2
    apply congrArg₂ Tapes.mk <;> funext k <;> by_cases eq : k = tmp
    all_goals simp [eq,wordEq]
    all_goals congr 2; funext i; simp [SparseRoleCircuit.encoded,eq]
  rwa [updated] at run

end

/-- The physical COPY bank contains the caller, six descriptor headers,
both basis workspaces and the private tapes of the chosen child machine. -/
noncomputable def copyPrepared [M8.Machine.Net] {t w W : ℕ} (A B : List (FlatCoordinateSchedule.Op 16))
    (x : Fin ((prime^w)^16*W) → ZMod 2) (v : Tapes t prime) (hs : Fin 6 → List Bool) :=
  let hdr : Tapes 6 prime := ⟨fun _ => 1, fun i => RadixZeroFill.encodedBinary (hs i)⟩
  M8.Machine.ArbitraryWidthOriginalRun.input (((v.append hdr).append (basisWorkspace B x)).append (basisWorkspace A x))

open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open M8.Machine.Segments M8.Machine.ArbitraryWidthOriginalRun SharedPlacementAlphabet in
/-- Copy the retained owner into the temporary, convert its frame, fan out,
then clear it, charging both basis passes and one child transpose. -/
theorem copyWindow_hoare [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) (w : ℕ) (hw : 0 < w) :
    let src := ownerTape n r d ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let tmp := Fin.last 142080
    let regs := life.targets.attach.map fun j => (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let targets := regs.map (ownerTape n r d)
    let R := ZMod (Shared50ModularControl.prime^w)
    let S := Swap.Shear.State (Fin 8) R
    ∃ (frame : ℕ → FramedCircuit.Frame (ZMod 2) (S → ZMod 2))
      (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)),
      LocalMoveProfile word ∧ SelectedCopyWord w (word (life.sourceFrame,0)) ∧
      AffineFieldProgram.interchanges (word (life.sourceFrame,0)) = 7 ∧
      ∃ (C : Matrix (Fin 8) (Fin 8) ℚ) (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C),
      let A := description _ rev.good
      let B := description _ fwd.good
      let prepare := fun {W} => copyPrepared (t := 142081+2) (w := w) (W := W) A B
      ∃ (states : ℕ) (machine : Program _ states prime),
      ∀ {W : ℕ} (hW : 0 < W),
      let N := (Shared50ModularControl.prime^w)^16 * W
      let _ : NeZero (Shared50ModularControl.prime^w) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos w)⟩
      let addr : Fin N ≃ S × Fin W := copyAddress
      ∀ (data : Fin 142081 → Fin N → ZMod 2)
      (bs : List Bool) (hs : Fin 6 → List Bool), Counter.value bs = N →
      RecursiveDimensionBank.Headers (copyChild w W) hs →
      let frameOf := fun j => tapeFrame addr (frame j)
      let common := fun i => data src (addr.symm
        (AffineFieldProgram.run (word (life.sourceFrame,0)) (addr i).1,(addr i).2))
      let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) bs
      let output := Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0
      let stored := Copy.extendStored (fun j => data (ownerTape n r d j))
      HoareTime machine (fun z => z = prepare (data src) (bank data) hs) (fun z => z = prepare (data src) (bank output) hs)
        (((FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant B)*N + cost (copyChild w W) hs + 2) + (life.targets.length+2)*(14*N+14*bs.length+34)+1) ∧
      (∀ j : Fin 661, output (ownerTape n r d j) = Copy.execute frameOf life stored j) ∧
      output tmp = Copy.execute frameOf life stored 661 := by
  intro src tmp regs targets R S
  obtain ⟨frame,word,profile,windows⟩ := copyAddress_word w
  obtain ⟨selected,seven,invol,read⟩ := windows life scheduled
  let gate : PointwiseRoleGate.Gate 142081 := ⟨src,tmp,Fin.castSucc_ne_last _⟩
  let copy := fun (s _ : Fin (prime+4)) => s
  let erase := fun (_ _ : Fin (prime+4)) => SparseRoleCircuit.encode (a := prime) 0
  obtain ⟨_,adds,addRun⟩ := copyAdds_hoare (a := prime) n r d life scheduled
  refine ⟨frame,word,profile,selected,seven,?_⟩
  obtain ⟨C,rev,fwd,shape⟩ := selected
  refine ⟨C,rev,fwd,?_⟩
  intro A B prepare
  let site := Fin.castAdd 6 (Fin.castAdd 2 tmp)
  let nA := FlatCoordinateCleanSchedule.tapeCount A
  let nB := FlatCoordinateCleanSchedule.tapeCount B
  let liftGate {q} (g : Program (142081+2) q prime) :=
    extendBanks (extend (extend (extend (extend (extend g 6) nB) nA) 16) 19)
  let pre := Placement.placed (FlatCoordinateCleanSchedule.program A) (sharedPlacement (Fin.castAdd nB site) (segmentSource A))
  let child := program (fun i : Fin 6 => Fin.castAdd nA (Fin.castAdd nB (Fin.natAdd (142081+2) i)))
    (Fin.castAdd nA (Fin.castAdd nB site))
  let post := Placement.placed (FlatCoordinateCleanSchedule.program B) (sharedPlacement site (segmentSource B))
  let convert := seq (seq (extendBanks (extend (extend pre 16) 19)) child)
    (extendBanks (extend (extend (extend post nA) 16) 19))
  refine ⟨_,seq (seq (seq (liftGate (PointwiseRoleGate.program gate copy)) convert) (liftGate adds))
    (liftGate (PointwiseRoleGate.program gate erase)), ?_⟩
  intro W hW N inst addr data bs hs count valid frameOf common bank output stored
  let background := fun (_ : Fin 142081) (_ : ℤ) => (blank : Fin (prime+4))
  let origins := fun (_ : Fin 142081) => (0 : ℤ)
  let headers : Tapes 6 prime := ⟨fun _ => 1, fun i => RadixZeroFill.encodedBinary (hs i)⟩
  let copied := Function.update data tmp (data src)
  let caller := (bank copied).append headers
  have distinct (i : Fin 6) : Fin.natAdd (142081+2) i ≠ site := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [site,Fin.val_natAdd,Fin.val_castAdd] at h
    omega
  obtain ⟨moved,converted,forward⟩ := copyMove_runs site _ distinct C rev fwd hw hW caller (data src) hs valid
    (by intro i; simp [caller,Tapes.append,headers])
    (by intro i; simp [caller,Tapes.append,headers])
    (by simp [caller,bank,site,Tapes.append,PointwiseRoleGate.bank])
    (by rw [sourceWord_cast]; simp [caller,bank,site,Tapes.append,PointwiseRoleGate.bank,copied]; congr 2)
  rw [← shape] at forward
  have agree : moved = common := by
    funext i
    obtain ⟨⟨s,j⟩,rfl⟩ := addr.symm.surjective i
    have h := forward (AffineFieldProgram.run (word (life.sourceFrame,0)) s) j
    rw [invol] at h
    simp only [common, Equiv.apply_symm_apply]
    exact h
  have updated : setTape caller site (sourceWord (fun i => moved (Fin.cast (copyChild_volume w W) i))) 0 =
      (bank (Function.update data tmp moved)).append headers := by
    rw [sourceWord_cast]
    simp only [caller,site,bank,PointwiseRoleGate.bank,setTape_append_left]
    congr 2
    apply congrArg₂ Tapes.mk <;> funext k <;> by_cases eq : k = tmp
    all_goals simp [eq]
    all_goals congr 2 <;> funext i <;> simp [SparseRoleCircuit.encoded,copied,eq]
  rw [updated, agree] at converted
  have liftRun {q b} {g : Program (142081+2) q prime} {v v' : Tapes (142081+2) prime}
      (h : HoareTime g (fun z => z = v) (fun z => z = v') b) :
      HoareTime (liftGate g) (fun z => z = prepare (data src) v hs) (fun z => z = prepare (data src) v' hs) b :=
    extend_banks_hoare (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
      (hoare_extend_eq h headers) (basisWorkspace B (data src))) (basisWorkspace A (data src)))
      (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  have decoded : common = frameOf 0 ((frameOf life.sourceFrame).symm (data src)) := funext (read addr (data src))
  let loaded := Function.update data tmp common
  let added := fun j i => if j ∈ targets then loaded j i + loaded tmp i else loaded j i
  have add := addRun loaded background origins bs count
  change HoareTime adds (fun w => w = bank loaded) (fun w => w = bank added) _ at add
  have write (X : Fin 142081 → Fin N → ZMod 2) (op : Fin (prime+4) → Fin (prime+4) → Fin (prime+4))
      (value : Fin N → ZMod 2) (action : ∀ i, op (SparseRoleCircuit.encode (X src i))
        (SparseRoleCircuit.encode (X tmp i)) = SparseRoleCircuit.encode (value i)) :
      HoareTime (PointwiseRoleGate.program gate op) (fun w => w = bank X)
        (fun w => w = bank (Function.update X tmp value)) (14*N+14*bs.length+33) := by
    have step := PointwiseRoleGate.gate_hoare gate op background origins (SparseRoleCircuit.encoded X) bs count
    have same : PointwiseRoleGate.applyGate gate op (SparseRoleCircuit.encoded X) =
        SparseRoleCircuit.encoded (Function.update X tmp value) := by
      funext j i
      by_cases eq : j = tmp
      · subst j
        simpa [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded] using action i
      · simp [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded,eq]
    rw [same] at step
    exact step
  have done := (((liftRun (write data copy (data src) (fun _ => rfl))).seq converted).seq
    (liftRun add)).seq (liftRun (write added erase 0 (fun _ => rfl)))
  have cleaned : Function.update added tmp 0 =
      Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0 := by
    funext j i
    by_cases eq : j = tmp <;> simp [eq,added,loaded]
  rw [cleaned] at done
  refine ⟨?_,?_,?_⟩
  · convert done using 1
    ring
  · intro j
    have off : ownerTape n r d j ≠ tmp := Fin.castSucc_ne_last _
    have member : ownerTape n r d j ∈ targets ↔ j.val ∈ life.targets := by
      change ownerTape n r d j ∈ regs.map (ownerTape n r d) ↔ _
      rw [List.mem_map_of_injective (ownerTape_injective n r d)]
      constructor
      · intro mem
        obtain ⟨k,_,eq⟩ := List.mem_map.mp mem
        exact (congrArg Fin.val eq) ▸ k.property
      · intro mem
        exact List.mem_map.mpr ⟨⟨j.val,mem⟩,List.mem_attach ..,Fin.ext rfl⟩
    have wf := Copy.wellformed life scheduled
    have retained : stored life.source = data src := by
      simp [stored,Copy.extendStored,(Copy.source_bounds life scheduled).2,src]
    have old : stored j.val = data (ownerTape n r d j) := by simp [stored,Copy.extendStored,j.isLt]
    have distinct : j.val ≠ 661 := Nat.ne_of_lt j.isLt
    simp only [output,Function.update_of_ne off,Copy.execute,Function.update_of_ne distinct,
      Copy.addTargets_eq _ wf.1 wf.2.1,Function.update_self,old,retained,member,decoded]
    funext i
    split <;> rfl
  · simp [output,Copy.execute]

end IntegerMultBounds.MathlibTM2.M6.BitNode
