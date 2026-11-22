module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepNodeAddress
public import IntegerMultBounds.MathlibTM2.M6.BitNodeInterchange

/-! Recover physical reads of the complete node from its rational stream endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Host
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine Swap.Modular Matrix
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Read a full modular state through the same address map used by all the
node pieces, including the weighted parent chart. -/
private theorem modularEndpoint {w V : ℕ} (r : Role)
    (address : BankLane → Swap.Shear.State Axis (ZMod (prime^w)) → Fin V)
    (x y : Fin 142081 → Fin V → ZMod 2)
    (reads : let atLane := fun lane z => address lane (windowState w z)
      readLanes atLane y = runNode (readLanes atLane x)) (s : Swap.Shear.State Axis (ZMod (prime^w))) :
    let lane : BankLane := (r.replica,r.port,r.cls)
    let tape := bankTape r.bank lane
    y tape (address lane s) = x tape (address lane (s.2,s.1)) := by
  let M := prime^w
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let v := Sum.elim s.1 s.2
  let z := fun i => ((v i).val : ℚ)
  have swap : (exchange (1 : Matrix Axis Axis ℚ)).mulVec z = z ∘ Sum.swap := by
    funext i
    cases i <;> simp [exchange,fromBlocks_mulVec,Function.comp_apply]
  have input := addressMod_lift M v
  have output := addressMod_lift M (v ∘ Sum.swap)
  have act := congrFun reads r
  rw [runNode_interchange] at act
  have cell := congrFun act z
  simp only [along_apply,swap,readLanes,readRoles,windowState] at cell
  change addressMod M z = v at input
  change addressMod M (z ∘ Sum.swap) = v ∘ Sum.swap at output
  rw [input,output] at cell
  exact cell

/-- In the actual parent chart, the endpoint at any physical owner position
is obtained by decoding it, exchanging the two fields, and encoding again. -/
theorem nodeEndpoint_cell {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (r : Role) (x y : OwnerArray w B W)
    (reads : ∀ b j, let addr := fun z => nodeWindowEquiv w B W parent units (b,windowState w z,j)
      readRoles addr y = runNode (readRoles addr x)) :
    let chart := nodeWindowEquiv w B W parent units
    let tape := bankTape r.bank (r.replica,r.port,r.cls)
    ∀ i, let (b,s,j) := chart.symm i
         y tape i = x tape (chart (b,(s.2,s.1),j)) := by
  intro chart tape i
  obtain ⟨⟨b,s,j⟩,rfl⟩ := chart.surjective i
  rw [Equiv.symm_apply_apply]
  exact modularEndpoint r (fun _ v => chart (b,v,j)) x y (reads b j) s

/-- The physical handoff trace needs read equations only for sweeps and
remainders. Bridges and side exchange are already included in the trace theorem. -/
theorem nodeHandoff_cell {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (r : Role) (x y : OwnerArray w B W)
    (idle : Fin 9 → OwnerArray w B W → OwnerArray w B W → Prop) :
    let chart := nodeWindowEquiv w B W parent units
    let read := fun b j => readRoles (fun z => chart (b,windowState w z,j))
    (∀ n a d, sweepEffect n w B W a d → ∀ b j, read b j d = (Piece.stage n).run (read b j a)) →
    (∀ n a d, idle n a d → ∀ b j, read b j d = (Piece.remainder n.val).run (read b j a)) →
    nodeProgram.foldr (fun p cont a => ∃ d, nodeHandoffEffect w B W idle p a d ∧ cont d)
      (fun a => a = y) x →
    ∀ i, let (b,s,j) := chart.symm i
         let tape := bankTape r.bank (r.replica,r.port,r.cls)
         y tape i = x tape (chart (b,(s.2,s.1),j)) := by
  intro chart read sweep rest trace
  apply nodeEndpoint_cell parent units r x y
  intro b j
  exact nodeHandoffEffect_read _ (fun n a d h => sweep n a d h b j)
    (fun n a d h => rest n a d h b j) trace

/-- On the sweep's physical owner word, the complete logical node exchanges
the two charted coordinate fields, keeping the block and spectator fixed. -/
theorem sweepEndpoint_read {w B W : ℕ} (b : Fin B) (j : Fin W) (r : Role)
    (x y : OwnerArray w B W)
    (reads : readLanes (sweepAddress b j) y = runNode (readLanes (sweepAddress b j) x)) :
    let tape := bankTape r.bank (r.replica,r.port,r.cls)
    let addr := fun s => stagedOwnerIndex b (FlatCoordinateLayout.index
      (helperSlotField (port r.port.val) none w s) j)
    ∀ s, y tape (addr s) = x tape (addr (s.2,s.1)) := by
  intro tape addr s
  exact modularEndpoint r (fun lane v => stagedOwnerIndex b (FlatCoordinateLayout.index
    (helperSlotField (port lane.2.1.val) none w v) j)) x y reads s

/-- The port chart is onto, so the exchange holds at every physical digit
vector, with no restriction on its representation by a rational address. -/
theorem sweepEndpoint_digits {w B W : ℕ} (b : Fin B) (j : Fin W) (r : Role)
    (x y : OwnerArray w B W)
    (reads : readLanes (sweepAddress b j) y = runNode (readLanes (sweepAddress b j) x))
    (digits : Fin 128 → ZMod (prime^w)) :
    let tape := bankTape r.bank (r.replica,r.port,r.cls)
    let addr := fun ds => stagedOwnerIndex b (FlatCoordinateLayout.index ds j)
    let order := helperFieldOrder none
    y tape (addr digits) = x tape (addr fun i => digits (order.symm (Sum.swap (order i)))) := by
  intro tape addr order
  obtain ⟨s,rfl⟩ := helperSlotField_surjective _ (port_checked _ r.port.isLt) none w digits
  have flip : helperSlotField (port r.port.val) none w (s.2,s.1) =
      fun i => helperSlotField (port r.port.val) none w s (order.symm (Sum.swap (order i))) := by
    funext i
    simp only [helperSlotField,Function.comp_apply,← show order = helperFieldOrder none from rfl,
      Equiv.apply_symm_apply]
    cases order i <;> rfl
  exact (sweepEndpoint_read b j r x y reads s).trans (congrArg (fun ds => x tape (addr ds)) flip)

/-- In physical radix order each half is an arbitrary integer below the
64-digit field size. Interchange preserves the inherited block and suffix. -/
theorem sweepEndpoint_fields {w B W : ℕ} (b : Fin B) (j : Fin W) (r : Role)
    (x y : OwnerArray w B W)
    (reads : readLanes (sweepAddress b j) y = runNode (readLanes (sweepAddress b j) x)) :
    let M := prime^w
    let size : M^64*M^64 = M^128 := (pow_add M 64 64).symm
    let cell := fun (h d : Fin (M^64)) =>
      stagedOwnerIndex b (finProdFinEquiv ((finProdFinEquiv (h,d)).cast size,j))
    let tape := bankTape r.bank (r.replica,r.port,r.cls)
    ∀ h d, y tape (cell h d) = x tape (cell d h) := by
  intro M size cell tape h d
  let digits (a b : Fin (M^64)) : Fin 128 → ZMod M := fun i => Fin.addCases (m := 64) (n := 64)
    (FlatCoordinateLayout.coordinates a) (FlatCoordinateLayout.coordinates b) i
  have addr (a b : Fin (M^64)) : FlatCoordinateLayout.index (digits a b) j =
      finProdFinEquiv ((finProdFinEquiv (a,b)).cast size,j) := by
    unfold FlatCoordinateLayout.index
    apply congrArg (fun k => finProdFinEquiv (k,j))
    apply Fin.ext
    simpa only [digits,Fin.val_cast,finProdFinEquiv_apply_val,FlatCoordinateLayout.rank_coordinates,
      Nat.mul_comm,Nat.add_comm] using ArbitraryWidthSliceTranspose.rank_append
        (FlatCoordinateLayout.coordinates a) (FlatCoordinateLayout.coordinates b)
  have flip : (fun i => digits h d ((helperFieldOrder none).symm (Sum.swap (helperFieldOrder none i)))) =
      digits d h := by
    funext i
    obtain ⟨k,rfl⟩ := (@finSumFinEquiv 64 64).surjective i
    cases k <;> simp only [helperFieldOrder,Equiv.trans_apply,Equiv.symm_trans_apply,
      Equiv.symm_symm,Equiv.symm_apply_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,
      Sum.map_inl,Sum.map_inr,Sum.swap_inl,Sum.swap_inr,digits] <;> simp only [
      finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.addCases_left,Fin.addCases_right]
    all_goals first | apply Fin.addCases_left | apply Fin.addCases_right
  have physical := sweepEndpoint_digits b j r x y reads (digits h d)
  dsimp only at physical
  rw [flip,addr,addr] at physical
  exact physical

end IntegerMultBounds.MathlibTM2.M6.BitNode
