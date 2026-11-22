module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedCorrectionRun
public import IntegerMultBounds.MathlibTM2.M6.BitSweepAllocatedReturn
public import IntegerMultBounds.MathlibTM2.M6.BitSweepEndpoint

/-! Read the borrowed bank through the role charts used by the scheduled node. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover FlatCoordinateLayout AffineFieldCoordinates
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def borrowedSpectator {w B K : ℕ} (b : Fin B) (g : LabelPadding.Label 64 w) (t : Fin K) :
    Fin (B*prime^(64*(w*64))*K) :=
  labelSpectator g (borrowedWindowCell b t)

theorem borrowedOwnerVolume (w B K : ℕ) :
    (prime^w)^16*(1*((prime^w)^112*(B*prime^(64*(w*64))*K))) =
    (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K) := by simp [Nat.mul_assoc]

private theorem activeWindow_at_label {w B K : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (x : Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) :
    borrowedActiveWindow b t g x s =
      x ((activeWindowAddress (0 : Fin 1) s (borrowedSpectator b g t)).cast (borrowedOwnerVolume w B K)) := by
  apply congrArg x
  apply Fin.ext
  simp [activeWindowAddress,chartAddress,
    -copyAddress_index,FlatCoordinateLayout.index,borrowedSpectator,labelSpectator,borrowedWindowCell,
    finProdFinEquiv]
  ring

private theorem inactiveWindow_at_label {w B K : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (digits : Fin 128 → ZMod (prime^w)) :
    let suffix := borrowedSpectator b g t
    helperFieldCell digits (0 : Fin 1) suffix =
      (stagedOwnerIndex (0 : Fin 1) (index digits suffix)).val := by
  intro suffix
  rw [stagedOwnerIndex_index]
  simp [helperFieldCell,helperLabelCell,finProdFinEquiv]
  ring

private theorem borrowedRoleCell_address {w B K : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (r : Role) (z : Axis ⊕ Axis → ℚ) :
    borrowedRoleCell b t g r (addressMod (prime^w) z) =
      (sweepAddress (w := w) (0 : Fin 1) (borrowedSpectator b g t) (r.replica,r.port,r.cls) z).val := by
  let digits := helperSlotField (port r.port.val) none w (windowState w z)
  apply Eq.trans _ (inactiveWindow_at_label b t g digits)
  simp [borrowedRoleCell,borrowedSpectator,labelSpectator,borrowedWindowCell,
    helperFieldCell,helperLabelCell,finProdFinEquiv,digits,windowState]
  ring

private theorem ext_at_cast {N V : ℕ} (h : N = V) (word : Fin V → ZMod 2)
    (a : ℕ) (j : Fin N) (atCell : a = j.val) : ext word a = word (j.cast h) := by
  subst a
  exact ext_apply word (j.cast h)

private theorem borrowedRoleRead_apply {w B K V : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin V → ZMod 2) (r : Role) (z : Axis ⊕ Axis → ℚ) :
    borrowedRoleRead b t g x r z = M8.RevMachine.ext (x (bankTape r.bank (r.replica,r.port,r.cls)))
      (borrowedRoleCell b t g r (addressMod (prime^w) z)) := by
  exact @Function.comp_apply _ _ _
    (fun v => ext (x (bankTape r.bank (r.replica,r.port,r.cls))) (borrowedRoleCell b t g r v))
    (addressMod (prime^w)) z

private theorem borrowedRoleRead_at_label {w B K V : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (h : (prime^w)^16*(1*((prime^w)^112*(B*prime^(64*(w*64))*K))) = V)
    (x : Fin 142081 → Fin V → ZMod 2)
    (r : Role) (z : Axis ⊕ Axis → ℚ) :
    borrowedRoleRead b t g x r z = x (bankTape r.bank (r.replica,r.port,r.cls))
      ((sweepAddress (w := w) (0 : Fin 1) (borrowedSpectator b g t) (r.replica,r.port,r.cls) z).cast
        h) := by
  rw [borrowedRoleRead_apply]
  exact ext_at_cast h (x (bankTape r.bank (r.replica,r.port,r.cls)))
    (borrowedRoleCell b t g r (addressMod (prime^w) z))
    (sweepAddress (w := w) (0 : Fin 1) (borrowedSpectator b g t) (r.replica,r.port,r.cls) z)
    (borrowedRoleCell_address b t g r z)

/-- All labels are consecutive spectator records in the ordinary sweep chart.
The same chart conversion therefore serves every label of a borrowed run. -/
theorem borrowedStageRead_eq_sweepRoles {w B K : ℕ} (n : Fin 9) (b : Fin B) (t : Fin K)
    (g : LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2) :
    borrowedStageRead n b t g x = sweepRoles n (0 : Fin 1) (borrowedSpectator b g t)
      (fun i j => x i (j.cast (borrowedOwnerVolume w B K))) := by
  funext r z
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  · simpa only [borrowedStageRead,sweepRoles,active,ite_true,activeRoleRead,along_apply,Function.comp_apply,
      readLanes,readRoles,activeSweepAddress] using
      activeWindow_at_label b t g (x (bankTape r.bank (r.replica,r.port,r.cls)))
        (windowState w ((bar ((port r.port.val).stageRoute n).transpose).mulVec z))
  · simpa only [borrowedStageRead,sweepRoles,active,ite_false,readLanes,readRoles] using
      borrowedRoleRead_at_label b t g (borrowedOwnerVolume w B K) x r z

theorem borrowedSpectator_covers {w B K : ℕ} (j : Fin (B*prime^(64*(w*64))*K)) :
    ∃ b g t, borrowedSpectator (w := w) b g t = j := by
  obtain ⟨⟨row,t⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨b,grow⟩,rfl⟩ := finProdFinEquiv.surjective row
  have count : prime^(64*(w*64)) = (prime^w)^(64*64) := by rw [← pow_mul]; congr 1; omega
  obtain ⟨g,hg⟩ := (address_bijective w).surjective (grow.cast count)
  refine ⟨b,g,t,Fin.ext ?_⟩
  simp [borrowedSpectator,labelSpectator,borrowedWindowCell,finProdFinEquiv,hg]
  ring

noncomputable def borrowedNodeArray {w B K : ℕ} (n : Fin 9) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i))
    (x : Fin 142081 → Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2) :
    OwnerArray w 1 (B*prime^(64*(w*64))*K) :=
  SweepFile.nodeArray parent units n (fun i j => x i (j.cast (borrowedOwnerVolume w B K)))

/-- Returning the corrected owners to node order realizes the scheduled stage
at every parent address, including independently occupied label records. -/
theorem borrowedStage_nodeRead {w B K : ℕ} (n : Fin 9) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i))
    (x y : Fin 142081 → Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2)
    (stage : ∀ b t g, borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g x)) :
    let W := B*prime^(64*(w*64))*K
    ∀ j : Fin W, let addr := fun z => nodeWindowEquiv w 1 W parent units (0,windowState w z,j)
      readRoles addr (borrowedNodeArray n parent units y) =
        (Piece.stage n).run (readRoles addr (borrowedNodeArray n parent units x)) := by
  intro W j addr
  obtain ⟨b,g,t,eqn⟩ := borrowedSpectator_covers (w := w) (B := B) (K := K) j
  have result := stage b t g
  rw [borrowedStageRead_eq_sweepRoles,borrowedStageRead_eq_sweepRoles,eqn] at result
  simpa only [addr,borrowedNodeArray,SweepFile.nodeArray_read] using result

/-- The physical handoff for one corrected sweep, in the common node layout. -/
def borrowedStageHandoff (w B K : ℕ) (parent : Fin 64 → ZMod (prime^w)) (units : ∀ i, IsUnit (parent i))
    (n : Fin 9) (a d : OwnerArray w 1 (B*prime^(64*(w*64))*K)) : Prop :=
  ∃ x y, a = borrowedNodeArray n parent units x ∧ d = borrowedNodeArray n parent units y ∧
    ∀ b t g, borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g x)

/-- A scheduled trace with borrowed sweeps interchanges the two parent fields
at every physical position and retains its inherited block, label and suffix. -/
theorem borrowedNodeHandoff_cell {w B K : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (r : Role) :
    let W := B*prime^(64*(w*64))*K
    let chart := nodeWindowEquiv w 1 W parent units
    let read := fun j => readRoles (fun z => chart (0,windowState w z,j))
    ∀ (idle : Fin 9 → OwnerArray w 1 W → OwnerArray w 1 W → Prop) (x y : OwnerArray w 1 W),
    (∀ n a d, idle n a d → ∀ j, read j d = (Piece.remainder n.val).run (read j a)) →
    nodeProgram.foldr (fun p cont a => ∃ d, nodePieceEffect w 1 W idle (borrowedStageHandoff w B K parent units) p a d ∧ cont d)
      (fun a => a = y) x →
    ∀ i, let (b,s,j) := chart.symm i
         let tape := bankTape r.bank (r.replica,r.port,r.cls)
         y tape i = x tape (chart (b,(s.2,s.1),j)) := by
  intro W chart read idle x y remainder trace
  apply nodeEndpoint_cell parent units r x y
  intro b j
  obtain rfl : b = 0 := Subsingleton.elim _ _
  apply nodePieceEffect_read _ _ (fun i a d h => remainder i a d h j) trace
  rintro n _ _ ⟨a,d,rfl,rfl,stage⟩
  exact borrowedStage_nodeRead n parent units a d stage j

end IntegerMultBounds.MathlibTM2.M6.BitNode
