module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedEndpoint

/-! Charge the independent borrowed-row node on its parent descriptor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.Networks.Certificates.PR589 IntegerMultBounds.Networks.Certificates.PR589.Nine
open BitHosting BitSchedule BitOccurrences Cover M8.RevMachine ActualAffineScaling
open IntegerMultBounds.Swap.Modular (reduce)
open M8.Machine.ArbitraryWidthOriginalTotalRun (cost)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- A remainder on another bank pair preserves the full source and target
equations of a sweep, including its independent label coordinates. -/
theorem BorrowedPorts.afterIdle {n : Fin 9} {w B K : ℕ} {x y z}
    (ports : BorrowedPorts n w B K x y) (i : Fin 9) (distinct : activePair n.val ≠ pairOf i)
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → z j = y j) : BorrowedPorts n w B K x z := by
  intro run t g cell owner j src dst read input
  have same (a : Fin 661) (data : a.val < 222) : z (owner a) = y (owner a) := by
    apply off
    intro k eqn
    have roles : BitNode.owner n run.1 run.2 a = idleRole i k :=
      (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eqn))
    have pair := (idleRole_coverage i _).mp ⟨k,roles.symm⟩
    simp only [BitNode.owner,data,ite_true] at pair
    exact distinct ((side_pair n run.1 run.2 _ (by unfold regSide; split <;> omega) _).symm.trans pair)
  have kept (a : Fin 661) (data : a.val < 222) : read z a = read y a := by
    funext s
    simpa only [read,phaseRead,Copy.extendStored,dite_eq_left a.isLt] using
      congrFun (same a data) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)
  rw [kept src (by dsimp [src]; omega),kept dst (by dsimp [dst]; omega)]
  exact ports run t g cell

/-- Follow an active pair across a sequence of remainders on other pairs. -/
theorem BorrowedPorts.afterIdles {n : Fin 9} {w B K : ℕ} {x y}
    (ports : BorrowedPorts n w B K x y) (idle : Fin 9 → OwnerStage _)
    (off : ∀ i a j, (∀ k, j ≠ idleTape i k) → (idle i).transform a j = a j)
    (windows : List (Fin 9)) (apart : ∀ i ∈ windows, activePair n.val ≠ pairOf i) :
    BorrowedPorts n w B K x (windows.foldl (fun a i => (idle i).transform a) y) := by
  induction windows generalizing y with
  | nil => exact ports
  | cons i rest ih =>
    exact ih (ports.afterIdle i (apart i List.mem_cons_self) (off i y))
      (fun k hk => apart k (List.mem_cons_of_mem _ hk))

noncomputable def alignedCell {w B K : ℕ} (exterior : Fin 112 → ZMod (prime^w))
    (b : Fin B) (t : Fin K) :
    LabelEntry.Cell (copyLabelLayout w ((prime^w)^112*B) K) ((prime^w)^112*B) :=
  ⟨⟨0,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _⟩,⟨0,by simp [copyLabelLayout]⟩,
    finProdFinEquiv (FlatCoordinateLayout.rank exterior,b),⟨0,by simp [copyLabelLayout,modulus]⟩,
    ⟨0,by simp [copyLabelLayout]⟩,⟨0,by simp [copyLabelLayout,modulus]⟩,t⟩

noncomputable def alignedOffset {w B K : ℕ} (active : Fin 16 → ZMod (prime^w))
    (exterior : Fin 112 → ZMod (prime^w)) (b : Fin B) (t : Fin K)
    (g : LabelPadding.Label 64 w) :
    Fin ((prime^w)^16*(((prime^w)^112*B)*prime^(64*(w*64))*K)) :=
  FlatCoordinateLayout.index active (labelSpectator g (alignedCell exterior b t))

/-- Read the source and XOR target in their port frames at the same
physical addresses as the remainder interval equations. -/
theorem BorrowedPorts.aligned {n w B K x y}
    (ports : BorrowedPorts n w ((prime^w)^112*B) K x y)
    (run : Fin 32 × Fin 5) (port : Fin 111) (exterior : Fin 112 → ZMod (prime^w))
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) :
    let read := fun (data : Fin 142081 → _ → ZMod 2) (i : Fin 661) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) =>
      data (ownerTape n run.1 run.2 i) (alignedOffset (AffineFieldCoordinates.embed s) exterior b t g)
    let src : Fin 661 := ⟨port.val,by omega⟩
    let dst : Fin 661 := ⟨111+port.val,by omega⟩
    let input := fun i : Fin 661 => (selectedFrame w (Frames.initialRefs i.val)).symm (read x i)
    read y src = selectedFrame w (Frames.finalRefs src.val) (input src) ∧
    read y dst = selectedFrame w (Frames.finalRefs dst.val) (input dst + input src) := by
  intro read src dst input
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n run.1 run.2,ownerTape_injective n run.1 run.2⟩
  let j := labelSpectator g (alignedCell exterior b t)
  have eqn (data) (i : Fin 661) : phaseRead owner data j i.val = read data i := by
    funext s
    simp only [phaseRead,Copy.extendStored,dite_eq_left i.isLt]
    rfl
  have action := ports run port g (alignedCell exterior b t)
  let initial := fun i : Fin 661 => (selectedFrame w (Frames.initialRefs i.val)).symm (phaseRead owner x j i.val)
  change phaseRead owner y j src.val = selectedFrame w (Frames.finalRefs src.val) (initial src) ∧
    phaseRead owner y j dst.val = selectedFrame w (Frames.finalRefs dst.val) (initial dst + initial src) at action
  simpa only [initial,input,eqn] using action

/-- The helper parity action uses the same physical offset as the ports. -/
theorem BorrowedHelpers.aligned {n w B K x y}
    (helpers : BorrowedHelpers n w ((prime^w)^112*B) K x y)
    (ρ : Role) (inactive : ρ.bank.val / 2 ≠ activePair n.val)
    (exterior : Fin 112 → ZMod (prime^w)) (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let uses := stageRuns.filter fun k => decide (∃ h : Fin 439, hostRole n k.1 k.2 h = ρ)
    let pos := fun a => alignedOffset (AffineFieldCoordinates.embed a) exterior b t g
    y tape (pos (if uses.length % 2 = 1 then s.swap else s)) = x tape (pos s) :=
  helpers ρ inactive g (alignedCell exterior b t) s

/-- Fold the exterior digits into the sweep block, so the phase and the idle
read the same flat offset for every independent matrix label. -/
theorem alignedSweep_read {w B K : ℕ} (active : Fin 16 → ZMod (prime^w))
    (exterior : Fin 112 → ZMod (prime^w)) (b : Fin B) (t : Fin K)
    (g : LabelPadding.Label 64 w) (x : Fin (volume prime (idleLayout w B K)) → ZMod 2) :
    chartRead x g (idleDigitCell rfl (fun j => Fin.addCases (motive := fun _ => ZMod (prime^w)) active exterior j) b t) =
      ext x (alignedOffset active exterior b t g) := by
  unfold alignedOffset
  apply congrArg (ext x)
  simp only [idleDigitCell,RecursiveInterchangeLayout.index,idleLayout,Fin.val_cast,
    FlatCoordinateLayout.index_val,labelSpectator,alignedCell,finProdFinEquiv,Equiv.coe_fn_mk,
    ArbitraryWidthSliceTranspose.rank_append active exterior,pow_zero,Fin.val_zero,mul_one,add_zero]
  ring

private theorem idle_read_split {n w B K : ℕ} (width : n = 128) (digits : Fin n → ZMod (prime^w))
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) (x : Fin (volume prime (idleLayout w B K)) → ZMod 2) :
    chartRead x g (idleDigitCell width digits b t) = ext x (alignedOffset
      (fun j => digits ((j.castAdd 112).cast width.symm)) (fun j => digits ((j.natAdd 16).cast width.symm)) b t g) := by
  subst n
  have split : (fun j : Fin 128 => Fin.addCases (motive := fun _ => ZMod (prime^w))
      (fun j : Fin 16 => digits (j.castAdd 112)) (fun j : Fin 112 => digits (j.natAdd 16)) j) = digits := by
    funext j
    induction j using Fin.addCases (m := 16) (n := 112) <;> simp
  simpa only [split,Fin.cast_eq_self] using alignedSweep_read (fun j : Fin 16 => digits (j.castAdd 112))
    (fun j : Fin 112 => digits (j.natAdd 16)) b t g x

theorem IdleTransport.alignedDigits {i : Fin 9} {k : (Fin 32 × Fin 5) × Fin 222} {w B K : ℕ}
    {before after} (run : IdleTransport i k w B K before after) :
    let e := idleInterval i k.2
    ∀ (a b : Fin e.1 → ZMod (prime^w)) (h d : Fin (e.2-e.1) → ZMod (prime^w))
      (u v : Fin (64-e.2) → ZMod (prime^w)) (block : Fin B) (t : Fin K) (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))),
      let digits := fun (h d : Fin (e.2-e.1) → ZMod (prime^w)) =>
        Fin.append (Fin.append (Fin.append a h) u) (Fin.append (Fin.append b d) v)
      let width : (e.1+(e.2-e.1)+(64-e.2))+(e.1+(e.2-e.1)+(64-e.2)) = 128 := by
        obtain ⟨hl,hr,_⟩ := remainder_counts _ (idleInterval_mem i k.2)
        change e.1 ≤ e.2 at hl
        change e.2 ≤ 63 at hr
        omega
      let pos := fun h d => alignedOffset (fun j => digits h d ((j.castAdd 112).cast width.symm))
        (fun j => digits h d ((j.natAdd 16).cast width.symm)) block t g
      ext after (pos d h) = ext before (pos h d) := by
  intro e a b h d u v block t g digits width pos
  exact (idle_read_split width (digits d h) block t g after).symm.trans
    ((run.digits a b h d u v block t g).trans (idle_read_split width (digits h d) block t g before))

/-- Cost of the borrowed-row sweeps and physical idle schedule on one aligned parent descriptor. -/
theorem borrowedNode_parentCost [M8.Machine.Net] (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℝ, ∀ (parent : Descriptor) (w B rows : ℕ), parent.Positive → 0 < w → 0 < B →
      parent.width = 64*w → parent.rows = 142080*rows → parent.beforeH = B*prime^(64*(w*64)) →
      let K := parent.beforeRows*rows*parent.between*parent.afterD
      let W := B*prime^(64*(w*64))*K
      let blocks := (prime^w)^112*B
      let phaseW := blocks*prime^(64*(w*64))*K
      let V := (prime^w)^16*phaseW
      let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
      ∃ (size : volume prime v = V)
        (inv idle : Fin 9 → OwnerStage V) (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V),
        BankActions bridge exchange ∧
        (∀ (price : ℕ → ℕ) (rate : ℕ → ℝ),
          (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
            phaseChildCost w phaseW p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w phaseW) (fun j => FlatCoordinateSchedule.bits
            (RecursiveDimensionBank.values (copyChild w phaseW) j)) ≤ price 7 →
          (∀ (i : Fin 9) (c : Fin 222), let e := idleInterval i c
            let child := phaseIntervalChild e.1 e.2 w W 64
            cost child (fun j => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child j)) ≤ price (e.2-e.1)) →
          (∀ j ∈ nodeChildren5, (price j : ℝ) ≤ V*rate j) →
          ((compiledNode inv idle bridge exchange).cost : ℝ) ≤
            volume prime parent*(D*(w : ℝ)^M8.Machine.BudgetBound.tau + (nodeChildren5.map rate).sum/142080)) ∧
        (∀ n x, stageRuns.foldr (fun k cont a => ∃ b, BorrowedStep n w blocks K k a b ∧ cont b)
          (fun a => a = (inv n).transform x) x ∧ BorrowedPorts n w blocks K x ((inv n).transform x) ∧
          BorrowedHelpers n w blocks K x ((inv n).transform x)) ∧
        (∀ n x (windows : List (Fin 9)), (∀ i ∈ windows, activePair n.val ≠ pairOf i) →
          BorrowedPorts n w blocks K x (windows.foldl (fun a i => (idle i).transform a) ((inv n).transform x))) ∧
        ∀ i x, (∀ k, IdleTransport i k w B K (fun t => x (idleTape i k) (Fin.cast size t))
          (fun t => (idle i).transform x (idleTape i k) (Fin.cast size t))) ∧
          ∀ j, (∀ k, j ≠ idleTape i k) → (idle i).transform x j = x j := by
  have assemble := compiledNode_cost_of_sweeps engine (2*(63*9+252*527)+1322*252) (fun w B K inv =>
    ∀ n x, stageRuns.foldr (fun k cont a => ∃ b, BorrowedStep n w B K k a b ∧ cont b)
      (fun a => a = (inv n).transform x) x ∧ BorrowedPorts n w B K x ((inv n).transform x) ∧
        BorrowedHelpers n w B K x ((inv n).transform x))
  obtain ⟨C,build⟩ := borrowedPieces_nodeCost engine
  obtain ⟨D,node⟩ := assemble ⟨C,fun w B K hw hb hk => by
    obtain ⟨inv,bill,trace⟩ := build w B K hw hb hk
    exact ⟨inv,bill,fun n x => ⟨trace n x,borrowedSweep_ports (trace n x),borrowedSweep_helpers (trace n x)⟩⟩⟩
  refine ⟨D,?_⟩
  intro parent w B rows positive hw hb width split label K W blocks phaseW V v
  obtain ⟨size,inv,idle,bridge,exchange,bank,bill,sweep,rest⟩ := node parent w B rows positive hw hb width split label
  exact ⟨size,inv,idle,bridge,exchange,bank,bill,sweep,fun n x windows apart =>
    (sweep n x).2.1.afterIdles idle (fun i a => (rest i a).2) windows apart,rest⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
