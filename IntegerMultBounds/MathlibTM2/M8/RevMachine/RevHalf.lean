module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode

/-!
# The node half of a reversed network

The node's blocks (`RevNode.blocks`) realize the node half of the family (`half`): from a frame
of `n ≥ m` atoms whose data are bits on `io`, the split reaches the node's bank (`NodeS`), every
piece of the schedule keeps it, a block call enters a child frame on the call's role stream and
recovers its output, and the merge returns the bits to `io`.

The pieces' coefficients are those of the network, within the coefficient bound and legal at the
machine prime (`RevRuns`), so every atom operation of every segment runs on the role bank
(`fits`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs ranks)
open CommonBank (bank K)
open Blocks (seqB seq_runs runs_mono Leading)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveRoleSerialization (roles)
open NodeBank (tapes io wireSlot wires tempSlot)
open NodePark (childRoles)
open NodeCall (nodeC)
open NodeSplit (midView roleView NodeInv zeroBit)
open SegmentBits (Bits)
open Family (leafC NodeFree Frame)
open Schedule (Seg Call schedule)
open AtomRolePlan (Fits)
open RevNode (Good depth)

variable (N : RevNetwork)

/-! ### The schedule -/

/-- The schedule of the network. -/
abbrev pcs : List (Graph.Piece (Seg (N.World ⊕ N.Temp) N.width) (Call (N.World ⊕ N.Temp))) := schedule N.control

/-- The ranks of its calls. -/
abbrev Rk : List ℕ := ranks Prod.snd (pcs N)

theorem mem_before {p : FieldProgram N.width} {op} (h : op ∈ Schedule.before p) : op ∈ p :=
  (List.takeWhile_sublist _).subset h

theorem mem_after {p : FieldProgram N.width} {op} (h : op ∈ Schedule.after p) : op ∈ p :=
  (List.dropWhile_suffix _).subset ((List.dropWhile_suffix _).subset h)

/-- An edge segment of the schedule is part of an edge program of the control. -/
theorem edge_mem {i : Graph.Site (pcs N)} {w : N.World ⊕ N.Temp} {ops : FieldProgram N.width}
    (hi : (pcs N)[i] = .seg (.edge w ops)) : ∃ p, Step.edge w p ∈ N.control ∧ ∀ op ∈ ops, op ∈ p := by
  have hm : Graph.Piece.seg (Seg.edge w ops) ∈ pcs N := hi ▸ List.getElem_mem _
  obtain ⟨step, hs, hp⟩ := List.mem_flatMap.mp hm
  cases step with
  | edge j p =>
    simp only [Schedule.stepPieces] at hp
    split_ifs at hp
    · simp only [List.mem_cons, Graph.Piece.seg.injEq, Seg.edge.injEq, reduceCtorEq, List.mem_nil_iff,
        or_false] at hp
      rcases hp with ⟨rfl, rfl⟩ | h | ⟨rfl, rfl⟩
      · exact ⟨p, hs, fun op h => mem_before N h⟩
      · exact h.elim
      · exact ⟨p, hs, fun op h => mem_after N h⟩
    · simp only [List.mem_singleton, Graph.Piece.seg.injEq, Seg.edge.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨ops, hs, fun _ h => h⟩
  | gate g => simp [Schedule.stepPieces] at hp
  | reset w => simp [Schedule.stepPieces] at hp

/-! ### The atom operations fit -/

variable {N}

theorem ratMod_ne_zero {c : ℚ} (h : IsUnit (Swap.Modular.ratMod (prime ^ 1) c)) : c ≠ 0 := by
  rintro rfl
  rw [Swap.Modular.ratMod_zero] at h
  have : Nontrivial (ZMod (prime ^ 1)) := ZMod.nontrivial_iff.mpr (by
    rw [pow_one]; exact Shared50ModularControl.prime_prime.one_lt.ne')
  exact not_isUnit_zero h

theorem den_lt {c : ℚ} (h : c.den ≤ coefficientBound) : c.den < prime :=
  lt_of_le_of_lt h Shared50ModularControl.coefficientBound_lt_prime

theorem scale_occurs {c : ℚ} (h0 : c ≠ 0) (hc : c.num.natAbs ≤ coefficientBound ∧ c.den ≤ coefficientBound) :
    Shared50AffineCoefficients.ScaleOccurs c := Or.inr ⟨h0, hc.1, hc.2⟩

theorem one_le_bound : 1 ≤ coefficientBound := Nat.one_le_two_pow

/-- **Every atom operation of a bounded legal operation fits.** -/
theorem op_fits {op : AffineFieldProgram.Op (Fin N.width) ℚ} (hc : Machine.Coordinates.CoeffBounded op)
    (hl : AffineFieldProgram.Legal (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime ^ 1)) op)) :
    ∀ o ∈ AtomOps.atomExpand op, Fits N.width o := by
  intro o ho
  cases op with
  | affineH a =>
    cases a with
    | scale i c =>
      simp only [AtomOps.atomExpand, List.mem_singleton] at ho; subst ho
      exact scale_occurs (ratMod_ne_zero hl) (hc c (by simp [M8.Exchange.opCoeffs]))
    | shift i j c =>
      simp only [AtomOps.atomExpand, List.mem_singleton] at ho; subst ho
      have hji : j < i := hl
      exact ⟨Fin.lt_def.mpr (by simp only [AffineFieldCoordinates.hIndex, Fin.val_castAdd]; exact hji),
        den_lt (hc c (by simp [M8.Exchange.opCoeffs])).2⟩
  | affineD a =>
    cases a with
    | scale i c =>
      simp only [AtomOps.atomExpand, List.mem_singleton] at ho; subst ho
      exact scale_occurs (ratMod_ne_zero hl) (hc c (by simp [M8.Exchange.opCoeffs]))
    | shift i j c =>
      simp only [AtomOps.atomExpand, List.mem_singleton] at ho; subst ho
      have hji : j < i := hl
      exact ⟨Fin.lt_def.mpr (by simp only [AffineFieldCoordinates.dIndex, Fin.val_natAdd]; omega),
        den_lt (hc c (by simp [M8.Exchange.opCoeffs])).2⟩
  | addToD i j =>
    simp only [AtomOps.atomExpand, List.mem_singleton] at ho; subst ho
    exact ⟨by simp [AffineFieldCoordinates.hIndex], by simp [AffineFieldCoordinates.dIndex],
      by simp; exact Shared50ModularControl.prime_prime.one_lt⟩
  | subFromD i j =>
    simp only [AtomOps.atomExpand, List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl
    · exact scale_occurs (by norm_num) ⟨by simpa using one_le_bound, by simpa using one_le_bound⟩
    · exact ⟨by simp [AffineFieldCoordinates.hIndex], by simp [AffineFieldCoordinates.dIndex],
        by simp; exact Shared50ModularControl.prime_prime.one_lt⟩
  | interchange i j => simp [AtomOps.atomExpand] at ho

/-- **Every atom operation of every segment of the schedule fits.** -/
theorem fits (hR : RevRuns N) {i : Graph.Site (pcs N)} {w : N.World ⊕ N.Temp} {ops : FieldProgram N.width}
    (hi : (pcs N)[i] = .seg (.edge w ops)) : ∀ o ∈ AtomSegment.atoms ops, Fits N.width o := by
  obtain ⟨p, hp, hsub⟩ := edge_mem N hi
  intro o ho
  obtain ⟨op, hop, ho⟩ := List.mem_flatMap.mp ho
  refine op_fits (hR.coeff_bound w p hp op (hsub op hop)) ?_ o ho
  have := N.legal_mod 1 w p hp (AffineFieldProgram.mapOp (Swap.Modular.ratMod (N.prime ^ 1)) op)
    (List.mem_map.mpr ⟨op, hsub op hop, rfl⟩)
  rw [hR.prime_eq] at this
  exact this

/-! ### Frames and the node's bank -/

variable {k : ℕ} {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

variable (N) in
/-- **The frames the family serves**: atom width `b₀`, rows that split over the contract roles at
every depth below, and blank suffixes on the payload, descriptor and PC stacks. -/
structure Ok (b₀ : ℕ) (σ : Frame (pcs N) capacity) : Prop where
  b : σ.b = b₀
  rows : N.roleCount ^ depth N.width (Rk N) σ.n ∣ σ.v.rows
  pay : ∀ z, σ.p ≤ z → σ.f z = blank
  desc : RecursiveStackAllocation.Available 0 σ.st
  pc : RecursiveStackAllocation.Available 1 σ.st

variable (N) in
/-- **The node's bank**: data on the role view with a blank `io` and bits on every wire. -/
def NodeS (σ : Frame (pcs N) capacity) (_i : ℕ) (y : Tapes (CommonBank.count (tapes N)) prime) : Prop :=
  ∃ data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v), NodeInv N data ∧
    y = bank (roles data) (hdr (roleView N σ.b σ.n σ.v)) σ.f σ.p
      (RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node))
      σ.scalar (nodeC N σ.b (σ.n / N.width)) σ.st

theorem one_le_depth {m : ℕ} {Rk' : List ℕ} {n : ℕ} (hm : 0 < m) (hn : m ≤ n) : 1 ≤ depth m Rk' n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  unfold depth
  simp only [RevNode.depthF, hn, ↓reduceIte]
  omega

theorem rows_dvd {b₀ : ℕ} {σ : Frame (pcs N) capacity} (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) :
    N.roleCount ∣ σ.v.rows :=
  (dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (one_le_depth (by have := N.two_le_width; omega) hm))).trans hok.rows

theorem bits_xor {n : ℕ} {a b : Fin n → Fin 4} (ha : Bits a) (hb : Bits b) :
    Bits (fun i => PointwiseBinary.xorSymbol (a i) (b i)) := by
  intro i
  obtain ⟨x, hx⟩ := ha i
  obtain ⟨y, hy⟩ := hb i
  show ∃ z, PointwiseBinary.xorSymbol (a i) (b i) = _
  rw [hx, hy]
  fin_cases x <;> fin_cases y
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- Role operations writing wires keep the node's data. -/
theorem ops_inv {v : Descriptor} (l : List (M8.Machine.RoleOps.Op (tapes N)))
    (hl : ∀ o ∈ l, match o with
      | .xor g => g.src ≠ io N ∧ g.dst ≠ io N
      | .fill g s => g.dst ≠ io N ∧ ∃ z, s = SparseRoleCircuit.encode z)
    (data : RecursiveMixedSchedule.Data (tapes N) v) (h : NodeInv N data) :
    NodeInv N (M8.Machine.RoleOps.run l data) := by
  induction l generalizing data with
  | nil => exact h
  | cons o l ih =>
    change NodeInv N (M8.Machine.RoleOps.run l (M8.Machine.RoleOps.transform o data))
    refine ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) _ ?_
    have ho := hl o List.mem_cons_self
    cases o with
    | xor g =>
      refine ⟨by simp [M8.Machine.RoleOps.transform, Function.update_of_ne (Ne.symm ho.2), h.1], fun i hi => ?_⟩
      by_cases hd : i = g.dst
      · subst hd
        simp only [M8.Machine.RoleOps.transform, Function.update_self]
        exact bits_xor (h.2 _ ho.1) (h.2 _ hi)
      · simp only [M8.Machine.RoleOps.transform, Function.update_of_ne hd]
        exact h.2 i hi
    | fill g s =>
      refine ⟨by simp [M8.Machine.RoleOps.transform, Function.update_of_ne (Ne.symm ho.1), h.1], fun i hi => ?_⟩
      by_cases hd : i = g.dst
      · subst hd
        simp only [M8.Machine.RoleOps.transform, Function.update_self]
        obtain ⟨z, rfl⟩ := ho.2
        exact fun _ => ⟨z, rfl⟩
      · simp only [M8.Machine.RoleOps.transform, Function.update_of_ne hd]
        exact h.2 i hi

/-! ### The pieces -/

open Classical in
variable (N) in
/-- The cost of a nonrecursive piece. -/
def segCost (σ : Frame (pcs N) capacity) : Seg (N.World ⊕ N.Temp) N.width → ℕ
  | .edge w ops =>
    if h : ∀ o ∈ AtomSegment.atoms ops, Fits N.width o then
      AtomRoleSegment.chainConst (wireSlot N w) (AtomRoleSegment.sops ops h) * (σ.n / N.width) *
        volume prime (roleView N σ.b σ.n σ.v)
    else 0
  | .gate g => M8.Machine.RoleOpsClean.coefficient (RevNode.gateOp N g) * volume prime (roleView N σ.b σ.n σ.v)
  | .reset w => M8.Machine.RoleOpsClean.coefficient
      [.fill ⟨io N, wireSlot N w, (NodeBank.wireSlot_ne_io N w).symm⟩ zeroBit] * volume prime (roleView N σ.b σ.n σ.v)

theorem gateOp_ok (g : Circuit.Gate (N.World ⊕ N.Temp) (ZMod 2)) :
    ∀ o ∈ RevNode.gateOp N g, match o with
      | .xor g => g.src ≠ io N ∧ g.dst ≠ io N
      | .fill g s => g.dst ≠ io N ∧ ∃ z, s = SparseRoleCircuit.encode z := by
  unfold RevNode.gateOp
  split_ifs
  · intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨NodeBank.wireSlot_ne_io N _, NodeBank.wireSlot_ne_io N _⟩
  · intro o ho; simp at ho

/-- **A nonrecursive piece** keeps the node's bank. -/
theorem half_seg (hR : RevRuns N) {b₀ : ℕ} (σ : Frame (pcs N) capacity) (y : Tapes (CommonBank.count (tapes N)) prime)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N)) (s : Seg (N.World ⊕ N.Temp) N.width)
    (hi : (pcs N)[i] = .seg s) (hy : NodeS N σ i.val y) :
    ∃ y', NodeS N σ (i.val+1) y' ∧ Runs (RevNode.segB N s) y y' (segCost N σ s) := by
  obtain ⟨data, hinv, rfl⟩ := hy
  have hd := rows_dvd hok hm
  have hp := NodeSplit.roleView_positive N (b := σ.b) (n := σ.n) σ.hpos hd
  have hV := Routines.hdr_headers (roleView N σ.b σ.n σ.v)
  cases s with
  | edge w ops =>
    have hfits := fits hR hi
    have hf : 0 < σ.n / N.width := Nat.div_pos hm (by have := N.two_le_width; omega)
    have hw : (roleView N σ.b σ.n σ.v).width = (N.width * (σ.n / N.width)) * σ.b := rfl
    set l := AtomRoleSegment.sops ops hfits
    have hh := AtomRoleSegment.chain_hoare σ.hb (RevNode.segT N w l) hf (wireSlot N w) _ hw hp _ hV l
      (RevNode.segT_ge N w l) data
    have hc := RevNode.nodeC_segCounters N σ.b (σ.n / N.width)
    have hr := NodeSegment.seg_runs (fs := σ.f) (p := σ.p)
      (node := RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node))
      (scalar := σ.scalar) (st := σ.st) (RevNode.segT_le N w l) _ hc hh
    set data' := AtomRoleSegment.chainData hf (wireSlot N w) _ hw l data
    refine ⟨_, ⟨data', ⟨?_, fun j hj => ?_⟩, rfl⟩, ?_⟩
    · exact (AtomRoleSegment.chain_other hf _ _ hw (io N) (NodeBank.wireSlot_ne_io N w).symm l data).trans hinv.1
    · by_cases hjw : j = wireSlot N w
      · subst hjw
        exact SegmentBits.chain_bits hf _ _ hw l data (hinv.2 _ (NodeBank.wireSlot_ne_io N w))
      · rw [show data' j = data j from AtomRoleSegment.chain_other hf _ _ hw j hjw l data]
        exact hinv.2 j hj
    · have hsc : segCost N σ (.edge w ops) = AtomRoleSegment.chainConst (wireSlot N w) l * (σ.n / N.width) *
          volume prime (roleView N σ.b σ.n σ.v) := by
        simp only [segCost]; split_ifs; rfl
      have hsb : RevNode.segB N (.edge w ops) = NodeSegment.place (AtomRoleSegment.chain (RevNode.segT N w l)
          (wireSlot N w) l (RevNode.segT_ge N w l)).2 (RevNode.segT_le N w l) := by
        simp only [RevNode.segB]; split_ifs; rfl
      rw [hsc, hsb]
      exact runs_mono hr (AtomRoleSegment.chainCost_le σ.hb hf _ _ hw hp l)
  | gate g =>
    refine ⟨_, ⟨_, ops_inv _ (gateOp_ok g) data hinv, rfl⟩,
      NodeBank.ops_runs (RevNode.gateOp N g) hV hp data _ _ _ _ _ _⟩
  | reset w =>
    refine ⟨_, ⟨_, ops_inv _ ?_ data hinv, rfl⟩, NodeBank.ops_runs _ hV hp data _ _ _ _ _ _⟩
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨(NodeBank.wireSlot_ne_io N w), 0, rfl⟩

/-! ### Split and merge -/

/-- **The split** reaches the node's bank. -/
theorem half_split {b₀ : ℕ} (σ : Frame (pcs N) capacity) (rr : Tapes (tapes N) prime) (hok : Ok N b₀ σ)
    (hm : N.width ≤ σ.n) (hg : Good N σ.v rr) :
    ∃ y, NodeS N σ 0 y ∧ Runs (NodeSplit.splitB N) (σ.at rr (leafC σ.b N.width σ.n 0)) y
      (NodeSplit.splitCost (N := N) σ.v σ.b σ.n) := by
  obtain ⟨-, x, rfl⟩ := hg
  obtain ⟨data, hinv, h⟩ := NodeSplit.split_runs (fs := σ.f) (p := σ.p) (node := σ.node) (scalar := σ.scalar)
    (st := σ.st) σ.hpos σ.hb σ.hw hm (rows_dvd hok hm) _ (RevNode.encoded_bits x)
  exact ⟨_, ⟨data, hinv, rfl⟩, h⟩

/-- **The merge** returns bits to `io`. -/
theorem half_merge {b₀ : ℕ} (σ : Frame (pcs N) capacity) (y : Tapes (CommonBank.count (tapes N)) prime)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (hy : NodeS N σ (pcs N).length y) :
    ∃ rr, Good N σ.v rr ∧ Runs (NodeSplit.mergeB N) y (σ.at rr (leafC σ.b N.width σ.n 0))
      (NodeSplit.mergeCost (N := N) σ.v σ.b σ.n) := by
  obtain ⟨data, hinv, rfl⟩ := hy
  obtain ⟨x, hx, h⟩ := NodeSplit.merge_runs (fs := σ.f) (p := σ.p) (scalar := σ.scalar) (st := σ.st)
    σ.hpos σ.hb σ.hw (rows_dvd hok hm) data hinv σ.hfree
  obtain ⟨xb, rfl⟩ := RevNode.bits_encoded hx
  exact ⟨_, ⟨σ.hpos, xb, rfl⟩, h⟩

/-! ### Calls -/

variable (N) in
/-- The cost of a call of rank `r` on wire `w`. -/
def callCost (σ : Frame (pcs N) capacity) (c : Call (N.World ⊕ N.Temp)) : ℕ :=
  NodeCall.enterCost (N := N) c.1 (σ.n / N.width) c.2 k (volume prime (roleView N σ.b σ.n σ.v)) +
    NodeCall.recoverCost (N := N) c.1 (hdr (roleView N σ.b σ.n σ.v))
      (hdr (NodeCall.childView (N := N) σ.b (σ.n / N.width) c.2 (roleView N σ.b σ.n σ.v))) σ.b (σ.n / N.width)
      (volume prime (roleView N σ.b σ.n σ.v))

theorem dvd_child {W d D rows : ℕ} (hD : d + 1 ≤ D) (h : W ^ D ∣ rows) : W ^ d ∣ rows / W := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  · have h' : W ^ d * W ∣ rows := (pow_succ W d ▸ pow_dvd_pow W hD).trans h
    exact Nat.dvd_div_of_mul_dvd (by rwa [Nat.mul_comm] at h')

/-- The frame of a block call of rank `r` on wire `w` at site `i`. -/
def childFrame {b₀ : ℕ} (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ) (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    Frame (pcs N) capacity :=
  let E := RecursiveCallProtocol.entered (NodePark.parked N w) (wireSlot N w) (io N) (volume prime (roleView N σ.b σ.n σ.v))
    (bank (roles data) (hdr (roleView N σ.b σ.n σ.v)) σ.f σ.p
      (RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node))
      σ.scalar (nodeC N σ.b (σ.n / N.width)) σ.st)
  { v := NodeCall.childView (N := N) σ.b (σ.n / N.width) r (roleView N σ.b σ.n σ.v)
    n := r * (σ.n / N.width)
    b := σ.b
    hpos := Family.sub_positive (NodeSplit.roleView_positive N σ.hpos (rows_dvd hok hm))
    hb := σ.hb
    hw := rfl
    f := E.tape (RecursiveCallBank.controlSlot 2)
    p := E.head (RecursiveCallBank.controlSlot 2)
    node := RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node)
    scalar := σ.scalar
    st := RecursiveChildCallSetup.savedStacks (hdr (roleView N σ.b σ.n σ.v)) σ.st (Graph.returnCode (pcs N) capacity i)
    hfree := RecursiveRowsNode.saved_available _ _ (RecursiveRowsNode.saved_available _ _ σ.hfree)
    ret := .recover i
    g := σ.st.tape 1
    q := σ.st.head 1
    hcode := ⟨(RevNode.savedStacks_pc (hdr (roleView N σ.b σ.n σ.v)) σ.st _).1,
      (RevNode.savedStacks_pc (hdr (roleView N σ.b σ.n σ.v)) σ.st _).2, fun j _ => hok.pc _ (by omega)⟩ }

/-- The call's frame is served. -/
theorem childFrame_ok {b₀ : ℕ} (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (σ : Frame (pcs N) capacity)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ)
    (hi : (pcs N)[i] = .call (w, r)) (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    Ok N b₀ (childFrame σ hok hm i w r data) := by
  have hsaved := RecursiveStackAllocation.saved_stacks_available (hdr (roleView N σ.b σ.n σ.v)) σ.st
    (Graph.returnCode (pcs N) capacity i) hok.desc hok.pc
  have hdepth := RevNode.depth_child (fun r h => (hRk r h).2) hm (GraphContract.rank_mem Prod.snd (pcs N) i.val i.isLt (w, r) hi)
  exact
    { b := hok.b
      rows := dvd_child hdepth hok.rows
      pay := NodePark.entered_blank_suffix N (u := 1+(1+K)) w (volume prime (roleView N σ.b σ.n σ.v)) (roles data)
        (hdr (roleView N σ.b σ.n σ.v)) σ.f σ.p
        ((RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node)).append
          (σ.scalar.append (CommonBank.counters (nodeC N σ.b (σ.n / N.width))))) σ.st hok.pay
      desc := hsaved.1
      pc := hsaved.2 }

/-- **A block call**: a child frame on the call's role stream, and its recovery. -/
theorem half_call {b₀ : ℕ} (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (σ : Frame (pcs N) capacity)
    (y : Tapes (CommonBank.count (tapes N)) prime) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (c : Call (N.World ⊕ N.Temp)) (hi : (pcs N)[i] = .call c) (hy : NodeS N σ i.val y) :
    ∃ τ : Frame (pcs N) capacity, Ok N b₀ τ ∧ τ.n = c.2 * (σ.n / N.width) ∧
      (volume prime τ.v : ℝ) = volume prime σ.v / N.roleCount ∧ τ.ret = .recover i ∧ τ.b = σ.b ∧
      ∃ rr, Good N τ.v rr ∧ ∃ E R, E + R ≤ callCost N σ c ∧
        Runs ((RevNode.blocks N k).enter c (Graph.returnCode (pcs N) capacity i)) y (τ.at rr (Prepare.rest τ.b N.width)) E ∧
        ∀ rr', Good N τ.v rr' → ∃ y', NodeS N σ (i.val+1) y' ∧
          Runs ((RevNode.blocks N k).recover c) (τ.exitAt rr' N.width) y' R := by
  obtain ⟨data, hinv, rfl⟩ := hy
  obtain ⟨w, r⟩ := c
  have hrr := hRk r (GraphContract.rank_mem Prod.snd (pcs N) i.val i.isLt (w, r) hi)
  set f := σ.n / N.width
  set node₂ := RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node)
  set code := Graph.returnCode (pcs N) capacity i
  have hd := rows_dvd hok hm
  have hp : (roleView N σ.b σ.n σ.v).Positive := NodeSplit.roleView_positive N σ.hpos hd
  have hf : 0 < f := Nat.div_pos hm (by have := N.two_le_width; omega)
  have hwv : (roleView N σ.b σ.n σ.v).width = (N.width * f) * σ.b := rfl
  set E := RecursiveCallProtocol.entered (NodePark.parked N w) (wireSlot N w) (io N) (volume prime (roleView N σ.b σ.n σ.v))
    (bank (roles data) (hdr (roleView N σ.b σ.n σ.v)) σ.f σ.p node₂ σ.scalar (nodeC N σ.b f) σ.st)
  have hsc : 0 + r * f ≤ N.width * f := by
    rw [zero_add]; exact Nat.mul_le_mul_right _ hrr.2.le
  have hvτ : volume prime (NodeCall.childView (N := N) σ.b f r (roleView N σ.b σ.n σ.v)) = volume prime (roleView N σ.b σ.n σ.v) :=
    RevMachine.sub_volume _ _ _ _ _ (roleView N σ.b σ.n σ.v) hwv hsc
  have hsaved := RecursiveStackAllocation.saved_stacks_available (hdr (roleView N σ.b σ.n σ.v)) σ.st code hok.desc hok.pc
  have hpc := RevNode.savedStacks_pc (hdr (roleView N σ.b σ.n σ.v)) σ.st code
  let τ : Frame (pcs N) capacity :=
    { v := NodeCall.childView (N := N) σ.b f r (roleView N σ.b σ.n σ.v)
      n := r * f
      b := σ.b
      hpos := Family.sub_positive hp
      hb := σ.hb
      hw := rfl
      f := E.tape (RecursiveCallBank.controlSlot 2)
      p := E.head (RecursiveCallBank.controlSlot 2)
      node := node₂
      scalar := σ.scalar
      st := RecursiveChildCallSetup.savedStacks (hdr (roleView N σ.b σ.n σ.v)) σ.st code
      hfree := RecursiveRowsNode.saved_available _ _ (RecursiveRowsNode.saved_available _ _ σ.hfree)
      ret := .recover i
      g := σ.st.tape 1
      q := σ.st.head 1
      hcode := ⟨hpc.1, hpc.2, fun j _ => hok.pc _ (by omega)⟩ }
  have hdepth := RevNode.depth_child (fun r h => (hRk r h).2) hm (GraphContract.rank_mem Prod.snd (pcs N) i.val i.isLt (w, r) hi)
  have hτok : Ok N b₀ τ :=
    { b := hok.b
      rows := dvd_child hdepth hok.rows
      pay := NodePark.entered_blank_suffix N (u := 1+(1+K)) w (volume prime (roleView N σ.b σ.n σ.v)) (roles data) (hdr (roleView N σ.b σ.n σ.v)) σ.f σ.p
        (node₂.append (σ.scalar.append (CommonBank.counters (nodeC N σ.b f)))) σ.st hok.pay
      desc := hsaved.1
      pc := hsaved.2 }
  have hbits := RevNode.bits_encoded (hinv.2 _ (NodeBank.wireSlot_ne_io N w))
  obtain ⟨xd, hxd⟩ := hbits
  refine ⟨τ, hτok, rfl, ?_, rfl, rfl, childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w))),
    ⟨Family.sub_positive hp, fun j => xd (Fin.cast hvτ j), ?_⟩, _, _, le_rfl,
    NodeCall.enter_runs w code hp σ.hb hf hwv hrr.1 hrr.2 data hinv.1, ?_⟩
  · -- the volume
    have h1 := RecursiveInterchangeLayout.role_volume_mul prime N.roleCount (midView N σ.b σ.n σ.v) hd
    have h2 := NodeSplit.mid_volume N (b := σ.b) (n := σ.n) (v := σ.v) σ.hw
    have hW : (N.roleCount : ℝ) ≠ 0 := by exact_mod_cast (NodeSplit.roleCount_pos N σ.hpos hd).ne'
    change (volume prime (NodeCall.childView (N := N) σ.b f r (roleView N σ.b σ.n σ.v)) : ℝ) = _
    rw [hvτ, eq_div_iff hW]
    exact_mod_cast h1.trans h2
  · rw [hxd]
    exact congrArg (childRoles N) (NodeSplit.source_cast hvτ _).symm
  · rintro rr' ⟨-, x'', rfl⟩
    set out : Fin (volume prime (roleView N σ.b σ.n σ.v)) → Fin 4 := fun j => SparseRoleCircuit.encode (x'' (Fin.cast hvτ.symm j))
    have hout : RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded x'') =
        RecursiveShiftRoleBank.source out := (NodeSplit.source_cast hvτ.symm _).symm
    have hpop := RevNode.popped_saved (hdr (roleView N σ.b σ.n σ.v)) σ.st code
    refine ⟨_, ⟨Function.update data (wireSlot N w) out, ⟨?_, fun j hj => ?_⟩, rfl⟩, ?_⟩
    · rw [Function.update_of_ne (NodeBank.wireSlot_ne_io N w).symm]; exact hinv.1
    · by_cases hjw : j = wireSlot N w
      · subst hjw; rw [Function.update_self]; exact fun z => ⟨_, rfl⟩
      · rw [Function.update_of_ne hjw]; exact hinv.2 j hj
    · change Runs (NodeCall.recoverB N w) (bank _ (hdr τ.v) τ.f τ.p τ.node τ.scalar (Prepare.rest τ.b N.width)
        (Family.popped τ.st τ.g τ.q)) _ _
      simp only [τ]
      rw [hpop, hout]
      exact NodeCall.recover_runs w hp σ.hb hf hwv data hinv.1 hok.pay hok.desc out

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
