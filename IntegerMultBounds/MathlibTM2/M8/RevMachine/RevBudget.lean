module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CounterCostBounds

/-!
# The frames' own budgets

Every block of a frame of `n` atoms of width `b` on volume `V` costs at most a constant times
`M = (n + 1) V + ℓ V`, with `ℓ` the length of the binary word of `b` (`Meas`): the preparation
and the counters divide by `b`, every other block is linear in the volume or the atom count. The
constants depend only on the network and the return-code width. So a frame's own cost, without
its children, is at most `K M` plus one leaf core per leaf (`own_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs ranks)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume)
open NodeBank (tapes io)
open Family (Frame inv)
open RevHalf (pcs Rk Ok)
open NodeSplit (midView roleView)

/-! ### Arithmetic -/

/-- The divisor constant of the atom width. -/
theorem lc_le (b : ℕ) : BinaryDescriptorDivMod.linearConstant (bits b) ≤ 296 * (bits b).length + 3522 := by
  unfold BinaryDescriptorDivMod.linearConstant; omega

variable (N : RevNetwork) {k : ℕ} {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

/-- The measure of a frame. -/
def Meas (σ : Frame (pcs N) capacity) : ℕ :=
  (σ.n + 1) * volume prime σ.v + (bits σ.b).length * volume prime σ.v

variable {N}

/-- The basic sizes of a frame. -/
structure Sizes (σ : Frame (pcs N) capacity) : Prop where
  one : 1 ≤ volume prime σ.v
  n : σ.n ≤ volume prime σ.v
  nb : σ.n * σ.b ≤ volume prime σ.v
  b : σ.b ≤ volume prime σ.v
  vm : volume prime σ.v ≤ Meas N σ
  nm : σ.n * volume prime σ.v ≤ Meas N σ
  lm : (bits σ.b).length * volume prime σ.v ≤ Meas N σ
  hl : ∀ i, (hdr σ.v i).length ≤ 2 * volume prime σ.v

theorem sizes (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) : Sizes σ := by
  have hV := RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le σ.v σ.hpos
  have hwv := NodeCall.width_le_volume σ.v σ.hpos
  rw [σ.hw] at hwv
  have hb := σ.hb
  refine ⟨hV, ?_, hwv, ?_, ?_, ?_, ?_, RecursiveRowsNode.header_length σ.v σ.hpos _ (Routines.hdr_headers σ.v)⟩
  · exact (Nat.le_mul_of_pos_right _ hb).trans hwv
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans hwv
  · unfold Meas; nlinarith
  · unfold Meas; nlinarith
  · unfold Meas; omega

theorem one_le_meas (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) : 1 ≤ Meas N σ :=
  (sizes σ hn).one.trans (sizes σ hn).vm

/-- The divisions by the atom width. -/
theorem div_b_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) {x : ℕ} (hx : x ≤ σ.n * σ.b) :
    BinaryDescriptorDivMod.linearConstant (bits σ.b) * (x + 1) + 2 * σ.b + 6 ≤ 8000 * Meas N σ := by
  have s := sizes σ hn
  have h1 : BinaryDescriptorDivMod.linearConstant (bits σ.b) * (x + 1) ≤
      (296 * (bits σ.b).length + 3522) * (2 * volume prime σ.v) :=
    Nat.mul_le_mul (lc_le σ.b) (by have := s.nb; have := s.one; omega)
  nlinarith [s.vm, s.lm, s.one, s.b]

/-- The divisions by the cutoff. -/
theorem div_m_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) {x : ℕ} (hx : x ≤ σ.n) :
    BinaryDescriptorDivMod.linearConstant (bits N.width) * (x + 1) ≤
      2 * BinaryDescriptorDivMod.linearConstant (bits N.width) * Meas N σ := by
  have s := sizes σ hn
  have : x + 1 ≤ 2 * Meas N σ := by have := s.n; have := s.vm; have := s.one; omega
  nlinarith

theorem len_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) {x : ℕ} (hx : x ≤ σ.n) :
    (bits x).length ≤ 2 * Meas N σ := by
  have s := sizes σ hn
  have := bits_len x; have := s.n; have := s.vm; have := s.one; omega

/-! ### Leaves, preparation and finish -/

theorem prep_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) :
    Family.prepCost σ.b N.width σ.n ≤ (8001 + 2 * BinaryDescriptorDivMod.linearConstant (bits N.width)) * Meas N σ := by
  have h1 := div_b_le σ hn (x := σ.n * σ.b) le_rfl
  have h2 := div_m_le σ hn (x := σ.n) le_rfl
  have := one_le_meas σ hn
  unfold Family.prepCost
  nlinarith

theorem leaf_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) (coreCost : ℕ → ℕ → ℕ) :
    Family.leafCost coreCost σ.v σ.b σ.n ≤ 2400 * Meas N σ + coreCost (volume prime σ.v) σ.b := by
  have s := sizes σ hn
  have hh : Family.hlen σ.v ≤ volume prime σ.v + 1 := by
    have := Nat.log2_le_self (volume prime σ.v); unfold Family.hlen; omega
  unfold Family.leafCost
  have := s.vm; have := s.one; have := s.n
  omega

theorem finish_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) :
    Family.finishCost N.width σ.n ≤ 40 * Meas N σ := by
  have h1 := len_le σ hn (x := σ.n / N.width) (Nat.div_le_self _ _)
  have h2 := len_le σ hn (x := σ.n) le_rfl
  have h3 := len_le σ hn (x := 0) (Nat.zero_le _)
  have := one_le_meas σ hn
  unfold Family.finishCost
  omega

/-! ### The node's views -/

structure ViewSizes (σ : Frame (pcs N) capacity) : Prop where
  mid : volume prime (midView N σ.b σ.n σ.v) = volume prime σ.v
  role : volume prime (roleView N σ.b σ.n σ.v) ≤ volume prime σ.v
  midPos : (midView N σ.b σ.n σ.v).Positive
  rolePos : (roleView N σ.b σ.n σ.v).Positive
  hmid : ∀ i, (hdr (midView N σ.b σ.n σ.v) i).length ≤ 2 * volume prime σ.v
  hrole : ∀ i, (hdr (roleView N σ.b σ.n σ.v) i).length ≤ 2 * volume prime σ.v

theorem viewSizes (σ : Frame (pcs N) capacity) (hd : N.roleCount ∣ σ.v.rows) : ViewSizes σ := by
  have hmid := NodeSplit.mid_volume N (b := σ.b) (n := σ.n) (v := σ.v) σ.hw
  have hW := NodeSplit.roleCount_pos N σ.hpos hd
  have hr := RecursiveInterchangeLayout.role_volume_mul prime N.roleCount (midView N σ.b σ.n σ.v) hd
  have hrole : volume prime (roleView N σ.b σ.n σ.v) ≤ volume prime σ.v := by
    rw [← hmid, ← hr]; exact Nat.le_mul_of_pos_right _ hW
  have hmp := NodeSplit.mid_positive N (b := σ.b) (n := σ.n) σ.hpos
  have hrp := NodeSplit.roleView_positive N (b := σ.b) (n := σ.n) σ.hpos hd
  refine ⟨hmid, hrole, hmp, hrp, fun i => ?_, fun i => ?_⟩
  · have := RecursiveRowsNode.header_length _ hmp _ (Routines.hdr_headers _) i
    rwa [hmid] at this
  · have := RecursiveRowsNode.header_length _ hrp _ (Routines.hdr_headers _) i
    omega

/-- The constant of the split. -/
def splitK (N : RevNetwork) : ℕ :=
  2 * BinaryDescriptorDivMod.linearConstant (bits N.width) + 10000 +
    (74 + RecursiveRowsNode.rowConstant N.roleCount + RecursiveRowsNodeRoleBank.constant N.roleCount) +
    M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N NodeSplit.zeroBit)

theorem split_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) (hd : N.roleCount ∣ σ.v.rows) :
    NodeSplit.splitCost (N := N) σ.v σ.b σ.n ≤ splitK N * Meas N σ := by
  have s := sizes σ hn
  have w := viewSizes σ hd
  have hM := one_le_meas σ hn
  have h1 : NodeSplit.splitCountersCost σ.n N.width ≤ (2 * BinaryDescriptorDivMod.linearConstant (bits N.width) + 300) *
      Meas N σ := by
    have a1 := div_m_le σ hn (x := σ.n) le_rfl
    have a2 := len_le σ hn (x := σ.n / N.width) (Nat.div_le_self _ _)
    have a3 := len_le σ hn (x := 0) (Nat.zero_le _)
    have a4 : N.width * (σ.n / N.width) ≤ σ.n := Nat.mul_div_le _ _
    have a5 : σ.n / N.width ≤ σ.n := Nat.div_le_self _ _
    have := s.n; have := s.vm
    unfold NodeSplit.splitCountersCost
    nlinarith
  have h2 := RecursiveViewFrame.pushCost_le (hdr σ.v) _ s.hl
  have h3 := RecursiveRowsNode.entry_cost_linear (c := N.roleCount) _ w.midPos _ (Routines.hdr_headers _)
  rw [w.mid] at h3
  have h4 := len_le σ hn (x := σ.n) le_rfl
  have h5 := len_le σ hn (x := σ.n % N.width) (Nat.mod_le _ _)
  have h6 := len_le σ hn (x := N.width * (σ.n / N.width)) (Nat.mul_div_le _ _)
  have h7 := len_le σ hn (x := 0) (Nat.zero_le _)
  have h8 : M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N NodeSplit.zeroBit) *
      volume prime (roleView N σ.b σ.n σ.v) ≤
      M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N NodeSplit.zeroBit) * Meas N σ :=
    Nat.mul_le_mul_left _ (w.role.trans s.vm)
  have h9 : (74 + RecursiveRowsNode.rowConstant N.roleCount + RecursiveRowsNodeRoleBank.constant N.roleCount) *
      volume prime σ.v ≤ (74 + RecursiveRowsNode.rowConstant N.roleCount + RecursiveRowsNodeRoleBank.constant N.roleCount) *
      Meas N σ := Nat.mul_le_mul_left _ s.vm
  have := s.vm; have := s.one
  unfold NodeSplit.splitCost splitK
  rw [w.mid]
  nlinarith

/-- The constant of the merge. -/
def mergeK (N : RevNetwork) : ℕ :=
  2 * BinaryDescriptorDivMod.linearConstant (bits N.width) + 20000 + (128 + RecursiveRowsNode.rowConstant N.roleCount) +
    M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N blank)

theorem merge_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) (hd : N.roleCount ∣ σ.v.rows) :
    NodeSplit.mergeCost (N := N) σ.v σ.b σ.n ≤ mergeK N * Meas N σ := by
  have s := sizes σ hn
  have w := viewSizes σ hd
  have hM := one_le_meas σ hn
  have h1 : NodeSplit.mergeCountersCost σ.b σ.n N.width ≤
      (2 * BinaryDescriptorDivMod.linearConstant (bits N.width) + 8100) * Meas N σ := by
    have a1 := div_m_le σ hn (x := σ.n) le_rfl
    have a2 := div_b_le σ hn (x := σ.n * σ.b) le_rfl
    have a3 := len_le σ hn (x := σ.n / N.width) (Nat.div_le_self _ _)
    have a4 := len_le σ hn (x := σ.n / N.width - 1) (by have := Nat.div_le_self σ.n N.width; omega)
    have a5 := len_le σ hn (x := σ.n % N.width) (Nat.mod_le _ _)
    unfold NodeSplit.mergeCountersCost
    nlinarith
  have h2 := RecursiveRowsNode.exit_cost_linear (c := N.roleCount) _ w.midPos (NodeSplit.roleCount_pos N σ.hpos hd) hd
    _ _ (Routines.hdr_headers _) (Routines.hdr_headers _)
  rw [w.mid, show RecursiveInterchangeLayout.role (midView N σ.b σ.n σ.v) N.roleCount =
    roleView N σ.b σ.n σ.v from rfl] at h2
  have h3 := RecursiveViewFrame.restoreCost_le (hdr σ.v) (hdr (midView N σ.b σ.n σ.v)) _ s.hl w.hmid
  have h8 : M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N blank) *
      volume prime (roleView N σ.b σ.n σ.v) ≤ M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N blank) * Meas N σ :=
    Nat.mul_le_mul_left _ (w.role.trans s.vm)
  have h9 : (128 + RecursiveRowsNode.rowConstant N.roleCount) * volume prime σ.v ≤
      (128 + RecursiveRowsNode.rowConstant N.roleCount) * Meas N σ := Nat.mul_le_mul_left _ s.vm
  have := s.vm; have := s.one
  unfold NodeSplit.mergeCost mergeK
  rw [w.mid]
  nlinarith

/-! ### Pieces -/

open Classical in
/-- The constant of a nonrecursive piece. -/
def segK (N : RevNetwork) : Schedule.Seg (N.World ⊕ N.Temp) N.width → ℕ
  | .edge w ops =>
    if h : ∀ o ∈ AtomSegment.atoms ops, AtomRolePlan.Fits N.width o then
      AtomRoleSegment.chainConst (NodeBank.wireSlot N w) (AtomRoleSegment.sops ops h)
    else 0
  | .gate g => M8.Machine.RoleOpsClean.coefficient (RevNode.gateOp N g)
  | .reset w => M8.Machine.RoleOpsClean.coefficient
      [.fill ⟨io N, NodeBank.wireSlot N w, (NodeBank.wireSlot_ne_io N w).symm⟩ NodeSplit.zeroBit]

theorem seg_le (σ : Frame (pcs N) capacity) (hn : 1 ≤ σ.n) (hd : N.roleCount ∣ σ.v.rows)
    (sg : Schedule.Seg (N.World ⊕ N.Temp) N.width) : RevHalf.segCost N σ sg ≤ segK N sg * Meas N σ := by
  have s := sizes σ hn
  have w := viewSizes σ hd
  have hr : volume prime (roleView N σ.b σ.n σ.v) ≤ Meas N σ := w.role.trans s.vm
  cases sg with
  | edge wi ops =>
    simp only [RevHalf.segCost, segK]
    split_ifs
    · have h1 : σ.n / N.width * volume prime (roleView N σ.b σ.n σ.v) ≤ Meas N σ :=
        (Nat.mul_le_mul (Nat.div_le_self _ _) w.role).trans s.nm
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ h1
    · simp
  | gate g => exact Nat.mul_le_mul_left _ hr
  | reset wi => exact Nat.mul_le_mul_left _ hr

/-! ### Calls -/

/-- The constant of a call. -/
def callK (N : RevNetwork) (k : ℕ) : ℕ :=
  180 * tapes N + 120000 + k + 2 * (N.width + 1) * (2 * N.width + 57) +
    4 * BinaryDescriptorDivMod.linearConstant (bits N.width) + 9000

theorem call_le (σ : Frame (pcs N) capacity) (hm : N.width ≤ σ.n) (hd : N.roleCount ∣ σ.v.rows)
    (c : Schedule.Call (N.World ⊕ N.Temp)) (hc1 : 1 ≤ c.2) (hc : c.2 < N.width) :
    RevHalf.callCost N σ c ≤ callK N k * Meas N σ := by
  unfold RevHalf.callCost
  have hn : 1 ≤ σ.n := le_trans (by have := N.two_le_width; omega) hm
  have s := sizes σ hn
  have w := viewSizes σ hd
  have hM := one_le_meas σ hn
  have hr : volume prime (roleView N σ.b σ.n σ.v) ≤ Meas N σ := w.role.trans s.vm
  set M := Meas N σ
  set V := volume prime (roleView N σ.b σ.n σ.v)
  set f := σ.n / N.width
  set LC := BinaryDescriptorDivMod.linearConstant (bits N.width)
  have hf : f ≤ σ.n := Nat.div_le_self _ _
  have fM : f ≤ M := hf.trans (s.n.trans s.vm)
  have hmf : N.width * f ≤ σ.n := Nat.mul_div_le _ _
  have hpl := NodePark.parked_length_le N c.1
  set P := (N.width + 1) * ((2 * N.width + 57) * M)
  set A := (88 * tapes N + 51883) * M
  set B := (92 * tapes N + 51883) * M
  -- entry
  have a1 := advs_le (r := c.2 - 1) (m := N.width) fM hM (by omega)
  have a2 := advs_le (r := N.width - c.2 - 1) (m := N.width) fM hM (by omega)
  have l1 := len_le σ hn (x := f) hf
  have l2 := len_le σ hn (x := f - 1) (by omega)
  have hpay : (88 * (NodePark.parked N c.1).length + 51883) * V ≤ A := Nat.mul_le_mul (by omega) hr
  have le1 := len_le σ hn (x := (N.width - c.2) * f) (by
    have : (N.width - c.2) * f ≤ N.width * f := Nat.mul_le_mul_right _ (Nat.sub_le _ _); omega)
  have le2 := len_le σ hn (x := c.2 * f) (by
    have : c.2 * f ≤ N.width * f := Nat.mul_le_mul_right _ hc.le; omega)
  have le3 := len_le σ hn (x := 0) (Nat.zero_le _)
  have hk : k ≤ k * M := Nat.le_mul_of_pos_right _ hM
  have hent : NodeCall.enterCost (N := N) c.1 f c.2 k V ≤ A + 2 * P + k * M + 1800 * M := by
    unfold NodeCall.enterCost NodeCall.countersCost
    omega
  -- recovery
  have hsum : (N.width - c.2) * f + c.2 * f = N.width * f := by rw [← Nat.add_mul, Nat.sub_add_cancel hc.le]
  have he : (N.width - c.2) * f = N.width * f - 0 - c.2 * f := by omega
  have hres := Enter.restore_cost_le (q := prime) Networks.Shared50ModularControl.prime_prime.two_le w.rolePos
    (n := N.width * f) (w := σ.b) (s := 0) (c := c.2 * f) (e := (N.width - c.2) * f) rfl (by omega) he
    (Routines.hdr_headers _)
  rw [Routines.hdr_eq (Headers.child_headers (Routines.hdr_headers (roleView N σ.b σ.n σ.v)) he)] at hres
  have d1 := div_b_le σ hn (x := N.width * f * σ.b) (Nat.mul_le_mul_right _ hmf)
  have d2 := div_m_le σ hn (x := N.width * f) hmf
  have e2 : 2 * LC * M = 2 * (LC * M) := by ring
  rw [e2] at d2
  have m1 := len_le σ hn (x := N.width * f) hmf
  have hpay' : (92 * (NodePark.parked N c.1).length + 51883) * V ≤ B := Nat.mul_le_mul (by omega) hr
  have hrec : NodeCall.recoverCost (N := N) c.1 (hdr (roleView N σ.b σ.n σ.v))
      (hdr (NodeCall.childView (N := N) σ.b f c.2 (roleView N σ.b σ.n σ.v))) σ.b f V ≤
      B + 2 * (LC * M) + 8300 * M := by
    unfold NodeCall.recoverCost NodeCall.recCountersCost NodeCall.childView
    omega
  have hK : callK N k * M = A + B + 2 * P + k * M + 4 * (LC * M) + 25234 * M := by
    simp only [A, B, P, LC, callK]; ring
  rw [hK]
  omega

/-! ### The schedule -/

variable (N) in
/-- The constant of the schedule's pieces. -/
def piecesK (k : ℕ) : List (Graph.Piece (Schedule.Seg (N.World ⊕ N.Temp) N.width) (Schedule.Call (N.World ⊕ N.Temp))) → ℕ
  | [] => 0
  | .seg sg :: l => segK N sg + 1 + piecesK k l
  | .call _ :: l => callK N k + 2 + piecesK k l

theorem mem_ranks {Seg Call : Type} (rank : Call → ℕ) :
    ∀ (l : List (Graph.Piece Seg Call)) (c : Call), Graph.Piece.call c ∈ l → rank c ∈ ranks rank l
  | [], _, h => by simp at h
  | .seg _ :: l, c, h => by
    simp only [List.mem_cons, reduceCtorEq, false_or] at h
    exact mem_ranks rank l c h
  | .call c' :: l, c, h => by
    simp only [ranks, List.mem_cons] at h ⊢
    rcases h with h | h
    · cases h; exact Or.inl rfl
    · exact Or.inr (mem_ranks rank l c h)

theorem pieces_le (σ : Frame (pcs N) capacity) (hm : N.width ≤ σ.n) (hd : N.roleCount ∣ σ.v.rows) :
    ∀ l : List (Graph.Piece (Schedule.Seg (N.World ⊕ N.Temp) N.width) (Schedule.Call (N.World ⊕ N.Temp))),
      (∀ c, Graph.Piece.call c ∈ l → 1 ≤ c.2 ∧ c.2 < N.width) →
      (l.map (GraphContract.segCall (fun sg => (RevHalf.segCost N σ sg : ℝ) + 1)
        fun c => (RevHalf.callCost N σ c : ℝ) + 2)).sum ≤ (piecesK N k l : ℝ) * Meas N σ
  | [], _ => by simp [piecesK]
  | .seg sg :: l, h => by
    have hn : 1 ≤ σ.n := le_trans (by have := N.two_le_width; omega) hm
    have ih := pieces_le σ hm hd l (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have h1 : (RevHalf.segCost N σ sg : ℝ) ≤ (segK N sg : ℝ) * Meas N σ := by exact_mod_cast seg_le σ hn hd sg
    have hM : (1 : ℝ) ≤ Meas N σ := by exact_mod_cast one_le_meas σ hn
    simp only [List.map_cons, List.sum_cons, GraphContract.segCall, piecesK]
    push_cast
    nlinarith
  | .call c :: l, h => by
    have hn : 1 ≤ σ.n := le_trans (by have := N.two_le_width; omega) hm
    have ih := pieces_le σ hm hd l (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hc := h c List.mem_cons_self
    have h1 : (RevHalf.callCost N σ c : ℝ) ≤ (callK N k : ℝ) * Meas N σ := by exact_mod_cast call_le σ hm hd c hc.1 hc.2
    have hM : (1 : ℝ) ≤ Meas N σ := by exact_mod_cast one_le_meas σ hn
    simp only [List.map_cons, List.sum_cons, GraphContract.segCall, piecesK]
    push_cast
    nlinarith

/-! ### A frame's own cost -/

variable (N) in
/-- The constant of a frame's own cost. -/
def ownK (k : ℕ) : ℕ :=
  (8001 + 2 * BinaryDescriptorDivMod.linearConstant (bits N.width)) + 1 + N.width * 2403 + 2 +
    (splitK N + 1 + piecesK N k (pcs N) + (mergeK N + 1)) + 41 + (k + 2)

/-- **A frame's own cost** is at most `K M` plus one leaf core per leaf. -/
theorem own_le [M8.Machine.Net] (hR : RevRuns N) (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (b₀ : ℕ)
    (hm0 : 0 < N.width) (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hn : 1 ≤ σ.n) :
    (inv (Rev97Node.leafCore N) hm0 (Rev97Node.half N hR hRk b₀ capacity)).ownCost σ ≤
      (ownK N k : ℝ) * Meas N σ + N.width * (LeafCore.coreCost (volume prime σ.v) σ.b : ℝ) := by
  have hM : (1 : ℝ) ≤ Meas N σ := by exact_mod_cast one_le_meas σ hn
  have h0 : (0 : ℝ) ≤ Meas N σ := by linarith
  have hp : (Family.prepCost σ.b N.width σ.n : ℝ) ≤
      ((8001 + 2 * BinaryDescriptorDivMod.linearConstant (bits N.width) : ℕ) : ℝ) * Meas N σ := by
    exact_mod_cast prep_le σ hn
  have hl : (Family.leafCost LeafCore.coreCost σ.v σ.b σ.n : ℝ) ≤
      2400 * Meas N σ + (LeafCore.coreCost (volume prime σ.v) σ.b : ℝ) := by
    exact_mod_cast leaf_le σ hn LeafCore.coreCost
  have hfi : (Family.finishCost N.width σ.n : ℝ) ≤ 40 * Meas N σ := by exact_mod_cast finish_le σ hn
  have hlv : (σ.n % N.width : ℕ) ≤ N.width := (Nat.mod_lt _ hm0).le
  have hlv' : ((σ.n % N.width : ℕ) : ℝ) ≤ N.width := by exact_mod_cast hlv
  have hcore : (0 : ℝ) ≤ LeafCore.coreCost (volume prime σ.v) σ.b := Nat.cast_nonneg _
  have hleaves : ((σ.n % N.width : ℕ) : ℝ) * (1 + 1 + ((Family.leafCost LeafCore.coreCost σ.v σ.b σ.n : ℝ) + 1)) ≤
      N.width * (3 + 2400 * Meas N σ + LeafCore.coreCost (volume prime σ.v) σ.b) := by
    apply mul_le_mul hlv' (by linarith) (by positivity) (by positivity)
  have hnode : (if N.width ≤ σ.n then (NodeSplit.splitCost (N := N) σ.v σ.b σ.n : ℝ) + 1 +
      ((pcs N).map (GraphContract.segCall (fun sg => (RevHalf.segCost N σ sg : ℝ) + 1)
        fun c => (RevHalf.callCost N σ c : ℝ) + 2)).sum + ((NodeSplit.mergeCost (N := N) σ.v σ.b σ.n : ℝ) + 1)
      else 0) ≤ ((splitK N + 1 + piecesK N k (pcs N) + (mergeK N + 1) : ℕ) : ℝ) * Meas N σ := by
    split_ifs with hm
    · have hd := RevHalf.rows_dvd hok hm
      have h1 : (NodeSplit.splitCost (N := N) σ.v σ.b σ.n : ℝ) ≤ (splitK N : ℝ) * Meas N σ := by
        exact_mod_cast split_le σ hn hd
      have h2 : (NodeSplit.mergeCost (N := N) σ.v σ.b σ.n : ℝ) ≤ (mergeK N : ℝ) * Meas N σ := by
        exact_mod_cast merge_le σ hn hd
      have h3 := pieces_le (k := k) σ hm hd (pcs N) (fun c hc => hRk _ (mem_ranks Prod.snd _ c hc))
      push_cast
      nlinarith
    · positivity
  unfold GraphExists.Inv.ownCost
  simp only [Family.inv, Rev97Node.half]
  have hk : ((k : ℝ) + 2) ≤ ((k + 2 : ℕ) : ℝ) * Meas N σ := by
    push_cast; nlinarith
  have hW : (N.width : ℝ) * 3 ≤ N.width * 3 * Meas N σ := by
    have : (0 : ℝ) ≤ N.width := Nat.cast_nonneg _
    nlinarith
  unfold ownK
  push_cast at hnode hp hk ⊢
  by_cases hm : N.width ≤ σ.n <;> simp only [hm, ↓reduceIte] at hnode ⊢ <;> linarith

/-- The leaf core's cost is at most `|C| V L` when `max(1, b)^τ ≤ L`. -/
theorem coreCost_le [M8.Machine.Net] (V b : ℕ) {L : ℝ} (hτ : ((max 1 b : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L) :
    (LeafCore.coreCost V b : ℝ) ≤ |LeafCore.C| * V * L := by
  have hB : (0 : ℝ) ≤ ((max 1 b : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau := by positivity
  have hx : LeafCore.C * V * ((max 1 b : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ |LeafCore.C| * V * L := by
    have : LeafCore.C * V ≤ |LeafCore.C| * V := mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
    have h0 : (0 : ℝ) ≤ |LeafCore.C| * V := by positivity
    calc _ ≤ |LeafCore.C| * V * ((max 1 b : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau :=
          mul_le_mul_of_nonneg_right this hB
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ h0
  unfold LeafCore.coreCost
  by_cases h : 0 ≤ LeafCore.C * V * ((max 1 b : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau
  · exact (Nat.floor_le h).trans hx
  · rw [Nat.floor_of_nonpos (not_le.mp h).le]
    have : 0 ≤ L := hB.trans hτ
    simp only [Nat.cast_zero]
    positivity

/-! ### The stage-2 PR97 family -/

/-- **The stage-2 PR97 family**: every frame of atom width `b₀` runs within
`C/(1-q₁) n + C/(1-q_τ) n^τ* L` of its volume, for every `L` above the binary length of `b₀` and
`max(1, b₀)^τ`. -/
theorem rev97_family [M8.Machine.Net] (b₀ : ℕ) {k : ℕ}
    (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ n, 1 ≤ n → GraphExists.Contract (ht := Family.pcSlot_pos)
        (inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos (Rev97Node.half97 b₀ capacity)) n
        (C / (1 - Stage2Moments.q₁) * n +
          C / (1 - Stage2Moments.qτB) * ((n : ℝ) ^ (1 - (Stage2Moments.savingB : ℝ)) * L)) := by
  set K : ℝ := ((ownK rev97m k : ℕ) : ℝ)
  set D : ℝ := |LeafCore.C|
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hD : 0 ≤ D := abs_nonneg _
  refine ⟨530 * K + 529 * D, by positivity, fun L hL hℓ hτ => ?_⟩
  have key : ∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n →
      (inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos (Rev97Node.half97 b₀ capacity)).ownCost σ ≤
        K * ((σ.n + 1) * volume prime σ.v + L * volume prime σ.v) + 529 * D * L * volume prime σ.v := by
    intro σ hok hn
    have h := own_le runs_rev97m Rev97Node.rk97 b₀ Rev97Node.width97_pos σ hok hn
    have hw : (rev97m.width : ℝ) = 529 := by exact_mod_cast (rfl : rev97m.width = 529)
    have hc := coreCost_le (volume prime σ.v) σ.b (L := L) (by rw [hok.b]; exact hτ)
    have hV : (0 : ℝ) ≤ volume prime σ.v := Nat.cast_nonneg _
    have hM : (Meas rev97m σ : ℝ) ≤ (σ.n + 1) * volume prime σ.v + L * volume prime σ.v := by
      unfold Meas
      push_cast
      rw [hok.b]
      nlinarith
    rw [hw] at h
    calc _ ≤ _ := h
      _ ≤ _ := by nlinarith
  have hV : ∀ σ : Frame (pcs rev97m) capacity, (0 : ℝ) ≤ volume prime σ.v := fun _ => Nat.cast_nonneg _
  refine Rev97Node.rev97_node b₀ capacity (by positivity) (by linarith) (fun σ hok hn hlt => ?_) (fun σ hok hn => ?_)
  · refine (key σ hok hn).trans ?_
    have h1 : ((σ.n : ℝ) + 1) ≤ 529 * L := by
      have : (σ.n : ℝ) + 1 ≤ 529 := by exact_mod_cast hlt
      linarith
    have := hV σ
    have h2 : ((σ.n : ℝ) + 1) * volume prime σ.v ≤ 529 * L * volume prime σ.v := mul_le_mul_of_nonneg_right h1 this
    nlinarith
  · have hn1 : 1 ≤ σ.n := le_trans (by norm_num) hn
    refine (key σ hok hn1).trans ?_
    have := hV σ
    have hLV : (volume prime σ.v : ℝ) ≤ L * volume prime σ.v := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hLV hK
    have e2 : 0 ≤ K * (L * volume prime σ.v) := by positivity
    have e3 : 0 ≤ D * (σ.n * volume prime σ.v) := by positivity
    have e4 : 0 ≤ K * (σ.n * volume prime σ.v) := by positivity
    have e5 : 0 ≤ D * (L * volume prime σ.v) := by positivity
    nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget
