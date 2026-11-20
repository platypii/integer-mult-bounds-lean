module

public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors
public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun

/-! Physical interchange of the unhosted interval on an idle owner's flag coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitHosting
open BitOccurrences

/-- Physical idle intervals, including empty spans, realize the charged rank list. -/
theorem remainderWidths_perm :
    (remainderIntervals.map fun e => e.2 - e.1).Perm remainders := by
  have widths : ∀ i : Fin 9, (idleRanks 4).getD i.val 0 =
      7 * idleTarget i.val - 7 * idleSource i.val := by decide +kernel
  apply List.Perm.trans _ remainders_perm
  apply List.Perm.of_eq
  simp only [remainderIntervals, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro k _
  rw [widths ⟨i, List.mem_range.mp hi⟩]
  change 7 * idleTarget i - (7 * idleSource i + 8*k) = (7 * idleTarget i - 7 * idleSource i) - 8*k
  omega

end IntegerMultBounds.MathlibTM2.M6.BitHosting

namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthOriginalTotalRun (program cost input)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

open RecursiveInterchangeLayout (Descriptor role)
open CopyChildLayout (spectators changeLayout packActive)
open Cover.Fallback (rankDescriptor)

open IntegerMultBounds.Networks.Certificates.PR589.Nine Matrix

/-- In flag coordinates the parent's rational remainder exchange swaps precisely
the selected positions. The omitted line component stays in the identity term. -/
theorem remainderExchange_flag (c : PortCertificate) (lo hi : ℕ) :
    let F := Matrix.fromBlocks c.flag 0 0 c.flag
    exchange (c.span lo hi) = 1 + F * (exchange (interval lo hi) - 1) * Fᵀ := by
  intro F
  simp only [F, exchange, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, PortCertificate.span]
  ext (i | i) (j | j) <;>
    simp [Matrix.one_apply, Matrix.sub_apply] <;> abel

/-- Projecting both parent address halves into a checked port flag commutes
with the remainder exchange. -/
theorem remainderExchange_read (c : PortCertificate) (hc : c.Checked) (lo hi : ℕ) :
    let F := Matrix.fromBlocks c.flag 0 0 c.flag
    Fᵀ * exchange (c.span lo hi) = exchange (interval lo hi) * Fᵀ := by
  intro F
  have orth : Fᵀ * F = 1 := by
    simp [F, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      c.flag_orthonormal hc, Matrix.fromBlocks_one]
  rw [remainderExchange_flag, Matrix.mul_add, Matrix.mul_one]
  change Fᵀ + Fᵀ * (F * _ * Fᵀ) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, orth, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul]
  abel

/-- Reading an actual parent address through the port flag gives an ordinary
interval swap on its 63 pending coordinates. -/
theorem remainderExchange_digits (c : PortCertificate) (hc : c.Checked) (lo hi : ℕ)
    (x : Axis ⊕ Axis → ℚ) :
    let F := Matrix.fromBlocks c.flag 0 0 c.flag
    let digits := Fᵀ *ᵥ x
    Fᵀ *ᵥ (exchange (c.span lo hi) *ᵥ x) =
      Sum.elim (fun p => if lo ≤ pendingIndex p ∧ pendingIndex p < hi then digits (.inr p)
        else digits (.inl p))
        (fun p => if lo ≤ pendingIndex p ∧ pendingIndex p < hi then digits (.inl p)
        else digits (.inr p)) := by
  intro F digits
  rw [Matrix.mulVec_mulVec, remainderExchange_read c hc, ← Matrix.mulVec_mulVec]
  change exchange (interval lo hi) *ᵥ digits = _
  funext i
  cases i with
  | inl p | inr p =>
    by_cases active : lo ≤ pendingIndex p ∧ pendingIndex p < hi <;>
      simp [exchange, Matrix.fromBlocks_mulVec, Matrix.sub_mulVec, interval,
        Matrix.mulVec_diagonal, active]

/-- The remaining coordinate on each half is the line of the port. Both
line projections retain their values under the parent's remainder exchange. -/
theorem remainderExchange_line (c : PortCertificate) (hc : c.Checked) (lo hi : ℕ) :
    let L := Matrix.fromBlocks c.linePart 0 0 c.linePart
    L * exchange (c.span lo hi) = L := by
  intro L
  have line : c.linePart * c.flag = 0 := by
    simp [PortCertificate.linePart, PortCertificate.flag, Matrix.fromBlocks_multiply,
      c.lineProj_mul_complement hc, Matrix.fromBlocks_zero]
  have disjoint : c.linePart * c.span lo hi = 0 := by
    rw [PortCertificate.span, ← Matrix.mul_assoc, ← Matrix.mul_assoc, line,
      Matrix.zero_mul, Matrix.zero_mul]
  simp [L, exchange, Matrix.fromBlocks_multiply, Matrix.mul_sub, disjoint]

open IntegerMultBounds.Swap.Modular

/-- Projecting the reduced parent exchange onto its port flag exchanges the
same interval on arbitrary modular digits, at every tape width. -/
theorem remainderExchange_modular (c : PortCertificate) (hc : c.Checked) (lo hi w : ℕ)
    (x : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
    let F := reduce (prime^w) c.flag
    let S := reduce (prime^w) (c.span lo hi)
    let y := M8.Exchange.exchange S x
    ∀ p, ((Fᵀ *ᵥ y.1) p, (Fᵀ *ᵥ y.2) p) =
      if lo ≤ pendingIndex p ∧ pendingIndex p < hi then ((Fᵀ *ᵥ x.2) p, (Fᵀ *ᵥ x.1) p)
      else ((Fᵀ *ᵥ x.1) p, (Fᵀ *ᵥ x.2) p) := by
  intro F S y p
  let m := prime^w
  have flag : Admissible m c.flag := by
    intro i j
    have bound : (c.flag i j).den ≤ 2 := (fullChart_entry c hc i (.inr j)).2
    exact Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (c.flag i j).den_pos.ne'
      (bound.trans_lt Shared50ModularControl.prime_odd) Shared50ModularControl.prime_prime).symm)
  let D : Matrix Pending Pending (ZMod m) := diagonal fun j =>
    if lo ≤ pendingIndex j ∧ pendingIndex j < hi then 1 else 0
  have sel : Admissible m (interval lo hi) := by
    intro i j
    simp only [interval, diagonal_apply]
    split_ifs <;> simp
  have reduced : reduce m (interval lo hi) = D := by
    ext i j
    simp only [reduce, Matrix.map_apply, interval, D, diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  have transposed : Admissible m c.flagᵀ := fun i j => flag j i
  have orth : Fᵀ * F = 1 := by
    change reduce m c.flagᵀ * reduce m c.flag = 1
    rw [← reduce_mul m transposed flag, c.flag_orthonormal hc, reduce_one]
  have span : S = F * D * Fᵀ := by
    change reduce m (c.flag * interval lo hi * c.flagᵀ) = _
    rw [reduce_mul m (admissible_mul m flag sel) transposed,
      reduce_mul m flag sel, reduced]
    rfl
  have commute : Fᵀ * S = D * Fᵀ := by
    rw [span, ← Matrix.mul_assoc, ← Matrix.mul_assoc, orth, Matrix.one_mul]
  have read (v : Axis → ZMod m) : Fᵀ *ᵥ (S *ᵥ v) = D *ᵥ (Fᵀ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, commute, Matrix.mulVec_mulVec]
  by_cases active : lo ≤ pendingIndex p ∧ pendingIndex p < hi <;>
    simp [y,M8.Exchange.exchange,Matrix.sub_mulVec,Matrix.mulVec_add,Matrix.mulVec_sub,
      read,D,-Matrix.mulVec_mulVec,Matrix.mulVec_diagonal,active]

/-- The idle owner's other digits and all its spectator positions are exactly
the middle gap and inherited fields of the parent's recursive rank descriptor. -/
theorem remainderSpectators (v : Descriptor) (rows w : ℕ)
    (splitRows : v.rows = 142080*rows) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let W := v.beforeRows*rows*v.beforeH*v.between*v.afterD
    spectators (phaseIntervalChild e.1 e.2 w W 64) =
      spectators (rankDescriptor prime ((e.2-e.1)*w) ((64-(e.2-e.1))*w) (role v 142080)) := by
  intro W
  obtain ⟨ordered, fits, _⟩ := BitHosting.remainder_counts e he
  have gap : 64-(e.2-e.1) = 64-e.2+e.1 := by omega
  simp only [spectators,phaseIntervalChild,rankDescriptor,role,W,splitRows,
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080),one_mul,gap,
    Nat.mul_comm (64-e.2+e.1) w,pow_mul,pow_add]
  ring

/-- The parent's recursive rank address and the idle interval address have the
same packed offset both before and after the exchange. -/
theorem remainderPacked_swap (v : Descriptor) (rows w : ℕ)
    (splitRows : v.rows = 142080*rows) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let child := phaseIntervalChild e.1 e.2 w (v.beforeRows*rows*v.beforeH*v.between*v.afterD) 64
    let parentChild := rankDescriptor prime ((e.2-e.1)*w) ((64-(e.2-e.1))*w) (role v 142080)
    let chart := changeLayout child parentChild rfl (remainderSpectators v rows w splitRows e he)
    ∀ a, (packActive parentChild (RecursiveInterchangeScaling.index
        (Shared50RecursiveNodeTranspose.swapAddress (chart a)))).val =
      (packActive child (RecursiveInterchangeScaling.index
        (Shared50RecursiveNodeTranspose.swapAddress a))).val := by
  intro child parentChild chart a
  exact CopyChildLayout.packActive_change child parentChild rfl
    (remainderSpectators v rows w splitRows e he) (Shared50RecursiveNodeTranspose.swapAddress a)

/-- A word representing the parent's rank child still represents it after
the physical exchange, at every parent address. -/
theorem remainderTranspose_represents (v : Descriptor) (rows w : ℕ)
    (splitRows : v.rows = 142080*rows) (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) :
    let child := phaseIntervalChild e.1 e.2 w (v.beforeRows*rows*v.beforeH*v.between*v.afterD) 64
    let parentChild := rankDescriptor prime ((e.2-e.1)*w) ((64-(e.2-e.1))*w) (role v 142080)
    let chart := changeLayout child parentChild rfl (remainderSpectators v rows w splitRows e he)
    ∀ (x : Fin (volume prime child) → ZMod 2) (p : Fin (volume prime parentChild) → ZMod 2),
      (∀ a, x (RecursiveInterchangeScaling.index a) = p (RecursiveInterchangeScaling.index (chart a))) →
      ∀ a, Shared50RecursiveNodeRows.transpose (one_dvd _) x (RecursiveInterchangeScaling.index a) =
        Shared50RecursiveNodeRows.transpose (one_dvd _) p (RecursiveInterchangeScaling.index (chart a)) := by
  intro child parentChild chart x p reads a
  let b := Shared50RecursiveNodeTranspose.swapAddress a
  have physical := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) x b
  have logical := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) p (chart b)
  exact physical.trans ((reads b).trans logical.symm)

/-- With its headers represented, one fixed program exchanges the idle interval on
the owner's tape, preserving both exterior slices even for an empty interval. -/
theorem remainderInterval_runs [M8.Machine.Net] {t w W : ℕ}
    (e : ℕ × ℕ) (hW : 0 < W)
    (caller : Tapes t prime) (headers : Fin 6 → Fin t) (src : Fin t)
    (hs : Fin 6 → List Bool) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    RecursiveDimensionBank.Headers child hs →
    (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) →
    (∀ i, caller.head (headers i) = 1) →
    ∀ x : Fin (volume prime child) → ZMod 2,
    caller.tape src = sourceWord x → caller.head src = 0 →
    ∃ y : Fin (volume prime child) → ZMod 2,
      HoareTime (program headers src) (fun z => z = input caller)
        (fun z => z = input (SharedPlacementAlphabet.setTape caller src (sourceWord y) 0))
        (cost child hs) ∧
      y = Shared50RecursiveNodeRows.transpose (one_dvd _) x ∧
      ∀ a b h d u v j,
        y (RecursiveInterchangeScaling.index (intervalAddress 64 a b d h u v j)) =
        x (RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v j)) := by
  intro child valid words heads x data origin
  have pos := pow_pos Shared50ModularControl.prime_prime.pos w
  have positive : child.Positive := ⟨Nat.zero_lt_one, Nat.zero_lt_one, pow_pos pos _,
    pow_pos pos _, Nat.mul_pos (pow_pos pos _) hW⟩
  exact ⟨_, M8.Machine.ArbitraryWidthOriginalTotalRun.runs caller headers src child hs
    positive valid words heads x data origin, rfl, intervalAddress_transpose 64 x⟩

/-- Compute the idle child's headers, then run its exchange on the same owner.
The arithmetic bank takes the binary width, spectator count and fixed interval length. -/
theorem remainderPrepared_runs [M8.Machine.Net] {t w W : ℕ}
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (hw : 0 < w) (hW : 0 < W)
    (caller : Tapes t prime) (src : Fin t)
    (x : Fin (volume prime (phaseIntervalChild e.1 e.2 w W 64)) → ZMod 2)
    (payload : caller.tape src = sourceWord x) (head : caller.head src = 0) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
    let headers := fun i => Fin.castAdd t (phaseHeaderSlots i)
    let site := Fin.natAdd 24 src
    let setup := M8.Machine.ArbitraryWidthOriginalRun.extendBanks
      (extend (extend (extend (phaseHeaderProgram e.1 e.2 64) t) 16) 19)
    ∃ y : Fin (volume prime child) → ZMod 2,
      HoareTime (seq setup (program headers site))
        (fun z => z = input ((phaseHeaderInput e.1 e.2 w W).append caller))
        (fun z => z = input (SharedPlacementAlphabet.setTape
          ((phaseHeaderOutput e.1 e.2 w W 64).append caller) site (sourceWord y) 0))
        ((2*(24*64+333)+250)*((prime^w)^128*W) + 1 + cost child hs) ∧
      y = Shared50RecursiveNodeRows.transpose (one_dvd _) x ∧
      ∀ a b h d u v j,
        y (RecursiveInterchangeScaling.index (intervalAddress 64 a b d h u v j)) =
        x (RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v j)) := by
  intro child hs headers site setup
  obtain ⟨ordered, fits, _⟩ := BitHosting.remainder_counts e he
  obtain ⟨build, valid, slots⟩ := intervalHeader_runs (by decide : 0 < 64) ordered
    (show e.2 ≤ 64 by omega) hw hW
  let output := phaseHeaderOutput e.1 e.2 w W 64
  obtain ⟨y, move, action⟩ := remainderInterval_runs e hW (output.append caller) headers site hs valid
    (fun i => by simpa [headers,Tapes.append,output] using (slots i).2)
    (fun i => by simpa [headers,Tapes.append,output] using (slots i).1)
    x (by simpa [site,Tapes.append] using payload) (by simpa [site,Tapes.append] using head)
  have prepare := M8.Machine.ArbitraryWidthOriginalRun.extend_banks_hoare
    (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq build caller)
      (FixedHeaderBankCopy.empty 16)) M8.Machine.ArbitraryWidthHighPrepareShared.privateInput)
  exact ⟨y, prepare.seq move, action⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
