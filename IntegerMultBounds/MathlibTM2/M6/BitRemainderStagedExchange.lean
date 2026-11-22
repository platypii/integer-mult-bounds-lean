module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderInputRotation
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderReturnCounters

/-! Read the ordinary port exchange on the compact staging owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Swap.Modular FlatCoordinateLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Insert the inherited block between the 16 active coordinates and the
remaining 112 coordinates with their spectator. -/
def stagedOwnerIndex {M B W : ℕ} (b : Fin B) (j : Fin (M^128*W)) : Fin (M^16*(B*(M^112*W))) :=
  let cell := finProdFinEquiv.symm (j.cast (ordinaryCompact_width M W).symm)
  finProdFinEquiv (cell.1,finProdFinEquiv (b,cell.2))

private theorem stagedRowRead {M B N W : ℕ} (g : Fin N)
    (owner : Fin ((B*N)*(M^128*W)) → ZMod 2) (staged : Fin (M^16*(B*(M^112*W))) → ZMod 2)
    (cells : ∀ a b k, staged (finProdFinEquiv (a,finProdFinEquiv (b,k))) =
      owner (finProdFinEquiv (finProdFinEquiv (b,g),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) :
    ∀ b j, staged (stagedOwnerIndex b j) = owner (finProdFinEquiv (finProdFinEquiv (b,g),j)) := by
  intro b j
  simpa only [stagedOwnerIndex,Prod.mk.eta,Equiv.apply_symm_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using
    cells (finProdFinEquiv.symm (j.cast (ordinaryCompact_width M W).symm)).1 b
      (finProdFinEquiv.symm (j.cast (ordinaryCompact_width M W).symm)).2

/-- Read any live label directly from a pair of staged owner words. Other
rows may carry independent data. -/
theorem OriginalPortReads.stagedLabelExchange {w W B : ℕ} {interval parent c} :
    let M := prime^(w+1)
    let N := M^(64*64)
    ∀ (label : LabelPadding.Label 64 (w+1)), IsUnit label →
    let g := LabelAddress.address label
    ∀ (input output : Fin ((B*N)*(M^128*W)) → ZMod 2)
      (src dst : Fin (M^16*(B*(M^112*W))) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output → (∀ i, IsUnit (parent i)) →
      (∀ a b k, input (finProdFinEquiv (finProdFinEquiv (b,g),
        (finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W))) =
        src (finProdFinEquiv (a,finProdFinEquiv (b,k)))) →
      (∀ a b k, dst (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
        (finProdFinEquiv (b,g),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) →
      let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := fromBlocks (diagonal parent*label) 0 0 (M8.ReversedExchange.rev 64*label)
      let address := fun b x (k : Fin W) => stagedOwnerIndex b (index ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b x k, dst (address b ((fromBlocks (1-P) P P (1-P)).mulVec x) k) = src (address b x k) := by
  intro M N label live g input output src dst reads units incoming outgoing P frame address b x k
  have entry := stagedRowRead g input src (fun a b j => (incoming a b j).symm)
  have exitRow := stagedRowRead g output dst outgoing
  dsimp only [address]
  rw [exitRow,entry]
  have exchange := reads.exchange units b label live rfl x k
  simpa only [Matrix.mul_one,Fin.cast_refl,id_eq] using exchange

private theorem OriginalPortReads.singularCell {w W B : ℕ} {interval parent c} :
    let M := prime^(w+1)
    let N := M^(64*64)
    ∀ {input output : Fin ((B*N)*(M^128*W)) → ZMod 2},
      OriginalPortReads _ W B interval parent c input output →
      ∀ (label : LabelPadding.Label 64 (w+1)), ¬ IsUnit label →
      let g := LabelAddress.address label
      ∀ (b : Fin B) j, output (finProdFinEquiv (finProdFinEquiv (b,g),j)) =
        input (finProdFinEquiv (finProdFinEquiv (b,g),j)) := by
  intro M N input output reads label singular g b j
  let row : Fin (B*N) := finProdFinEquiv (b,g)
  have number : row.val = b.val*M^(64*64)+g.val := by
    simp [row,N,M,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have same := congrFun ((reads b label).2 singular) j
  rw [← number] at same
  simp only [ownerRow,dite_eq_left row.isLt] at same
  exact same

/-- A singular label retains every cell of its staged owner word. -/
theorem OriginalPortReads.stagedSingularRow {w W B : ℕ} {interval parent c} :
    let M := prime^(w+1)
    let N := M^(64*64)
    ∀ (label : LabelPadding.Label 64 (w+1)), ¬ IsUnit label →
    let g := LabelAddress.address label
    ∀ (input output : Fin ((B*N)*(M^128*W)) → ZMod 2)
      (src dst : Fin (M^16*(B*(M^112*W))) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output →
      (∀ a b k, src (finProdFinEquiv (a,finProdFinEquiv (b,k))) = input (finProdFinEquiv
        (finProdFinEquiv (b,g),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) →
      (∀ a b k, dst (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
        (finProdFinEquiv (b,g),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) →
      ∀ b j, dst (stagedOwnerIndex b j) = src (stagedOwnerIndex b j) := by
  intro M N label singular g input output src dst reads incoming outgoing b j
  rw [stagedRowRead g output dst outgoing,stagedRowRead g input src incoming]
  exact reads.singularCell label singular b j

/-- On a retained row, entry and return charts implement a requested address
map for arbitrary bits exactly when the two physical addresses agree. -/
theorem retainedRow_exchange_iff {ι κ : Type*} (entry exitRow : ι → κ) (exchange : ι → ι) :
    (∀ (row : κ → ZMod 2) (x : ι), row (exitRow (exchange x)) = row (entry x)) ↔
      ∀ x, exitRow (exchange x) = entry x := by
  classical
  constructor
  · intro reads x
    by_contra different
    have h := reads (fun j => if j = entry x then 1 else 0) x
    simp [different] at h
  · intro addresses row x
    rw [addresses]

/-- For a permutation, the exit chart of a retained row is uniquely
determined by its entry chart and the inverse of the desired exchange. -/
theorem retainedRow_exit_iff {ι κ : Type*} (entry exitRow : ι → κ) (exchange : ι ≃ ι) :
    (∀ (row : κ → ZMod 2) (x : ι), row (exitRow (exchange x)) = row (entry x)) ↔
      exitRow = entry ∘ exchange.symm := by
  rw [retainedRow_exchange_iff]
  constructor
  · intro addresses
    funext y
    simpa using addresses (exchange.symm y)
  · rintro rfl x
    simp

/-- Entry and return transpose use inverse physical offsets. At a singular
label the complete round trip therefore fixes each parent-order cell. -/
theorem OriginalPortReads.parentSingularRow {w W B : ℕ} {interval parent c} :
    let M := prime^(w+1)
    let N := M^(64*64)
    ∀ (label : LabelPadding.Label 64 (w+1)), ¬ IsUnit label →
    let g := LabelAddress.address label
    ∀ (input output : Fin ((B*N)*(M^128*W)) → ZMod 2)
      (src dst : Fin (M^128*((B*N)*W)) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output →
      (∀ a (b : Fin B) k, input (finProdFinEquiv (finProdFinEquiv (b,g),finProdFinEquiv (a,k))) =
        src (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,g),k)))) →
      (∀ a (b : Fin B) k, dst (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,g),k))) =
        output (finProdFinEquiv (finProdFinEquiv (b,g),finProdFinEquiv (a,k)))) →
      ∀ a (b : Fin B) k, dst (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,g),k))) =
        src (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,g),k))) := by
  intro M N label singular g input output src dst reads incoming outgoing a b k
  rw [outgoing, ← incoming]
  exact reads.singularCell label singular b (finProdFinEquiv (a,k))

theorem OriginalPortReads.stagedExchange {w W B : ℕ} {interval parent c} :
    let M := prime^(w+1)
    let N := M^(64*64)
    let g := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    ∀ (input output : Fin ((B*N)*(M^128*W)) → ZMod 2)
      (src dst : Fin (M^16*(B*(M^112*W))) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output → (∀ i, IsUnit (parent i)) →
      (∀ b j a k, input (finProdFinEquiv (finProdFinEquiv (b,j),
        (finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W))) =
        if j = g then src (finProdFinEquiv (a,finProdFinEquiv (b,k))) else 0) →
      (∀ a b k, dst (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
        (finProdFinEquiv (b,g),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) →
      let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let address := fun b x (k : Fin W) => stagedOwnerIndex b (index ((frame.mulVec x) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b x k, dst (address b ((fromBlocks (1-P) P P (1-P)).mulVec x) k) = src (address b x k) := by
  intro M N g input output src dst reads units incoming outgoing P frame address b x k
  simpa only [Matrix.mul_one] using
      OriginalPortReads.stagedLabelExchange (1 : LabelPadding.Label 64 (w+1)) isUnit_one input output src dst
        reads units (fun a b j => by simpa using incoming b g a j) outgoing b x k

open RecursiveInterchangeLayout (Descriptor volume role)

/-- The scanner sees one directory record family per inherited block.
All spectators of the staged payload form its trailing word. -/
noncomputable def stagedScannerLayout (w B W : ℕ) : Descriptor :=
  ⟨1,142080,B*(prime^(w+1))^(64*64),64*(w+1),1,W⟩

theorem stagedScanner_shape (w B W : ℕ) :
    (stagedScannerLayout w B W).beforeH = B*prime^(64*((w+1)*64)) := by
  change B*(prime^(w+1))^(64*64) = _
  rw [← pow_mul,show (w+1)*(64*64) = 64*((w+1)*64) by omega]

theorem stagedScanner_volume (w B W : ℕ) :
    let M := prime^(w+1)
    volume prime (role (stagedScannerLayout w B W) 142080) = B*(M^(64*64)*(M^128*W)) := by
  intro M
  change 1*(142080/142080)*(B*M^(64*64))*prime^(64*(w+1))*1*prime^(64*(w+1))*W = _
  rw [show prime^(64*(w+1)) = M^64 by dsimp [M]; rw [← pow_mul,Nat.mul_comm 64]]
  rw [show M^128 = M^64*M^64 from pow_add M 64 64]
  simp only [Nat.reduceDiv,Nat.one_mul,Nat.mul_one]
  ac_rfl

theorem stagedScanner_reads {w B W : ℕ} {interval parent c} :
    let layout := stagedScannerLayout w B W
    let R := LabelMask.records (role layout 142080)
    let M := prime^(w+1)
    ∀ (input output : Fin (R*(M^128*(layout.between*layout.afterD))) → ZMod 2),
    OriginalPortReads R (layout.between*layout.afterD) (layout.beforeRows*1*B)
      interval parent c input output →
    ∃ src dst : Fin ((B*M^(64*64))*(M^128*W)) → ZMod 2,
      List.ofFn src = List.ofFn input ∧ List.ofFn dst = List.ofFn output ∧
      OriginalPortReads (B*M^(64*64)) W B interval parent c src dst := by
  intro layout R M input output reads
  have r : R = B*M^(64*64) := by
    simp [R,layout,stagedScannerLayout,LabelMask.records,role,M]
  have width : layout.between*layout.afterD = W := Nat.one_mul _
  have blocks : layout.beforeRows*1*B = B := Nat.one_mul _
  generalize layout.between*layout.afterD = K at input output reads width
  rw [blocks] at reads
  subst K
  revert input output
  rw [r]
  intro input output reads
  exact ⟨input,output,rfl,rfl,reads⟩

open Cover.Fallback M8.RevMachine IntegerMultBounds.MathlibTM2.Fast.Main Stack Host

/-- Install the scheduled scanner at the descriptor shared by the forward
and return handoffs, with exactly one parent prefix per inherited block. -/
theorem stagedOrdinaryParent_exec [M8.Machine.Net] {common work : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ T, ∃ localBody : Unit → Pr Unit (66+(common+24+31+(work+T))) columnCapacity prime U,
    ∃ C : ℝ, ∃ overhead : ℕ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      let layout := stagedScannerLayout w B W
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ i, IsUnit (parent i)) →
        (root = true → ∀ i, parent i = 1) → ∀ (prefixWidth : ℕ) (prefixes : ℕ → List (Fin (prime+4))),
        (∀ i < B, (prefixes i).length = prefixWidth) → prefixWidth ≤ prime^layout.width →
        OrdinaryParentRoundTrip (common := common) (work := work+T) (rows := 1) (B := B) interval layout
          root parent (by omega) (fits.trans (by omega)) (pool.trans (by omega)) (by omega) (pairRoom.trans (by omega)) overhead C localBody prefixWidth prefixes := by
  obtain ⟨T,body,C,overhead,run⟩ := scheduledOrdinaryParent_exec (U := U) interval member space pool room fits pairRoom
  refine ⟨T,body,C,overhead,?_⟩
  intro w B W hb hw layout root parent units unitRoot prefixWidth prefixes sizes cap
  have pos : layout.Positive :=
    ⟨Nat.zero_lt_one,(by decide : 0 < 142080),Nat.mul_pos hb (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _),Nat.zero_lt_one,hw⟩
  intro k src c hc
  exact run layout w 1 B pos rfl rfl (stagedScanner_shape w B W) root parent units unitRoot
    prefixWidth prefixes (fun i hi => sizes i (by simpa [layout,stagedScannerLayout] using hi)) cap (k := k) src c hc

end IntegerMultBounds.MathlibTM2.M6.BitNode
