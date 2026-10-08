import IntegerMultBounds.Machine.ScalingControl

/-! Pure sequential merge semantics for positive unit scaling. Source streams
are contiguous intervals, consumed only at their heads. The finite selector's
prefix counts recover precisely the inverse-scaled source address. No tape
implementation or running-time claim is made here. -/

namespace IntegerMultBounds.Machine.ScalingMergeData

open ScalingPieces ScalingControl

/-- Number of blocks consumed from stream j before output z. -/
def popCount {c : ℕ} (hc : 0 < c) (Q z j : ℕ) : ℕ :=
  ((Finset.range z).filter (fun w => (select hc Q w).val = j)).card

/-- Earlier outputs selecting a piece correspond to the initial segment of
that piece before the current reconstructed source. -/
theorem previous_count {Q c z j : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) (hj : AdmissiblePiece Q c z j) :
    popCount hc Q z j = restore Q c z j - boundary Q c j := by
  have hrQ := restore_lt hc hz hj
  have hrj := piece_restore hQ hz hj
  have hrI := (piece_interval hQ hc hrQ).mp hrj
  have hcard : (Finset.Ico (boundary Q c j) (restore Q c z j)).card =
      ((Finset.range z).filter (fun w => (select hc Q w).val = j)).card := by
    apply Finset.card_bij (fun y _ => output Q c y)
    · intro y hy
      obtain ⟨hyl,hyr⟩ := Finset.mem_Ico.mp hy
      have hyQ : y < Q := lt_trans hyr hrQ
      have hyj : piece Q c y = j :=
        (piece_interval hQ hc hyQ).mpr ⟨hyl,lt_trans hyr hrI.2⟩
      have hyz : output Q c y < z := by
        rw [← output_restore hz hj]
        exact (output_lt_iff hc (hyj.trans hrj.symm)).mpr hyr
      have hsel := select_unique hQ hc hcop (output_lt hQ (c := c) (y := y))
        (source_piece hQ hc hyQ)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyz, hsel.symm.trans hyj⟩
    · intro x hx y hy hxy
      exact output_injective hcop
        (lt_trans (Finset.mem_Ico.mp hx).2 hrQ)
        (lt_trans (Finset.mem_Ico.mp hy).2 hrQ) hxy
    · intro w hw
      obtain ⟨hwz,hwj⟩ := Finset.mem_filter.mp hw
      have hwz := Finset.mem_range.mp hwz
      have hwQ : w < Q := lt_trans hwz hz
      have hwA : AdmissiblePiece Q c w j := by
        rw [← hwj]
        exact select_admissible hc hcop w
      have hwI := (piece_interval hQ hc (restore_lt hc hwQ hwA)).mp
        (piece_restore hQ hwQ hwA)
      refine ⟨restore Q c w j,Finset.mem_Ico.mpr ⟨hwI.1,?_⟩,output_restore hwQ hwA⟩
      exact (restore_lt_iff hc hwA hj).mpr hwz
  simpa only [Nat.card_Ico,popCount] using hcard.symm

/-- The next unread offset in the selected stream is exactly the inverse
source address. This is the head-consumption invariant of the merge. -/
theorem selected_offset {Q c z : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) :
    let j := (select hc Q z).val
    restore Q c z j = boundary Q c j + popCount hc Q z j := by
  dsimp only
  have hj := select_admissible hc hcop z
  rw [previous_count hQ hc hcop hz hj]
  have hi := (piece_interval hQ hc (restore_lt hc hz hj)).mp (piece_restore hQ hz hj)
  omega

/-- The selected stream always has an unread block. -/
theorem selected_not_exhausted {Q c z : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) :
    let j := (select hc Q z).val
    popCount hc Q z j < boundary Q c (j + 1) - boundary Q c j := by
  dsimp only
  have hj := select_admissible hc hcop z
  have hi := (piece_interval hQ hc (restore_lt hc hz hj)).mp (piece_restore hQ hz hj)
  have ho := selected_offset hQ hc hcop hz
  dsimp only at ho
  omega

/-- Every source stream is fully consumed after all Q outputs. -/
theorem complete_count {Q c j : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) :
    popCount hc Q Q j = boundary Q c (j + 1) - boundary Q c j := by
  have hcard : (Finset.Ico (boundary Q c j) (boundary Q c (j + 1))).card =
      ((Finset.range Q).filter (fun w => (select hc Q w).val = j)).card := by
    apply Finset.card_bij (fun y _ => output Q c y)
    · intro y hy
      have hyI := Finset.mem_Ico.mp hy
      have hyQ : y < Q := lt_of_lt_of_le hyI.2 (boundary_le Q c (j + 1))
      have hyj := (piece_interval hQ hc hyQ).mpr hyI
      have hsel := select_unique hQ hc hcop (output_lt hQ (c := c) (y := y))
        (source_piece hQ hc hyQ)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (output_lt hQ),hsel.symm.trans hyj⟩
    · intro x hx y hy hxy
      exact output_injective hcop
        (lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 (boundary_le Q c (j + 1)))
        (lt_of_lt_of_le (Finset.mem_Ico.mp hy).2 (boundary_le Q c (j + 1))) hxy
    · intro w hw
      obtain ⟨hwQ,hwj⟩ := Finset.mem_filter.mp hw
      have hwQ := Finset.mem_range.mp hwQ
      have hwA : AdmissiblePiece Q c w j := by
        rw [← hwj]
        exact select_admissible hc hcop w
      exact ⟨restore Q c w j,
        Finset.mem_Ico.mpr ((piece_interval hQ hc (restore_lt hc hwQ hwA)).mp
          (piece_restore hQ hwQ hwA)),output_restore hwQ hwA⟩
  simpa only [Nat.card_Ico,popCount] using hcard.symm

/-- One merge step increments exactly the selected stream's cursor. -/
theorem popCount_succ {c : ℕ} (hc : 0 < c) (Q z j : ℕ) :
    popCount hc Q (z + 1) j =
      popCount hc Q z j + if (select hc Q z).val = j then 1 else 0 := by
  classical
  simp only [popCount,Finset.range_add_one,Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

/-- The initial contents of one stream, in original source order. The payload
can itself be a list, so this operation does not change internal block order. -/
def blocks {α : Type*} (Q c j : ℕ) (payload : ℕ → α) : List α :=
  (List.range' (boundary Q c j) (boundary Q c (j + 1) - boundary Q c j)).map payload

/-- Unconsumed suffixes after the first z output choices. -/
def remaining {α : Type*} {c : ℕ} (hc : 0 < c) (Q z : ℕ)
    (payload : ℕ → α) (j : ℕ) : List α :=
  (blocks Q c j payload).drop (popCount hc Q z j)

/-- Looking at the selected stream's head returns the correct whole block. -/
theorem selected_head {α : Type*} {Q c z : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) (payload : ℕ → α) :
    let j := (select hc Q z).val
    (remaining hc Q z payload j).head? = some (payload (restore Q c z j)) := by
  dsimp only
  rw [remaining,List.head?_drop,blocks,List.getElem?_map,
    List.getElem?_range' (selected_not_exhausted hQ hc hcop hz)]
  simp only [one_mul,Option.map_some]
  rw [← selected_offset hQ hc hcop hz]

/-- Popping the selected head changes exactly the corresponding suffix. -/
theorem remaining_step {α : Type*} {c : ℕ} (hc : 0 < c) (Q z : ℕ)
    (payload : ℕ → α) :
    Function.update (remaining hc Q z payload) (select hc Q z).val
      ((remaining hc Q z payload (select hc Q z).val).tail) =
      remaining hc Q (z + 1) payload := by
  funext j
  by_cases hj : (select hc Q z).val = j
  · subst j
    simp only [Function.update_self,remaining,popCount_succ,ite_true]
    simp [List.tail_drop]
  · simp only [Function.update_of_ne (Ne.symm hj),remaining,popCount_succ,ite_eq_right hj,
      Nat.add_zero]

/-- No source blocks remain after the complete merge, even for empty pieces. -/
theorem remaining_complete {α : Type*} {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (payload : ℕ → α) (j : ℕ) :
    remaining hc Q Q payload j = [] := by
  rw [remaining,complete_count hQ hc hcop]
  have hlen : (blocks Q c j payload).length =
      boundary Q c (j + 1) - boundary Q c j := by
    simp [blocks]
  rw [← hlen,List.drop_length]

/-- In forward coordinates the destination selected by multiplication
contains exactly the original source payload. -/
theorem restored_output {Q c y : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hy : y < Q) :
    restore Q c (output Q c y) (select hc Q (output Q c y)).val = y := by
  rw [← select_unique hQ hc hcop (output_lt hQ) (source_piece hQ hc hy)]
  exact restore_output hc y

/-- A literal sequential list merge: read and remove one selected head, then
recurse to the next output. Failure represents reading an exhausted stream. -/
def merge {α : Type*} {c : ℕ} (hc : 0 < c) (Q : ℕ) :
    ℕ → ℕ → (ℕ → List α) → Option (List α)
  | _,0,_ => some []
  | z,n + 1,streams => do
    let j := (select hc Q z).val
    let a ← (streams j).head?
    let rest ← merge hc Q (z + 1) n (Function.update streams j (streams j).tail)
    pure (a :: rest)

/-- Every prefix-state merge succeeds and outputs the inverse-scaled blocks
in increasing destination order. -/
theorem merge_remaining {α : Type*} {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (payload : ℕ → α) (n z : ℕ) (hbound : z + n ≤ Q) :
    merge hc Q z n (remaining hc Q z payload) =
      some ((List.range' z n).map
        (fun w => payload (restore Q c w (select hc Q w).val))) := by
  induction n generalizing z with
  | zero => simp [merge]
  | succ n ih =>
    have hz : z < Q := by omega
    simp only [merge,selected_head hQ hc hcop hz,remaining_step]
    rw [ih (z + 1) (by omega)]
    simp [List.range'_succ]

/-- End-to-end pure merge correctness, starting with the contiguous source
streams. Whole payload values are returned unchanged. -/
theorem merge_blocks {α : Type*} {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (payload : ℕ → α) :
    merge hc Q 0 Q (fun j => blocks Q c j payload) =
      some ((List.range Q).map
        (fun z => payload (restore Q c z (select hc Q z).val))) := by
  have hh := merge_remaining hQ hc hcop payload Q 0 (by omega)
  have hzero : remaining hc Q 0 payload = fun j => blocks Q c j payload := by
    funext j
    simp [remaining,popCount]
  rw [hzero] at hh
  simpa only [List.range_eq_range'] using hh

end IntegerMultBounds.Machine.ScalingMergeData
