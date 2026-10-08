import IntegerMultBounds.Machine.ScalingMerge
import IntegerMultBounds.Machine.Dispatch
import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.OneHot
import IntegerMultBounds.Machine.FiberShift

/-! Literal inverse scaling scatter. Read a single source sequentially and append
whole blocks to the selected fixed buffer. Every copy, dispatch and residue
advance is physically executed and charged. -/

namespace IntegerMultBounds.Machine.ScalingScatter

open Placement (ExactRun exact_seq)
open CountedCopyReuse (empty binary)

/-- Source, one spare slot, mutable block clock, immutable block descriptor,
then the c destination buffers. A fixed swap selects the destination. -/
def core {c : ℕ} (buffers : Tapes c 0) (source : ℤ → Fin 4) (q : ℤ)
    (bs : List Bool) : Tapes (4+c) 0 :=
  (CountedCopyReuse.bank source empty empty (binary bs) q 0 1 1).append buffers

def copyPlacement {c : ℕ} (j : Fin c) : Fin (4+c) ≃ Fin (4+c) :=
  Equiv.swap (Fin.castAdd c (1 : Fin 4)) (Fin.natAdd 4 j)

def copyProgram {c : ℕ} (j : Fin c) : Program (4+c) 16 0 :=
  Placement.placed CountedCopyReuse.program (copyPlacement j)

@[simp] private theorem slots_ne {c : ℕ} (i : Fin 4) (j : Fin c) :
    Fin.castAdd c i ≠ Fin.natAdd 4 j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  omega

@[simp] private theorem slots_ne' {c : ℕ} (i : Fin 4) (j : Fin c) :
    Fin.natAdd 4 j ≠ Fin.castAdd c i := Ne.symm (slots_ne i j)

private theorem swap_control {c : ℕ} (j : Fin c) (i : Fin 4) (hi : i ≠ 1) :
    copyPlacement j (Fin.castAdd c i) = Fin.castAdd c i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hi (Fin.castAdd_inj.mp h)
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    omega

private theorem active_core {c : ℕ} (buffers : Tapes c 0) (source : ℤ → Fin 4)
    (q : ℤ) (bs : List Bool) (j : Fin c) :
    Placement.active (copyPlacement j) (core buffers source q bs) =
      CountedCopyReuse.bank source (buffers.tape j) empty (binary bs)
        q (buffers.head j) 1 1 := by
  unfold Placement.active core
  congr 1
  · funext i
    fin_cases i
    · simp [swap_control j 0 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [copyPlacement,Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 2 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 3 (by decide),Tapes.append,CountedCopyReuse.bank]
  · funext i
    fin_cases i
    · simp [swap_control j 0 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [copyPlacement,Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 2 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 3 (by decide),Tapes.append,CountedCopyReuse.bank]

/-- Append one block to the selected buffer and advance its head. -/
def appendBuffer {c : ℕ} (buffers : Tapes c 0) (j : Fin c) (xs : List (Fin 4)) : Tapes c 0 :=
  ⟨Function.update buffers.head j (buffers.head j+xs.length),
   Function.update buffers.tape j (putWord (buffers.tape j) (buffers.head j) xs)⟩

private theorem replace_core {c : ℕ} (buffers : Tapes c 0) (source : ℤ → Fin 4)
    (q : ℤ) (bs : List Bool) (j : Fin c) (xs : List (Fin 4)) :
    Placement.replace (copyPlacement j) (core buffers source q bs)
      (CountedCopyReuse.bank source (putWord (buffers.tape j) (buffers.head j) xs) empty (binary bs)
        (q+xs.length) (buffers.head j+xs.length) 1 1) =
      core (appendBuffer buffers j xs) source (q+xs.length) bs := by
  unfold Placement.replace Placement.combine Placement.extra core copyPlacement
    Tapes.reindex Tapes.append CountedCopyReuse.bank appendBuffer
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i => fin_cases i <;> simp [Equiv.swap_apply_def]
    | right i =>
      by_cases hi : i = j
      · subst i; simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def,hi]
  · funext i
    induction i using Fin.addCases with
    | left i => fin_cases i <;> simp [Equiv.swap_apply_def]
    | right i =>
      by_cases hi : i = j
      · subst i; simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def,hi]

/-- Actual placed counted copy, preserving every source cell and all other
buffers, and restoring the mutable block clock. -/
theorem copy_exact {c : ℕ} (buffers : Tapes c 0) (source : ℤ → Fin 4)
    (q : ℤ) (bs : List Bool) (j : Fin c) (xs : List (Fin 4))
    (hcount : Counter.value bs = xs.length)
    (hsource : putWord source q xs = source) :
    ExactRun (copyProgram j) (CountedCopyReuse.runtime xs.length bs)
      (core buffers source q bs)
      (core (appendBuffer buffers j xs) source (q+xs.length) bs) := by
  have hh := CountedCopyReuse.copy_exact source (buffers.tape j) q (buffers.head j) xs bs hcount
  rw [hsource] at hh
  change ExactRun CountedCopyReuse.program _ _ _ at hh
  rw [← active_core buffers source q bs j] at hh
  simpa only [copyProgram,replace_core] using
    Placement.placed_exact CountedCopyReuse.program (copyPlacement j) (core buffers source q bs) _ hh

/-- The modulus and current residue occupy two fixed one-hot control banks. -/
def bank {c : ℕ} (buffers : Tapes c 0) (source : ℤ → Fin 4) (q : ℤ)
    (bs : List Bool) (modulus current : Tapes c 0) (m z : Fin c) : Tapes (4+c+c+c) 0 :=
  ((core buffers source q bs).append (OneHot.bank modulus m)).append (OneHot.bank current z)

def family {c : ℕ} (j : Fin c) : Program (4+c+c+c) 16 0 :=
  extend (extend (copyProgram j) c) c

/-- Only scanned control cells enter this fixed finite lookup table. -/
def selector {c : ℕ} (hc : 0 < c) (symbols : Fin (4+c+c+c) → Fin 4) : Fin c :=
  ScalingControl.table hc
    (OneHot.decode hc (fun i => symbols (Fin.castAdd c (Fin.natAdd (4+c) i))))
    (OneHot.decode hc (fun i => symbols (Fin.natAdd (4+c+c) i)))

theorem selector_bank {c : ℕ} (hc : 0 < c) (buffers : Tapes c 0)
    (source : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (modulus current : Tapes c 0) (m z : Fin c) :
    selector hc (bank buffers source q bs modulus current m z).reads = ScalingControl.table hc m z := by
  simp [selector,bank,Tapes.reads,Tapes.append,OneHot.decode_symbol]

def advanceProgram {c : ℕ} (hc : 0 < c) : Program (4+c+c+c) 2 0 :=
  Placement.placed (OneHot.program hc) (finAddFlip : Fin (c+(4+c+c)) ≃ Fin (4+c+c+c))

/-- Copy a whole source block to the selected buffer, then advance its residue. -/
def body {c : ℕ} (hc : 0 < c) : Program (4+c+c+c) (c*16+1+2) 0 :=
  seq (Dispatch.program hc family (selector hc)) (advanceProgram hc)

private theorem exact_extend {t q u : ℕ} {M : Program t q 0} {n : ℕ}
    {v w : Tapes t 0} (frame : Tapes u 0) (h : ExactRun M n v w) :
    ExactRun (extend M u) n (v.append frame) (w.append frame) := by
  obtain ⟨last,hr,hh,hfinal⟩ := h
  refine ⟨last.extend frame,extend_run M frame hr,extend_halt M frame hh,?_⟩
  change last.tapes.append frame = _
  rw [hfinal]

private theorem advance_exact {c : ℕ} (hc : 0 < c) (v : Tapes (4+c+c) 0)
    (current : Tapes c 0) (z : Fin c) :
    ExactRun (advanceProgram hc) 1 (v.append (OneHot.bank current z))
      (v.append (OneHot.bank current (OneHot.next hc z))) := by
  let e : Fin (c+(4+c+c)) ≃ Fin (4+c+c+c) := finAddFlip
  have ha : Placement.active e (v.append (OneHot.bank current z)) = OneHot.bank current z := by
    unfold Placement.active e
    simp [Tapes.append,finAddFlip_apply_castAdd,OneHot.bank]
  obtain ⟨hr,hh⟩ := OneHot.advance_exact hc current z
  have hx : ExactRun (OneHot.program hc) 1 (OneHot.bank current z)
      (OneHot.bank current (OneHot.next hc z)) := ⟨_,hr,hh,rfl⟩
  rw [← ha] at hx
  have hh := Placement.placed_exact (OneHot.program hc) e _ _ hx
  have hr : Placement.replace e (v.append (OneHot.bank current z))
      (OneHot.bank current (OneHot.next hc z)) =
      v.append (OneHot.bank current (OneHot.next hc z)) := by
    have hframe : Placement.extra e (v.append (OneHot.bank current z)) = v := by
      cases v
      simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
    rw [Placement.replace,hframe]
    have hactive : Placement.active e (v.append (OneHot.bank current (OneHot.next hc z))) =
        OneHot.bank current (OneHot.next hc z) := by
      simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd,OneHot.bank]
    have hextra : Placement.extra e (v.append (OneHot.bank current (OneHot.next hc z))) = v := by
      cases v
      simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
    simpa only [hactive,hextra] using
      Placement.view e (v.append (OneHot.bank current (OneHot.next hc z)))
  simpa only [advanceProgram,e,hr] using hh

/-- Exact literal body execution: one dispatch, one real join, one residue
advance, and the full reusable-copy runtime. The modulus stays unchanged. -/
theorem body_exact {c : ℕ} (hc : 0 < c) (buffers : Tapes c 0)
    (source : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (modulus current : Tapes c 0)
    (m z : Fin c) (xs : List (Fin 4)) (hcount : Counter.value bs = xs.length)
    (hsource : putWord source q xs = source) :
    let j := ScalingControl.table hc m z
    ExactRun (body hc) (CountedCopyReuse.runtime xs.length bs+3)
      (bank buffers source q bs modulus current m z)
      (bank (appendBuffer buffers j xs) source (q+xs.length)
        bs modulus current m (OneHot.next hc z)) := by
  dsimp only at hsource ⊢
  let j := ScalingControl.table hc m z
  have hcopy := exact_extend (OneHot.bank current z)
    (exact_extend (OneHot.bank modulus m) (copy_exact buffers source q bs j xs hcount hsource))
  obtain ⟨last,hr,hh,hfinal⟩ := hcopy
  have hdispatch : ExactRun (Dispatch.program hc family (selector hc))
      (1+CountedCopyReuse.runtime xs.length bs)
      (bank buffers source q bs modulus current m z)
      (bank (appendBuffer buffers j xs) source (q+xs.length)
        bs modulus current m z) := by
    exact ⟨last.mapState (Dispatch.tag j),
      Dispatch.run_selected hc family (selector hc) _ j
        (selector_bank hc buffers source q bs modulus current m z) hr,
      Dispatch.halt_selected hc family (selector hc) j hh,hfinal⟩
  have hadvance := advance_exact hc
    ((core (appendBuffer buffers j xs) source (q+xs.length) bs).append
      (OneHot.bank modulus m)) current z
  have hboth := exact_seq hdispatch hadvance
  simpa only [body,bank,j,show 1+CountedCopyReuse.runtime xs.length bs+1+1 =
    CountedCopyReuse.runtime xs.length bs+3 by omega] using hboth

/-- Uniform body bound independent of the stream index and input modulus. -/
theorem body_hoare {c : ℕ} (hc : 0 < c) (buffers : Tapes c 0)
    (source : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (modulus current : Tapes c 0)
    (m z : Fin c) (xs : List (Fin 4)) (hcount : Counter.value bs = xs.length)
    (hsource : putWord source q xs = source) :
    let j := ScalingControl.table hc m z
    HoareTime (body hc)
      (fun v => v = bank buffers source q bs modulus current m z)
      (fun v => v = bank (appendBuffer buffers j xs) source
        (q+xs.length) bs modulus current m (OneHot.next hc z))
      (5*xs.length+7*bs.length+19) := by
  dsimp only
  rintro v rfl
  obtain ⟨last,hr,hh,hfinal⟩ := body_exact hc buffers source q bs modulus current m z xs hcount hsource
  have htime := CountedCopyReuse.runtime_le_linear xs bs hcount
  exact ⟨_,last,by omega,hr,hh,hfinal⟩

/-- Desired buffers contain successive source addresses multiplied by c. -/
def targetBlocks (Q c j : ℕ) (payload : ℕ → List (Fin 4)) : List (List (Fin 4)) :=
  ScalingMergeData.blocks Q c j (fun y => payload (ScalingPieces.output Q c y))

def bufferPrefix {c : ℕ} (hc : 0 < c) (Q z j : ℕ)
    (payload : ℕ → List (Fin 4)) : List (Fin 4) :=
  ((targetBlocks Q c j payload).take (ScalingMergeData.popCount hc Q z j)).flatten

private theorem count_le {Q c z : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hz : z ≤ Q) (j : ℕ) :
    ScalingMergeData.popCount hc Q z j ≤
      ScalingControl.boundary Q c (j+1)-ScalingControl.boundary Q c j := by
  rw [← ScalingMergeData.complete_count hQ hc hcop]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hw,hj⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hw) hz),hj⟩

private theorem prefix_length {Q c z B : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z ≤ Q) (j : ℕ) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) :
    (bufferPrefix hc Q z j payload).length = ScalingMergeData.popCount hc Q z j*B := by
  have hu : BlockRotationData.Uniform B
      ((targetBlocks Q c j payload).take (ScalingMergeData.popCount hc Q z j)) := by
    intro block hb
    have hm := List.mem_of_mem_take hb
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
    exact hwidth _
  rw [bufferPrefix,BlockRotationData.uniform_volume B _ hu,List.length_take]
  have hl : (targetBlocks Q c j payload).length =
      ScalingControl.boundary Q c (j+1)-ScalingControl.boundary Q c j := by
    simp [targetBlocks,ScalingMergeData.blocks]
  rw [hl,Nat.min_eq_left (count_le hQ hc hcop hz j)]

private theorem selected_prefix_succ {Q c z : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) (payload : ℕ → List (Fin 4)) :
    let j := (ScalingControl.select hc Q z).val
    bufferPrefix hc Q (z+1) j payload = bufferPrefix hc Q z j payload ++ payload z := by
  dsimp only
  have hh := ScalingMergeData.selected_head hQ hc hcop hz
    (fun y => payload (ScalingPieces.output Q c y))
  dsimp only at hh
  rw [ScalingPieces.output_restore hz (ScalingControl.select_admissible hc hcop z)] at hh
  rw [ScalingMergeData.remaining,List.head?_drop] at hh
  obtain ⟨hi,hval⟩ := List.getElem?_eq_some_iff.mp hh
  simp only [bufferPrefix,targetBlocks,ScalingMergeData.popCount_succ,ite_true]
  rw [List.take_succ_eq_append_getElem hi,List.flatten_append,hval]
  simp

/-- Each buffer is an exact target-piece prefix, with its head just after it. -/
def buffers {c : ℕ} (hc : 0 < c) (Q B : ℕ) (background : Fin c → ℤ → Fin 4)
    (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (z : ℕ) : Tapes c 0 where
  head := fun j => p j + ((ScalingMergeData.popCount hc Q z j.val*B : ℕ) : ℤ)
  tape := fun j => putWord (background j) (p j) (bufferPrefix hc Q z j.val payload)

private theorem buffers_step {Q c z B : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) (background : Fin c → ℤ → Fin 4)
    (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    appendBuffer (buffers hc Q B background p payload z) (ScalingControl.select hc Q z) (payload z) =
      buffers hc Q B background p payload (z+1) := by
  unfold appendBuffer buffers
  congr 1
  · funext j
    by_cases hj : j = ScalingControl.select hc Q z
    · subst j
      simp only [Function.update_self,ScalingMergeData.popCount_succ,ite_true,hwidth]
      push_cast
      ring
    · have hv : (ScalingControl.select hc Q z).val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp only [Function.update_of_ne hj,ScalingMergeData.popCount_succ,ite_eq_right hv,Nat.add_zero]
  · funext j
    by_cases hj : j = ScalingControl.select hc Q z
    · subst j
      simp only [Function.update_self]
      rw [← prefix_length hQ hc hcop hz.le _ payload hwidth,putWord_append_forward,
        selected_prefix_succ hQ hc hcop hz]
    · have hv : (ScalingControl.select hc Q z).val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp only [Function.update_of_ne hj,bufferPrefix,ScalingMergeData.popCount_succ,
        ite_eq_right hv,Nat.add_zero]

/-- The source block stream remains in its original increasing address order. -/
def inputWord (Q : ℕ) (payload : ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range Q).map payload).flatten

private theorem source_next {Q B z : ℕ} (hz : z < Q) (source : ℤ → Fin 4)
    (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    putWord (putWord source q (inputWord Q payload)) (q+((z*B : ℕ) : ℤ)) (payload z) =
      putWord source q (inputWord Q payload) := by
  have hu : BlockRotationData.Uniform B ((List.range Q).map payload) := by
    intro block hb
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact hwidth _
  have hh := FiberShift.source_fiber source q _ B z hu (by simpa using hz)
  simpa only [inputWord,List.getElem_map,List.getElem_range] using hh

/-- Complete physical invariant for inverse scaling scatter. -/
def state {c : ℕ} (hc : 0 < c) (Q B : ℕ) (background : Fin c → ℤ → Fin 4)
    (p : Fin c → ℤ) (source : ℤ → Fin 4) (q : ℤ) (bs : List Bool)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (z : ℕ) : Tapes (4+c+c+c) 0 :=
  bank (buffers hc Q B background p payload z) (putWord source q (inputWord Q payload))
    (q+((z*B : ℕ) : ℤ)) bs modulus current (ScalingControl.residue hc Q) (ScalingControl.residue hc z)

theorem state_step {Q c B z : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hz : z < Q) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (source : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (hcount : Counter.value bs = B)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (body hc)
      (fun v => v = state hc Q B background p source q bs modulus current payload z)
      (fun v => v = state hc Q B background p source q bs modulus current payload (z+1))
      (5*B+7*bs.length+19) := by
  have hh := body_hoare hc (buffers hc Q B background p payload z)
    (putWord source q (inputWord Q payload)) (q+((z*B : ℕ) : ℤ)) bs modulus current
    (ScalingControl.residue hc Q) (ScalingControl.residue hc z) (payload z)
    (hcount.trans (hwidth z).symm) (source_next hz source q payload hwidth)
  dsimp only at hh
  change HoareTime (body hc)
    (fun v => v = state hc Q B background p source q bs modulus current payload z)
    (fun v => v = bank
      (appendBuffer (buffers hc Q B background p payload z) (ScalingControl.select hc Q z) (payload z))
      (putWord source q (inputWord Q payload)) (q+((z*B : ℕ) : ℤ)+(payload z).length)
      bs modulus current (ScalingControl.residue hc Q) (OneHot.next hc (ScalingControl.residue hc z)))
    (5*(payload z).length+7*bs.length+19) at hh
  rw [buffers_step hQ hc hcop hz background p payload hwidth,hwidth] at hh
  have hnext : OneHot.next hc (ScalingControl.residue hc z) = ScalingControl.residue hc (z+1) :=
    OneHot.next_residue hc z
  have hpos : q+((z*B : ℕ) : ℤ)+(B : ℤ) = q+(((z+1)*B : ℕ) : ℤ) := by push_cast; ring
  simpa only [state,hnext,hpos] using hh

/-- A fixed machine independent of modulus, block width and payload. -/
def program {c : ℕ} (hc : 0 < c) : Program (4+c+c+c+2) (7+(c*16+1+2+5)+4) 0 :=
  CountedLoopReuse.program (body hc)

/-- Entire inverse scatter: the source is consumed sequentially, whole blocks
are appended in order to the correct buffers, and both work clocks are cleaned. -/
theorem scatter_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ) (source : ℤ → Fin 4) (q : ℤ)
    (bs countBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (program hc)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p source q bs modulus current payload 0) empty (binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p source q bs modulus current payload Q) empty (binary countBits) 1 1)
      (Q*(5*B+7*bs.length+25)+7*countBits.length+16) := by
  have hh := CountedLoopReuse.loop_hoare (body hc) countBits Q
    (state hc Q B background p source q bs modulus current payload)
    (fun _ => 5*B+7*bs.length+19) hn
    (fun z hz => state_step hQ hc hcop hz background p source q bs hb modulus current payload hwidth)
  have hcost : (∑ _i ∈ Finset.range Q, (5*B+7*bs.length+19))+6*Q+7*countBits.length+16 =
      Q*(5*B+7*bs.length+25)+7*countBits.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Canonical prepared descriptors give a linear payload-volume bound. -/
theorem scatter_hoare_linear {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (source : ℤ → Fin 4) (q : ℤ) (bs countBits : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (program hc)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p source q bs modulus current payload 0) empty (binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p source q bs modulus current payload Q) empty (binary countBits) 1 1)
      (51*(Q*B)+23) := by
  have wb := GrowingCounterData.canonical_width bs cb
  have wn := GrowingCounterData.canonical_width countBits cn
  have lb := Nat.log2_le_self (Counter.value bs)
  have ln := Nat.log2_le_self (Counter.value countBits)
  exact (scatter_hoare hQ hc hcop background p source q bs countBits hb hn modulus current payload hwidth).consequence
    (fun _ h => h) (fun _ h => h) (ScalingMerge.linear_bound Q B bs countBits hB (by omega) (by omega))

/-- Initially every output buffer is exactly its arbitrary background. -/
theorem buffers_initial {c : ℕ} (hc : 0 < c) (Q B : ℕ)
    (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) :
    buffers hc Q B background p payload 0 = ⟨p,background⟩ := by
  simp [buffers,bufferPrefix,ScalingMergeData.popCount,putWord]

/-- Final piece contents are in increasing restored-address order: output y
contains input at c*y modulo Q after the pieces are concatenated. -/
theorem buffers_final_tape {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (B : ℕ) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (payload : ℕ → List (Fin 4)) (j : Fin c) :
    (buffers hc Q B background p payload Q).tape j =
      putWord (background j) (p j) (targetBlocks Q c j.val payload).flatten := by
  simp only [buffers,bufferPrefix,ScalingMergeData.complete_count hQ hc hcop]
  have hl : (targetBlocks Q c j.val payload).length =
      ScalingControl.boundary Q c (j.val+1)-ScalingControl.boundary Q c j.val := by
    simp [targetBlocks,ScalingMergeData.blocks]
  rw [← hl,List.take_length]

/-- Every final buffer head is positioned immediately after its complete piece. -/
theorem buffers_final_head {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (B : ℕ) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (payload : ℕ → List (Fin 4)) (j : Fin c) :
    (buffers hc Q B background p payload Q).head j = p j+
      (((ScalingControl.boundary Q c (j.val+1)-ScalingControl.boundary Q c j.val)*B : ℕ) : ℤ) := by
  simp only [buffers,ScalingMergeData.complete_count hQ hc hcop]

end IntegerMultBounds.Machine.ScalingScatter
