import IntegerMultBounds.Machine.ScalingMergeData
import IntegerMultBounds.Machine.Dispatch
import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.OneHot
import IntegerMultBounds.Machine.FiberShift

/-! Literal sequential scaling merge. Block sources occupy fixed tapes, and
finite local-symbol dispatch selects a reusable counted block copy. Descriptor
preparation and control heads are explicit in every contract. -/

namespace IntegerMultBounds.Machine.ScalingMerge

open Placement (ExactRun exact_seq)
open CountedCopyReuse (empty binary)

/-- One spare slot, destination, mutable block clock, immutable block descriptor,
then the c source tapes. The spare permits a simple fixed swap placement. -/
def core {c : ℕ} (sources : Tapes c 0) (dest : ℤ → Fin 4) (q : ℤ)
    (bs : List Bool) : Tapes (4+c) 0 :=
  (CountedCopyReuse.bank empty dest empty (binary bs) 0 q 1 1).append sources

def copyPlacement {c : ℕ} (j : Fin c) : Fin (4+c) ≃ Fin (4+c) :=
  Equiv.swap (Fin.castAdd c (0 : Fin 4)) (Fin.natAdd 4 j)

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

private theorem swap_control {c : ℕ} (j : Fin c) (i : Fin 4) (hi : i ≠ 0) :
    copyPlacement j (Fin.castAdd c i) = Fin.castAdd c i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hi (Fin.castAdd_inj.mp h)
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    omega

private theorem active_core {c : ℕ} (sources : Tapes c 0) (dest : ℤ → Fin 4)
    (q : ℤ) (bs : List Bool) (j : Fin c) :
    Placement.active (copyPlacement j) (core sources dest q bs) =
      CountedCopyReuse.bank (sources.tape j) dest empty (binary bs)
        (sources.head j) q 1 1 := by
  unfold Placement.active core
  congr 1
  · funext i
    fin_cases i
    · simp [copyPlacement,Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 1 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 2 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 3 (by decide),Tapes.append,CountedCopyReuse.bank]
  · funext i
    fin_cases i
    · simp [copyPlacement,Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 1 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 2 (by decide),Tapes.append,CountedCopyReuse.bank]
    · simp [swap_control j 3 (by decide),Tapes.append,CountedCopyReuse.bank]

/-- Only the selected source head advances; all source cells are retained. -/
def advanceSource {c : ℕ} (sources : Tapes c 0) (j : Fin c) (n : ℕ) : Tapes c 0 :=
  ⟨Function.update sources.head j (sources.head j+n),sources.tape⟩

private theorem replace_core {c : ℕ} (sources : Tapes c 0) (dest dest' : ℤ → Fin 4)
    (q q' : ℤ) (bs : List Bool) (j : Fin c) (n : ℕ) :
    Placement.replace (copyPlacement j) (core sources dest q bs)
      (CountedCopyReuse.bank (sources.tape j) dest' empty (binary bs)
        (sources.head j+n) q' 1 1) = core (advanceSource sources j n) dest' q' bs := by
  unfold Placement.replace Placement.combine Placement.extra core copyPlacement
    Tapes.reindex Tapes.append CountedCopyReuse.bank advanceSource
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i =>
      fin_cases i <;> simp [Equiv.swap_apply_def]
    | right i =>
      by_cases hi : i = j
      · subst i; simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def,hi]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      fin_cases i <;> simp [Equiv.swap_apply_def]
    | right i =>
      by_cases hi : i = j
      · subst i; simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def,hi]

/-- Actual placed counted copy, preserving every source cell and all other
source heads, and restoring the mutable block clock. -/
theorem copy_exact {c : ℕ} (sources : Tapes c 0) (dest : ℤ → Fin 4)
    (q : ℤ) (bs : List Bool) (j : Fin c) (xs : List (Fin 4))
    (hcount : Counter.value bs = xs.length)
    (hsource : putWord (sources.tape j) (sources.head j) xs = sources.tape j) :
    ExactRun (copyProgram j) (CountedCopyReuse.runtime xs.length bs)
      (core sources dest q bs)
      (core (advanceSource sources j xs.length) (putWord dest q xs) (q+xs.length) bs) := by
  have hh := CountedCopyReuse.copy_exact (sources.tape j) dest (sources.head j) q xs bs hcount
  rw [hsource] at hh
  change ExactRun CountedCopyReuse.program _ _ _ at hh
  rw [← active_core sources dest q bs j] at hh
  simpa only [copyProgram,replace_core] using
    Placement.placed_exact CountedCopyReuse.program (copyPlacement j) (core sources dest q bs) _ hh

/-- The modulus and current residue occupy two fixed one-hot control banks. -/
def bank {c : ℕ} (sources : Tapes c 0) (dest : ℤ → Fin 4) (q : ℤ)
    (bs : List Bool) (modulus current : Tapes c 0) (m z : Fin c) : Tapes (4+c+c+c) 0 :=
  ((core sources dest q bs).append (OneHot.bank modulus m)).append (OneHot.bank current z)

def family {c : ℕ} (j : Fin c) : Program (4+c+c+c) 16 0 :=
  extend (extend (copyProgram j) c) c

/-- Only scanned control cells enter this fixed finite lookup table. -/
def selector {c : ℕ} (hc : 0 < c) (symbols : Fin (4+c+c+c) → Fin 4) : Fin c :=
  ScalingControl.table hc
    (OneHot.decode hc (fun i => symbols (Fin.castAdd c (Fin.natAdd (4+c) i))))
    (OneHot.decode hc (fun i => symbols (Fin.natAdd (4+c+c) i)))

theorem selector_bank {c : ℕ} (hc : 0 < c) (sources : Tapes c 0)
    (dest : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (modulus current : Tapes c 0) (m z : Fin c) :
    selector hc (bank sources dest q bs modulus current m z).reads = ScalingControl.table hc m z := by
  simp [selector,bank,Tapes.reads,Tapes.append,OneHot.decode_symbol]

def advanceProgram {c : ℕ} (hc : 0 < c) : Program (4+c+c+c) 2 0 :=
  Placement.placed (OneHot.program hc) (finAddFlip : Fin (c+(4+c+c)) ≃ Fin (4+c+c+c))

/-- Copy a selected whole block, then advance the current output residue. -/
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
theorem body_exact {c : ℕ} (hc : 0 < c) (sources : Tapes c 0)
    (dest : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (modulus current : Tapes c 0)
    (m z : Fin c) (xs : List (Fin 4)) (hcount : Counter.value bs = xs.length)
    (hsource : let j := ScalingControl.table hc m z
      putWord (sources.tape j) (sources.head j) xs = sources.tape j) :
    let j := ScalingControl.table hc m z
    ExactRun (body hc) (CountedCopyReuse.runtime xs.length bs+3)
      (bank sources dest q bs modulus current m z)
      (bank (advanceSource sources j xs.length) (putWord dest q xs) (q+xs.length)
        bs modulus current m (OneHot.next hc z)) := by
  dsimp only at hsource ⊢
  let j := ScalingControl.table hc m z
  have hcopy := exact_extend (OneHot.bank current z)
    (exact_extend (OneHot.bank modulus m) (copy_exact sources dest q bs j xs hcount hsource))
  obtain ⟨last,hr,hh,hfinal⟩ := hcopy
  have hdispatch : ExactRun (Dispatch.program hc family (selector hc))
      (1+CountedCopyReuse.runtime xs.length bs)
      (bank sources dest q bs modulus current m z)
      (bank (advanceSource sources j xs.length) (putWord dest q xs) (q+xs.length)
        bs modulus current m z) := by
    exact ⟨last.mapState (Dispatch.tag j),
      Dispatch.run_selected hc family (selector hc) _ j
        (selector_bank hc sources dest q bs modulus current m z) hr,
      Dispatch.halt_selected hc family (selector hc) j hh,hfinal⟩
  have hadvance := advance_exact hc
    ((core (advanceSource sources j xs.length) (putWord dest q xs) (q+xs.length) bs).append
      (OneHot.bank modulus m)) current z
  have hboth := exact_seq hdispatch hadvance
  simpa only [body,bank,j,show 1+CountedCopyReuse.runtime xs.length bs+1+1 =
    CountedCopyReuse.runtime xs.length bs+3 by omega] using hboth

/-- Uniform body bound independent of the stream index and input modulus. -/
theorem body_hoare {c : ℕ} (hc : 0 < c) (sources : Tapes c 0)
    (dest : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (modulus current : Tapes c 0)
    (m z : Fin c) (xs : List (Fin 4)) (hcount : Counter.value bs = xs.length)
    (hsource : let j := ScalingControl.table hc m z
      putWord (sources.tape j) (sources.head j) xs = sources.tape j) :
    let j := ScalingControl.table hc m z
    HoareTime (body hc)
      (fun v => v = bank sources dest q bs modulus current m z)
      (fun v => v = bank (advanceSource sources j xs.length) (putWord dest q xs)
        (q+xs.length) bs modulus current m (OneHot.next hc z))
      (5*xs.length+7*bs.length+19) := by
  dsimp only
  rintro v rfl
  obtain ⟨last,hr,hh,hfinal⟩ := body_exact hc sources dest q bs modulus current m z xs hcount hsource
  have htime := CountedCopyReuse.runtime_le_linear xs bs hcount
  exact ⟨_,last,by omega,hr,hh,hfinal⟩

/-- Physical contiguous source streams and their consumed-prefix head positions.
The background contents outside these streams are arbitrary and preserved. -/
def sources {c : ℕ} (hc : 0 < c) (Q B : ℕ) (background : Fin c → ℤ → Fin 4)
    (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (z : ℕ) : Tapes c 0 where
  head := fun j => p j + ((ScalingMergeData.popCount hc Q z j.val * B : ℕ) : ℤ)
  tape := fun j => putWord (background j) (p j) (ScalingMergeData.blocks Q c j.val payload).flatten

private theorem sources_step {c : ℕ} (hc : 0 < c) (Q B : ℕ)
    (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (z : ℕ) :
    advanceSource (sources hc Q B background p payload z) (ScalingControl.select hc Q z) B =
      sources hc Q B background p payload (z+1) := by
  unfold advanceSource sources
  congr 1
  funext i
  by_cases hi : i = ScalingControl.select hc Q z
  · subst i
    simp only [Function.update_self,ScalingMergeData.popCount_succ,ite_true]
    push_cast
    ring
  · have hval : (ScalingControl.select hc Q z).val ≠ i.val := by
      intro h
      exact hi (Fin.ext h.symm)
    simp only [Function.update_of_ne hi,ScalingMergeData.popCount_succ,ite_eq_right hval,Nat.add_zero]

private theorem source_next {Q c B z : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hz : z < Q) (background : Fin c → ℤ → Fin 4)
    (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    let j := ScalingControl.select hc Q z
    let src := sources hc Q B background p payload z
    putWord (src.tape j) (src.head j) (payload (ScalingPieces.restore Q c z j.val)) = src.tape j := by
  dsimp only
  have hhead := ScalingMergeData.selected_head hQ hc hcop hz payload
  dsimp only at hhead
  rw [ScalingMergeData.remaining,List.head?_drop] at hhead
  obtain ⟨hi,hval⟩ := List.getElem?_eq_some_iff.mp hhead
  have huniform : BlockRotationData.Uniform B
      (ScalingMergeData.blocks Q c (ScalingControl.select hc Q z).val payload) := by
    intro block hb
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact hwidth y
  have hh := FiberShift.source_fiber (background (ScalingControl.select hc Q z))
    (p (ScalingControl.select hc Q z)) _ B _ huniform hi
  rw [hval] at hh
  exact hh

/-- Already emitted blocks, listed in increasing output address. -/
def outputPrefix {c : ℕ} (hc : 0 < c) (Q z : ℕ) (payload : ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range z).map
    (fun w => payload (ScalingPieces.restore Q c w (ScalingControl.select hc Q w).val))).flatten

private theorem prefix_succ {c : ℕ} (hc : 0 < c) (Q z : ℕ) (payload : ℕ → List (Fin 4)) :
    outputPrefix hc Q (z+1) payload = outputPrefix hc Q z payload ++
      payload (ScalingPieces.restore Q c z (ScalingControl.select hc Q z).val) := by
  simp [outputPrefix,List.range_succ,List.map_append,List.flatten_append]

private theorem prefix_length {c : ℕ} (hc : 0 < c) (Q z B : ℕ)
    (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    (outputPrefix hc Q z payload).length = z*B := by
  unfold outputPrefix
  rw [BlockRotationData.uniform_volume B]
  · simp
  · intro block hb
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    exact hwidth _

/-- Complete loop invariant, including all payload/control head positions and
all tape contents. Only the current residue and destination cells are written. -/
def state {c : ℕ} (hc : 0 < c) (Q B : ℕ) (background : Fin c → ℤ → Fin 4)
    (p : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ) (bs : List Bool)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (z : ℕ) : Tapes (4+c+c+c) 0 :=
  bank (sources hc Q B background p payload z) (putWord dest q (outputPrefix hc Q z payload))
    (q+((z*B : ℕ) : ℤ)) bs modulus current (ScalingControl.residue hc Q) (ScalingControl.residue hc z)

/-- The literal body realizes one step of the mathematical merge invariant. -/
theorem state_step {Q c B z : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hz : z < Q) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs : List Bool) (hcount : Counter.value bs = B)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (body hc)
      (fun v => v = state hc Q B background p dest q bs modulus current payload z)
      (fun v => v = state hc Q B background p dest q bs modulus current payload (z+1))
      (5*B+7*bs.length+19) := by
  let j := ScalingControl.select hc Q z
  let xs := payload (ScalingPieces.restore Q c z j.val)
  have hlen : xs.length = B := hwidth _
  have hh := body_hoare hc (sources hc Q B background p payload z)
    (putWord dest q (outputPrefix hc Q z payload)) (q+((z*B : ℕ) : ℤ)) bs modulus current
    (ScalingControl.residue hc Q) (ScalingControl.residue hc z) xs
    (hcount.trans hlen.symm) (source_next hQ hc hcop hz background p payload hwidth)
  dsimp only at hh
  change HoareTime (body hc)
    (fun v => v = state hc Q B background p dest q bs modulus current payload z)
    (fun v => v = bank (advanceSource (sources hc Q B background p payload z) j xs.length)
      (putWord (putWord dest q (outputPrefix hc Q z payload)) (q+((z*B : ℕ) : ℤ)) xs)
      (q+((z*B : ℕ) : ℤ)+xs.length) bs modulus current
      (ScalingControl.residue hc Q) (OneHot.next hc (ScalingControl.residue hc z)))
    (5*xs.length+7*bs.length+19) at hh
  have hout : putWord (putWord dest q (outputPrefix hc Q z payload)) (q+((z*B : ℕ) : ℤ)) xs =
      putWord dest q (outputPrefix hc Q (z+1) payload) := by
    rw [← prefix_length hc Q z B payload hwidth,putWord_append_forward,prefix_succ]
  have hnext : OneHot.next hc (ScalingControl.residue hc z) = ScalingControl.residue hc (z+1) :=
    OneHot.next_residue hc z
  rw [hlen,hout,hnext] at hh
  dsimp only [j] at hh
  rw [sources_step] at hh
  have hpos : q+((z*B : ℕ) : ℤ)+(B : ℤ) = q+(((z+1)*B : ℕ) : ℤ) := by push_cast; ring
  simpa only [state,hpos] using hh

/-- One fixed finite machine for this fixed multiplier, independent of Q and B. -/
def program {c : ℕ} (hc : 0 < c) : Program (4+c+c+c+2) (7+(c*16+1+2+5)+4) 0 :=
  CountedLoopReuse.program (body hc)

/-- Complete literal merge of prepared contiguous streams. Both binary clocks
are cleaned, their immutable descriptors survive, all source cells survive,
and the output is exactly inverse-scaled with block contents unchanged. -/
theorem merge_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs countBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (program hc)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p dest q bs modulus current payload 0) empty (binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p dest q bs modulus current payload Q) empty (binary countBits) 1 1)
      (Q*(5*B+7*bs.length+25)+7*countBits.length+16) := by
  have hh := CountedLoopReuse.loop_hoare (body hc) countBits Q
    (state hc Q B background p dest q bs modulus current payload)
    (fun _ => 5*B+7*bs.length+19) hn
    (fun z hz => state_step hQ hc hcop hz background p dest q bs hb modulus current payload hwidth)
  have hcost : (∑ _i ∈ Finset.range Q, (5*B+7*bs.length+19))+6*Q+7*countBits.length+16 =
      Q*(5*B+7*bs.length+25)+7*countBits.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Canonical descriptor widths make every charged transition linear in the
payload volume. Descriptor synthesis and source splitting are separate tasks. -/
theorem linear_bound (Q B : ℕ) (bs countBits : List Bool) (hB : 0 < B)
    (hb : bs.length ≤ B+1) (hn : countBits.length ≤ Q+1) :
    Q*(5*B+7*bs.length+25)+7*countBits.length+16 ≤ 51*(Q*B)+23 := by
  have hbody : 5*B+7*bs.length+25 ≤ 44*B := by omega
  have hh := Nat.mul_le_mul_left Q hbody
  have hQB : Q ≤ Q*B := by nlinarith
  nlinarith

private theorem descriptor_width (bs : List Bool) (h : GrowingCounterData.Canonical bs) :
    bs.length ≤ Counter.value bs+1 := by
  have hw := GrowingCounterData.canonical_width bs h
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

/-- Linear-volume Hoare contract for the complete literal merge with canonical
prepared descriptors. The exact initial and final banks remain explicit. -/
theorem merge_hoare_linear {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (bs countBits : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (program hc)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p dest q bs modulus current payload 0) empty (binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state hc Q B background p dest q bs modulus current payload Q) empty (binary countBits) 1 1)
      (51*(Q*B)+23) := by
  have wb := descriptor_width bs cb
  have wn := descriptor_width countBits cn
  rw [hb] at wb
  rw [hn] at wn
  exact (merge_hoare hQ hc hcop background p dest q bs countBits hb hn modulus current payload hwidth).consequence
    (fun _ h => h) (fun _ h => h) (linear_bound Q B bs countBits hB wb wn)

/-- Every source begins at the beginning of its physically prepared stream. -/
theorem sources_initial_head {c : ℕ} (hc : 0 < c) (Q B : ℕ)
    (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (j : Fin c) :
    (sources hc Q B background p payload 0).head j = p j := by
  simp [sources,ScalingMergeData.popCount]

/-- Every source finishes exactly after its entire stream; empty streams retain
their initial head, and every source tape retains its original cells. -/
theorem sources_final_head {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (B : ℕ) (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ)
    (payload : ℕ → List (Fin 4)) (j : Fin c) :
    (sources hc Q B background p payload Q).head j = p j +
      (((ScalingControl.boundary Q c (j.val+1)-ScalingControl.boundary Q c j.val)*B : ℕ) : ℤ) := by
  simp only [sources,ScalingMergeData.complete_count hQ hc hcop]

/-- Source data never changes anywhere, including arbitrary outside backgrounds. -/
theorem sources_tapes_unchanged {c : ℕ} (hc : 0 < c) (Q B : ℕ)
    (background : Fin c → ℤ → Fin 4) (p : Fin c → ℤ) (payload : ℕ → List (Fin 4)) (z : ℕ) :
    (sources hc Q B background p payload z).tape = (sources hc Q B background p payload 0).tape := rfl

end IntegerMultBounds.Machine.ScalingMerge
