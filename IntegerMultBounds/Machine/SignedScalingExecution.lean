import IntegerMultBounds.Machine.ScalingExecutionReuse
import IntegerMultBounds.Machine.ScalingInverseExecution
import IntegerMultBounds.Machine.CountedSpanReset

/-! Literal rational-coordinate scaling through a shared intermediate tape.
The numerator forward pass and denominator inverse pass retain their own fixed
control banks; static placement aliases only the physically shared payload. -/

namespace IntegerMultBounds.Machine.SignedScalingExecution

/-- Replace a complete tape and its head, without moving any other tape. -/
def setTape {t : ℕ} (v : Tapes t 0) (i : Fin t) (f : ℤ → Fin 4) (p : ℤ) : Tapes t 0 :=
  ⟨Function.update v.head i p,Function.update v.tape i f⟩

@[simp] theorem setTape_self {t : ℕ} (v : Tapes t 0) (i : Fin t) :
    setTape v i (v.tape i) (v.head i) = v := by
  cases v
  simp [setTape]

@[simp] theorem setTape_setTape {t : ℕ} (v : Tapes t 0) (i : Fin t)
    (f g : ℤ → Fin 4) (p q : ℤ) : setTape (setTape v i f p) i g q = setTape v i g q := by
  simp [setTape,Function.update_idem]

theorem setTape_append_left {l r : ℕ} (v : Tapes l 0) (w : Tapes r 0) (i : Fin l)
    (f : ℤ → Fin 4) (p : ℤ) :
    setTape (v.append w) (Fin.castAdd r i) f p = (setTape v i f p).append w := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; have hi := i.isLt; omega

/-- Run a right-hand bank while sharing its selected slot with a left-hand
payload slot. The right-hand bank's original slot becomes stationary frame. -/
def sharedPlacement {l r : ℕ} (i : Fin l) (j : Fin r) : Fin (r+l) ≃ Fin (l+r) :=
  (finAddFlip : Fin (r+l) ≃ Fin (l+r)).trans (Equiv.swap (Fin.castAdd r i) (Fin.natAdd l j))

private theorem cross_ne {l r : ℕ} (i : Fin l) (j : Fin r) :
    Fin.castAdd r i ≠ Fin.natAdd l j := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at he
  have hi := i.isLt
  omega

private theorem shared_active_index {l r : ℕ} (i : Fin l) (j k : Fin r) :
    sharedPlacement i j (Fin.castAdd l k) = if k = j then Fin.castAdd r i else Fin.natAdd l k := by
  simp only [sharedPlacement,Equiv.trans_apply,finAddFlip_apply_castAdd]
  by_cases hk : k = j
  · subst k; simp
  · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (cross_ne i k)) (by simpa using hk)]
    simp [hk]

private theorem shared_extra_index {l r : ℕ} (i k : Fin l) (j : Fin r) :
    sharedPlacement i j (Fin.natAdd r k) = if k = i then Fin.natAdd l j else Fin.castAdd r k := by
  simp only [sharedPlacement,Equiv.trans_apply,finAddFlip_apply_natAdd]
  by_cases hk : k = i
  · subst k; simp
  · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hk) (cross_ne k j)]
    simp [hk]

theorem active_shared {l r : ℕ} (v : Tapes l 0) (w : Tapes r 0) (i : Fin l) (j : Fin r) :
    Placement.active (sharedPlacement i j) (v.append w) = setTape w j (v.tape i) (v.head i) := by
  unfold Placement.active setTape
  congr 1 <;> funext k <;> rw [shared_active_index] <;>
    by_cases hk : k = j <;> simp [hk,Tapes.append]

theorem extra_shared {l r : ℕ} (v : Tapes l 0) (w : Tapes r 0) (i : Fin l) (j : Fin r) :
    Placement.extra (sharedPlacement i j) (v.append w) = setTape v i (w.tape j) (w.head j) := by
  unfold Placement.extra setTape
  congr 1 <;> funext k <;> rw [shared_extra_index] <;>
    by_cases hk : k = i <;> simp [hk,Tapes.append]

theorem replace_shared {l r : ℕ} (v : Tapes l 0) (w w' : Tapes r 0) (i : Fin l) (j : Fin r) :
    Placement.replace (sharedPlacement i j) (v.append w) w' =
      (setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j)) := by
  rw [Placement.replace,extra_shared]
  have ha : Placement.active (sharedPlacement i j)
      ((setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j))) = w' := by
    rw [active_shared]
    simp [setTape]
  have he : Placement.extra (sharedPlacement i j)
      ((setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j))) =
        setTape v i (w.tape j) (w.head j) := by
    rw [extra_shared]
    simp [setTape]
  simpa only [ha,he] using Placement.view (sharedPlacement i j)
    ((setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j)))

/-- The inverse pass's original input slot is retained as an idle frame tape. -/
def inverseSourceSlot (c : ℕ) : Fin (ScalingExecution.TapeCount c) :=
  Fin.natAdd (ScalingExecution.SplitTapes c)
    (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (0 : Fin 4))))

/-- Pure block sequence emitted by the numerator pass. -/
def numeratorPayload {a : ℕ} (ha : 0 < a) (Q : ℕ) (payload : ℕ → List (Fin 4))
    (z : ℕ) : List (Fin 4) :=
  payload (ScalingPieces.restore Q a z (ScalingControl.select ha Q z).val)

theorem numerator_input {a : ℕ} (ha : 0 < a) (Q : ℕ) (payload : ℕ → List (Fin 4)) :
    ScalingScatter.inputWord Q (numeratorPayload ha Q payload) = ScalingMerge.outputPrefix ha Q Q payload := rfl


/-- Hoare placement with one physically shared tape and an idle original slot. -/
theorem shared_hoare {l r states : ℕ} {M : Program r states 0} {w w' : Tapes r 0} {cost : ℕ}
    (h : HoareTime M (fun x => x = w) (fun x => x = w') cost)
    (v : Tapes l 0) (i : Fin l) (j : Fin r) (spare : ℤ → Fin 4) (spareHead : ℤ)
    (hf : v.tape i = w.tape j) (hp : v.head i = w.head j) :
    HoareTime (Placement.placed M (sharedPlacement i j))
      (fun x => x = v.append (setTape w j spare spareHead))
      (fun x => x = (setTape v i (w'.tape j) (w'.head j)).append (setTape w' j spare spareHead)) cost := by
  have ha : Placement.active (sharedPlacement i j) (v.append (setTape w j spare spareHead)) = w := by
    rw [active_shared,hf,hp,setTape_setTape,setTape_self]
  have hh := Placement.hoare_at h (sharedPlacement i j) _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [replace_shared]
  simp only [setTape,Function.update_self]

/-- Prepared per-coefficient controls and reusable scratch. -/
structure Controls (c : ℕ) where
  background : Fin c → ℤ → Fin 4
  origins : Fin c → ℤ
  descriptors : Fin c → List Bool
  blockBits : List Bool
  countBits : List Bool
  modulus : Tapes c 0
  current : Tapes c 0

/-- Only immutable lengths are prepared; residue symbols may be arbitrary. -/
structure Controls.Valid {c : ℕ} (C : Controls c) (Q B : ℕ) : Prop where
  block_value : Counter.value C.blockBits = B
  count_value : Counter.value C.countBits = Q
  block_canonical : GrowingCounterData.Canonical C.blockBits
  count_canonical : GrowingCounterData.Canonical C.countBits
  piece_value : ∀ j, Counter.value (C.descriptors j) =
    ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val
  piece_canonical : ∀ j, GrowingCounterData.Canonical (C.descriptors j)
  scratch_blank : ∀ j z, C.origins j ≤ z → z < C.origins j+
    ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → C.background j z = blank

def forwardInput {a : ℕ} (A : Controls a) (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (ScalingExecution.TapeCount a) 0 :=
  ScalingExecutionReuse.input Q source p A.background A.origins middle r A.descriptors
    A.blockBits A.countBits A.modulus A.current payload

def forwardOutput {a : ℕ} (A : Controls a) (ha : 0 < a) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (ScalingExecution.TapeCount a) 0 :=
  ScalingExecutionReuse.output ha Q B source p A.background A.origins middle r A.descriptors
    A.blockBits A.countBits A.modulus A.current payload

def inverseInput {d : ℕ} (D : Controls d) (Q : ℕ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (ScalingExecution.TapeCount d) 0 :=
  ScalingInverseExecution.input Q middle r D.background D.origins dest q D.descriptors
    D.blockBits D.countBits D.modulus D.current payload

def inverseOutput {d : ℕ} (D : Controls d) (hd : 0 < d) (Q B : ℕ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (ScalingExecution.TapeCount d) 0 :=
  ScalingInverseExecution.output hd Q B middle r D.background D.origins dest q D.descriptors
    D.blockBits D.countBits D.modulus D.current payload

private theorem forward_hoare {Q a B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hcop : a.Coprime Q)
    (hB : 0 < B) (A : Controls a) (hA : A.Valid Q B) (source : ℤ → Fin 4) (p : ℤ)
    (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (ScalingExecutionReuse.program ha)
      (fun v => v = forwardInput A Q source p middle r payload)
      (fun v => v = forwardOutput A ha Q B source p middle r payload) (127*(Q*B)+120*a+52) := by
  have hlen : (ScalingExecution.inputWord Q payload).length = Q*B := by
    unfold ScalingExecution.inputWord
    rw [BlockRotationData.uniform_volume B]
    · simp
    · intro word hw; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hw; exact hwidth y
  have hp (j : Fin a) := ScalingSplit.piece_length ha _ hlen j
  exact ScalingExecutionReuse.scaling_hoare hQ ha hcop hB source p A.background A.origins middle r
    A.descriptors A.blockBits A.countBits hA.block_value hA.count_value hA.block_canonical hA.count_canonical
    payload (fun j => (hA.piece_value j).trans (hp j).symm) hA.piece_canonical A.modulus A.current hwidth
    (by intro j z hl hu; rw [hp j] at hu; exact hA.scratch_blank j z hl hu)

private theorem inverse_hoare {Q d B : ℕ} (hQ : 0 < Q) (hd : 0 < d) (hcop : d.Coprime Q)
    (hB : 0 < B) (D : Controls d) (hD : D.Valid Q B) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (ScalingInverseExecution.program hd)
      (fun v => v = inverseInput D Q middle r dest q payload)
      (fun v => v = inverseOutput D hd Q B middle r dest q payload) (127*(Q*B)+120*d+51) := by
  have hp (j : Fin d) : (ScalingInverseExecution.words Q payload j).length =
      ScalingSplit.offset Q d B (j.val+1)-ScalingSplit.offset Q d B j.val := by
    rw [ScalingInverseExecution.word_eq_piece hd payload hwidth]
    exact ScalingSplit.piece_length hd _ (ScalingInverseExecution.output_length (Q := Q) (c := d) payload hwidth) j
  exact ScalingInverseExecution.scaling_hoare hQ hd hcop hB middle r D.background D.origins dest q
    D.descriptors D.blockBits D.countBits hD.block_value hD.count_value hD.block_canonical hD.count_canonical
    payload (fun j => (hD.piece_value j).trans (hp j).symm) hD.piece_canonical D.modulus D.current hwidth
    (by intro j z hl hu; rw [hp j] at hu; exact hD.scratch_blank j z hl hu)


private theorem span_set (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool) :
    setTape (CountedSpanSeek.bank f p bs ns) 0 g q = CountedSpanSeek.bank g q bs ns := by
  unfold setTape CountedSpanSeek.bank CountedLoopReuse.bank CountedLoopReuse.controls CountedSeek.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem span_tape (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) :
    (CountedSpanSeek.bank f p bs ns).tape 0 = f := rfl

private theorem span_head (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) :
    (CountedSpanSeek.bank f p bs ns).head 0 = p := rfl

private theorem span_shared_hoare {t states : ℕ} {M : Program 5 states 0}
    {f g : ℤ → Fin 4} {p q : ℤ} {bs ns : List Bool} {cost : ℕ}
    (h : HoareTime M (fun v => v = CountedSpanSeek.bank f p bs ns)
      (fun v => v = CountedSpanSeek.bank g q bs ns) cost)
    (v : Tapes t 0) (i : Fin t) (hf : v.tape i = f) (hp : v.head i = p) :
    HoareTime (Placement.placed M (sharedPlacement i 0))
      (fun w => w = v.append (CountedSpanSeek.bank CountedCopyReuse.empty 0 bs ns))
      (fun w => w = (setTape v i g q).append (CountedSpanSeek.bank CountedCopyReuse.empty 0 bs ns)) cost := by
  have hh := shared_hoare h v i 0 CountedCopyReuse.empty 0 hf hp
  simpa only [span_set,span_tape,span_head] using hh

abbrev ForwardStates (a : ℕ) :=
  20+((ScalingSplit.states a+ScalingSplit.states a)+(7+(a*16+1+2+5)+4))+ScalingBuffersReset.states a
abbrev InverseStates (d : ℕ) :=
  20+(7+(d*16+1+2+5)+4)+ScalingConcatenate.states d+ScalingBuffersReset.states d
abbrev TapeCount (a d : ℕ) := (ScalingExecution.TapeCount a+ScalingExecution.TapeCount d)+5

def intermediateSlot (a d : ℕ) : Fin (ScalingExecution.TapeCount a+ScalingExecution.TapeCount d) :=
  Fin.castAdd (ScalingExecution.TapeCount d) (ScalingExecution.destinationSlot a)

/-- The positive rational core executes both passes, the handoff rewind, and
complete cleanup of the intermediate payload. -/
def unsignedProgram {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    Program (TapeCount a d) (ForwardStates a+32+InverseStates d+98) 0 :=
  seq (seq (seq
    (extend (extend (ScalingExecutionReuse.program ha) (ScalingExecution.TapeCount d)) 5)
    (Placement.placed CountedSpanSeek.backwardProgram (sharedPlacement (intermediateSlot a d) 0)))
    (extend (Placement.placed (ScalingInverseExecution.program hd)
      (sharedPlacement (ScalingExecution.destinationSlot a) (inverseSourceSlot d))) 5))
    (Placement.placed CountedSpanReset.program (sharedPlacement (intermediateSlot a d) 0))

/-- The denominator's original source slot is a fixed idle tape; its true input
is the numerator destination selected by static placement. -/
def stripSource {d : ℕ} (v : Tapes (ScalingExecution.TapeCount d) 0) : Tapes (ScalingExecution.TapeCount d) 0 :=
  setTape v (inverseSourceSlot d) CountedCopyReuse.empty 0

def unsignedInput {a d : ℕ} (ha : 0 < a) (A : Controls a) (D : Controls d) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((forwardInput A Q source p middle r payload).append
    (stripSource (inverseInput D Q middle r dest q (numeratorPayload ha Q payload)))).append
    (CountedSpanSeek.bank CountedCopyReuse.empty 0 A.blockBits A.countBits)

/-- Both internal coefficient scratch banks and the shared intermediate tape
are restored. Only the final output payload and residue controls have changed. -/
def unsignedOutput {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((setTape (forwardOutput A ha Q B source p middle r payload) (ScalingExecution.destinationSlot a) middle r).append
    (stripSource (inverseOutput D hd Q B middle r dest q (numeratorPayload ha Q payload)))).append
    (CountedSpanSeek.bank CountedCopyReuse.empty 0 A.blockBits A.countBits)

private theorem inverse_aux_tape {d : ℕ} (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) (m k : Tapes d 0) :
    (ScalingInverseExecution.auxiliary f p bs ns m k).tape
      (Fin.castAdd 2 (Fin.castAdd d (Fin.castAdd d (0 : Fin 4)))) = f := by
  change ((((CountedCopyReuse.bank f CountedCopyReuse.empty CountedCopyReuse.empty (CountedCopyReuse.binary bs)
    p 0 1 1).append m).append k).append (CountedLoopReuse.controls CountedCopyReuse.empty
      (CountedCopyReuse.binary ns) 1 1)).tape _ = _
  simp [Tapes.append,CountedCopyReuse.bank]

private theorem inverse_aux_head {d : ℕ} (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) (m k : Tapes d 0) :
    (ScalingInverseExecution.auxiliary f p bs ns m k).head
      (Fin.castAdd 2 (Fin.castAdd d (Fin.castAdd d (0 : Fin 4)))) = p := by
  change ((((CountedCopyReuse.bank f CountedCopyReuse.empty CountedCopyReuse.empty (CountedCopyReuse.binary bs)
    p 0 1 1).append m).append k).append (CountedLoopReuse.controls CountedCopyReuse.empty
      (CountedCopyReuse.binary ns) 1 1)).head _ = _
  simp [Tapes.append,CountedCopyReuse.bank]

private theorem forward_aux_head {a : ℕ} (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) (m k : Tapes a 0) :
    (ScalingExecutionReuse.auxiliary f p bs ns m k).head
      (Fin.castAdd 2 (Fin.castAdd a (Fin.castAdd a (1 : Fin 4)))) = p := by
  change ((((CountedCopyReuse.bank CountedCopyReuse.empty f CountedCopyReuse.empty (CountedCopyReuse.binary bs)
    0 p 1 1).append m).append k).append (CountedLoopReuse.controls CountedCopyReuse.empty
      (CountedCopyReuse.binary ns) 1 1)).head _ = _
  simp [Tapes.append,CountedCopyReuse.bank]

private theorem inverse_input_tape {d : ℕ} (D : Controls d) (Q : ℕ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (inverseInput D Q middle r dest q payload).tape (inverseSourceSlot d) =
      putWord middle r (ScalingScatter.inputWord Q payload) := by
  simp [inverseInput,inverseSourceSlot,ScalingInverseExecution.input,inverse_aux_tape,
    Tapes.append]

private theorem inverse_input_head {d : ℕ} (D : Controls d) (Q : ℕ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (inverseInput D Q middle r dest q payload).head (inverseSourceSlot d) = r := by
  simp [inverseInput,inverseSourceSlot,ScalingInverseExecution.input,inverse_aux_head,
    Tapes.append]


private theorem inverse_output_tape {d : ℕ} (D : Controls d) (hd : 0 < d) (Q B : ℕ)
    (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (inverseOutput D hd Q B middle r dest q payload).tape (inverseSourceSlot d) =
      putWord middle r (ScalingScatter.inputWord Q payload) := by
  simp [inverseOutput,inverseSourceSlot,ScalingInverseExecution.output,ScalingInverseExecution.finalAuxiliary,
    inverse_aux_tape,Tapes.append]

private theorem inverse_output_head {d : ℕ} (D : Controls d) (hd : 0 < d) (Q B : ℕ)
    (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (inverseOutput D hd Q B middle r dest q payload).head (inverseSourceSlot d) = r+((Q*B : ℕ) : ℤ) := by
  simp [inverseOutput,inverseSourceSlot,ScalingInverseExecution.output,ScalingInverseExecution.finalAuxiliary,
    inverse_aux_head,Tapes.append]

private theorem forward_output_tape {a : ℕ} (A : Controls a) (ha : 0 < a) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4)) :
    (forwardOutput A ha Q B source p middle r payload).tape (ScalingExecution.destinationSlot a) =
      putWord middle r (ScalingMerge.outputPrefix ha Q Q payload) :=
  ScalingExecutionReuse.output_tape ha Q B source p A.background A.origins middle r A.descriptors
    A.blockBits A.countBits A.modulus A.current payload

private theorem forward_output_head {a : ℕ} (A : Controls a) (ha : 0 < a) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4)) :
    (forwardOutput A ha Q B source p middle r payload).head (ScalingExecution.destinationSlot a) = r+((Q*B : ℕ) : ℤ) := by
  simp [forwardOutput,ScalingExecutionReuse.output,ScalingExecutionReuse.finalAuxiliary,
    forward_aux_head,ScalingExecution.destinationSlot,Tapes.append]

/-- Complete unsigned numerator/denominator scaling. The intermediate payload
is physically rewound, consumed, erased and returned to its original head. -/
theorem unsigned_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B)
    (A : Controls a) (D : Controls d) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank) :
    HoareTime (unsignedProgram ha hd)
      (fun v => v = unsignedInput ha A D Q source p middle r dest q payload)
      (fun v => v = unsignedOutput ha hd A D Q B source p middle r dest q payload)
      (448*(Q*B)+120*(a+d)+200) := by
  let ni := forwardInput A Q source p middle r payload
  let no := forwardOutput A ha Q B source p middle r payload
  let di := inverseInput D Q middle r dest q (numeratorPayload ha Q payload)
  let dout := inverseOutput D hd Q B middle r dest q (numeratorPayload ha Q payload)
  let span := CountedSpanSeek.bank CountedCopyReuse.empty 0 A.blockBits A.countBits
  let i := ScalingExecution.destinationSlot a
  let j := inverseSourceSlot d
  let raw := putWord middle r (ScalingMerge.outputPrefix ha Q Q payload)
  have nft : no.tape i = raw := forward_output_tape A ha Q B source p middle r payload
  have nfh : no.head i = r+((Q*B : ℕ) : ℤ) := forward_output_head A ha Q B source p middle r payload
  have dit : di.tape j = raw := inverse_input_tape D Q middle r dest q (numeratorPayload ha Q payload)
  have dih : di.head j = r := inverse_input_head D Q middle r dest q (numeratorPayload ha Q payload)
  have dot : dout.tape j = raw := inverse_output_tape D hd Q B middle r dest q (numeratorPayload ha Q payload)
  have doh : dout.head j = r+((Q*B : ℕ) : ℤ) := inverse_output_head D hd Q B middle r dest q (numeratorPayload ha Q payload)
  have h0 := ((forward_hoare hQ ha hcopA hB A hA source p middle r payload hwidth).extend
    (stripSource di)).extend span
  have hforward : HoareTime (extend (extend (ScalingExecutionReuse.program ha) (ScalingExecution.TapeCount d)) 5)
      (fun v => v = (ni.append (stripSource di)).append span)
      (fun v => v = (no.append (stripSource di)).append span) (127*(Q*B)+120*a+52) := by
    apply h0.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,⟨_,rfl,rfl⟩,rfl⟩
    · rintro v ⟨w,⟨u,rfl,rfl⟩,rfl⟩; rfl
  have hrewind₀ := span_shared_hoare
    (CountedSpanSeek.rewind_hoare_linear raw r B Q A.blockBits A.countBits
      hA.block_value hA.count_value hB hA.block_canonical hA.count_canonical)
    (no.append (stripSource di)) (Fin.castAdd (ScalingExecution.TapeCount d) i)
    (by simpa [Tapes.append] using nft) (by simpa [Tapes.append] using nfh)
  rw [setTape_append_left] at hrewind₀
  have hden₀ := shared_hoare
    (inverse_hoare hQ hd hcopD hB D hD middle r dest q (numeratorPayload ha Q payload) (fun y => hwidth _))
    (setTape no i raw r) i j CountedCopyReuse.empty 0
    (by simpa [setTape] using dit.symm) (by simpa [setTape] using dih.symm)
  have he : setTape (setTape no i raw r) i (dout.tape j) (dout.head j) = no := by
    rw [setTape_setTape,dot,doh,← nft,← nfh,setTape_self]
  change HoareTime _ (fun v => v = (setTape no i raw r).append (stripSource di))
    (fun v => v = (setTape (setTape no i raw r) i (dout.tape j) (dout.head j)).append (stripSource dout)) _ at hden₀
  rw [he] at hden₀
  have hden₁ := hden₀.extend span
  have hden : HoareTime (extend (Placement.placed (ScalingInverseExecution.program hd) (sharedPlacement i j)) 5)
      (fun v => v = ((setTape no i raw r).append (stripSource di)).append span)
      (fun v => v = (no.append (stripSource dout)).append span) (127*(Q*B)+120*d+51) := by
    apply hden₁.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,rfl,rfl⟩
    · rintro v ⟨w,rfl,rfl⟩; rfl
  have hlen : (ScalingMerge.outputPrefix ha Q Q payload).length = Q*B := by
    unfold ScalingMerge.outputPrefix
    rw [BlockRotationData.uniform_volume B]
    · simp
    · intro word hw; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hw; exact hwidth _
  have hreset₀ := CountedSpanReset.reset_word_hoare_linear middle r (ScalingMerge.outputPrefix ha Q Q payload)
    B Q A.blockBits A.countBits hlen hA.block_value hA.count_value hB hA.block_canonical hA.count_canonical
    (by simpa only [hlen] using hblank)
  rw [hlen] at hreset₀
  have hreset := span_shared_hoare hreset₀ (no.append (stripSource dout))
    (Fin.castAdd (ScalingExecution.TapeCount d) i)
    (by simpa [Tapes.append] using nft) (by simpa [Tapes.append] using nfh)
  rw [setTape_append_left] at hreset
  apply (((hforward.seq hrewind₀).seq hden).seq hreset).consequence (fun _ h => h) (fun _ h => h) _
  omega


/-- The output is the denominator pass's true destination, never its idle slot. -/
def destinationSlot (a d : ℕ) : Fin (TapeCount a d) :=
  Fin.castAdd 5 (Fin.natAdd (ScalingExecution.TapeCount a) (ScalingInverseExecution.destinationSlot d))

theorem unsigned_output_tape {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d)
    (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (unsignedOutput ha hd A D Q B source p middle r dest q payload).tape (destinationSlot a d) =
      putWord dest q (ScalingInverseExecution.outputWord Q d (numeratorPayload ha Q payload)) := by
  have hne : ScalingInverseExecution.destinationSlot d ≠ inverseSourceSlot d := by
    exact cross_ne _ _
  simp only [unsignedOutput,destinationSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    stripSource,setTape,Function.update_of_ne hne]
  exact ScalingInverseExecution.output_tape hd Q B middle r D.background D.origins dest q D.descriptors
    D.blockBits D.countBits D.modulus D.current (numeratorPayload ha Q payload)

/-- The entire shared intermediate background and original head are restored. -/
theorem unsigned_output_middle {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d)
    (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    let v := unsignedOutput ha hd A D Q B source p middle r dest q payload
    let slot := Fin.castAdd 5 (intermediateSlot a d)
    v.tape slot = middle ∧ v.head slot = r := by
  simp [unsignedOutput,intermediateSlot,Tapes.append,setTape]

theorem tapeCount_eq (a d : ℕ) : TapeCount a d = 25+4*(a+d) := by
  dsimp only [TapeCount]
  rw [ScalingExecution.tapeCount_eq,ScalingExecution.tapeCount_eq]
  omega

theorem unsigned_stateCount_eq (a d : ℕ) : ForwardStates a+32+InverseStates d+98 = 98*(a+d)+213 := by
  dsimp only [ForwardStates,InverseStates]
  rw [ScalingExecutionReuse.stateCount_eq,ScalingInverseExecution.stateCount_eq]
  omega

end IntegerMultBounds.Machine.SignedScalingExecution
