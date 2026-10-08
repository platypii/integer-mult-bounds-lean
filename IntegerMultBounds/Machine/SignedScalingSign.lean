import IntegerMultBounds.Machine.SignedScalingExecution
import IntegerMultBounds.Machine.BlockNegationReuse
import IntegerMultBounds.Machine.ScalingAffineBridge

/-! Compile-time sign choice for literal rational-coordinate scaling. Positive
coefficients use the unsigned core directly. Negative coefficients additionally
rewind and negate the unsigned stream, then erase and rewind that intermediate.
Tail-length and tail-block-count descriptors remain explicit prepared inputs. -/
namespace IntegerMultBounds.Machine.SignedScalingSign

open SignedScalingExecution (Controls setTape sharedPlacement shared_hoare)
open CountedCopyReuse (empty)

/-- Additional scratch and immutable tail descriptors for coordinate negation. -/
structure SignControls where
  scratch : ℤ → Fin 4
  origin : ℤ
  tailBits : List Bool
  tailCountBits : List Bool

structure SignControls.Valid (S : SignControls) (Q B : ℕ) : Prop where
  tail_value : Counter.value S.tailBits = (Q-1)*B
  count_value : Counter.value S.tailCountBits = Q-1
  tail_canonical : GrowingCounterData.Canonical S.tailBits
  count_canonical : GrowingCounterData.Canonical S.tailCountBits
  scratch_blank : ∀ z, S.origin ≤ z → z < S.origin+(((Q-1)*B : ℕ) : ℤ) → S.scratch z = blank

/-- The exact unsigned block stream, before the optional sign stage. -/
def unsignedBlocks {a : ℕ} (ha : 0 < a) (Q d : ℕ) (payload : ℕ → List (Fin 4)) : List (List (Fin 4)) :=
  ScalingAffineBridge.inverseBlocks Q d (SignedScalingExecution.numeratorPayload ha Q payload)

theorem blocks_length {a : ℕ} (ha : 0 < a) (Q d : ℕ) (payload : ℕ → List (Fin 4)) :
    (unsignedBlocks ha Q d payload).length = Q := by simp [unsignedBlocks,ScalingAffineBridge.inverseBlocks]

theorem blocks_uniform {a : ℕ} (ha : 0 < a) (Q d B : ℕ) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) : BlockRotationData.Uniform B (unsignedBlocks ha Q d payload) := by
  intro word hw
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hw
  exact hwidth _

theorem blocks_volume {a : ℕ} (ha : 0 < a) (Q d B : ℕ) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) : (unsignedBlocks ha Q d payload).flatten.length = Q*B := by
  rw [BlockRotationData.uniform_volume B _ (blocks_uniform ha Q d B payload hwidth),blocks_length]

/-- Both literal pass orders realize the same exact signed block list. -/
theorem signed_blocks {Q a : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hcop : a.Coprime Q)
    (d : ℕ) (negative : Bool) (payload : ℕ → List (Fin 4)) :
    (if negative then BlockNegationData.negate (unsignedBlocks ha Q d payload)
      else unsignedBlocks ha Q d payload) = ScalingAffineBridge.signedBlocks ha Q d negative payload := by
  have he := ScalingAffineBridge.stages_commute hQ ha hcop d payload
  change unsignedBlocks ha Q d payload = _ at he
  rw [he]
  rfl

private theorem bank_set (source dest scratch newSource : ℤ → Fin 4) (b dt ct : List Bool)
    (p q r newHead : ℤ) :
    setTape (BlockNegationReuse.bank source dest scratch b dt ct p q r) 0 newSource newHead =
      BlockNegationReuse.bank newSource dest scratch b dt ct newHead q r := by
  unfold setTape BlockNegationReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem span_set (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool) :
    setTape (CountedSpanSeek.bank f p bs ns) 0 g q = CountedSpanSeek.bank g q bs ns := by
  unfold setTape CountedSpanSeek.bank CountedLoopReuse.bank CountedLoopReuse.controls CountedSeek.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem span_shared_hoare {t states : ℕ} {M : Program 5 states 0}
    {f g : ℤ → Fin 4} {p q : ℤ} {bs ns : List Bool} {cost : ℕ}
    (h : HoareTime M (fun v => v = CountedSpanSeek.bank f p bs ns)
      (fun v => v = CountedSpanSeek.bank g q bs ns) cost)
    (v : Tapes t 0) (i : Fin t) (hf : v.tape i = f) (hp : v.head i = p) :
    HoareTime (Placement.placed M (sharedPlacement i 0))
      (fun w => w = v.append (CountedSpanSeek.bank empty 0 bs ns))
      (fun w => w = (setTape v i g q).append (CountedSpanSeek.bank empty 0 bs ns)) cost := by
  have hh := shared_hoare h v i 0 empty 0 hf hp
  simpa only [span_set,show (CountedSpanSeek.bank g q bs ns).tape 0 = g from rfl,
    show (CountedSpanSeek.bank g q bs ns).head 0 = q from rfl] using hh

private theorem negate_hoare (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hq : blocks.length = Q) (hu : BlockRotationData.Uniform B blocks)
    (bs : List Bool) (hb : Counter.value bs = B) (cb : GrowingCounterData.Canonical bs)
    (S : SignControls) (hS : S.Valid Q B) :
    HoareTime BlockNegationReuse.program
      (fun v => v = BlockNegationReuse.bank (putWord source p blocks.flatten) dest S.scratch
        bs S.tailBits S.tailCountBits p q S.origin)
      (fun v => v = BlockNegationReuse.bank (putWord source p blocks.flatten)
        (putWord dest q (BlockNegationData.negate blocks).flatten) S.scratch bs S.tailBits S.tailCountBits
        (p+((Q*B : ℕ) : ℤ)) (q+((Q*B : ℕ) : ℤ)) S.origin) (210*(Q*B)+219) := by
  cases blocks with
  | nil => simp only [List.length_nil] at hq; omega
  | cons first tail =>
    have hf : first.length = B := hu first (by simp)
    have ht : BlockRotationData.Uniform B tail := fun x hx => hu x (by simp [hx])
    have hn : tail.length = Q-1 := by simp only [List.length_cons] at hq; omega
    have hv := BlockRotationData.uniform_volume B (first::tail) hu
    rw [hq] at hv
    have hh := BlockNegationReuse.negate_hoare_linear source dest S.scratch p q S.origin first tail B hf ht hB
      bs S.tailBits S.tailCountBits hb (by simpa only [hn] using hS.tail_value)
      (by simpa only [hn] using hS.count_value) cb hS.tail_canonical hS.count_canonical
      (by simpa only [BlockRotationData.uniform_volume B tail ht,hn] using hS.scratch_blank)
    simpa only [hv] using hh

abbrev CoreStates (a d : ℕ) := SignedScalingExecution.ForwardStates a+32+SignedScalingExecution.InverseStates d+98
abbrev TapeCount (a d : ℕ) := (SignedScalingExecution.TapeCount a d+8)+5

def coreSlot (a d : ℕ) : Fin (SignedScalingExecution.TapeCount a d+8) :=
  Fin.castAdd 8 (SignedScalingExecution.destinationSlot a d)

/-- A fixed negative-sign program; every intermediate movement is charged. -/
def negativeProgram {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    Program (TapeCount a d) (CoreStates a d+32+202+98) 0 :=
  seq (seq (seq (extend (extend (SignedScalingExecution.unsignedProgram ha hd) 8) 5)
    (Placement.placed CountedSpanSeek.backwardProgram (sharedPlacement (coreSlot a d) 0)))
    (extend (Placement.placed BlockNegationReuse.program
      (sharedPlacement (SignedScalingExecution.destinationSlot a d) (0 : Fin 8))) 5))
    (Placement.placed CountedSpanReset.program (sharedPlacement (coreSlot a d) 0))

/-- The positive-sign program frames the unused sign controls with no extra pass. -/
def positiveProgram {a d : ℕ} (ha : 0 < a) (hd : 0 < d) : Program (TapeCount a d) (CoreStates a d) 0 :=
  extend (extend (SignedScalingExecution.unsignedProgram ha hd) 8) 5

def signBank (S : SignControls) (bs : List Bool) (dest : ℤ → Fin 4) (q : ℤ) : Tapes 8 0 :=
  BlockNegationReuse.bank empty dest S.scratch bs S.tailBits S.tailCountBits 0 q S.origin

def negativeInput {a d : ℕ} (ha : 0 < a) (A : Controls a) (D : Controls d) (S : SignControls) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((SignedScalingExecution.unsignedInput ha A D Q source p middle r signMiddle t payload).append
    (signBank S A.blockBits dest q)).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

def negativeOutput {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d)
    (S : SignControls) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((setTape (SignedScalingExecution.unsignedOutput ha hd A D Q B source p middle r signMiddle t payload)
    (SignedScalingExecution.destinationSlot a d) signMiddle t).append
    (signBank S A.blockBits (putWord dest q (BlockNegationData.negate (unsignedBlocks ha Q d payload)).flatten)
      (q+((Q*B : ℕ) : ℤ)))).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

private theorem core_head {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d)
    (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (SignedScalingExecution.unsignedOutput ha hd A D Q B source p middle r dest q payload).head
      (SignedScalingExecution.destinationSlot a d) = q+((Q*B : ℕ) : ℤ) := by
  have hne : ScalingInverseExecution.destinationSlot d ≠ SignedScalingExecution.inverseSourceSlot d := by
    intro h
    have hv := congrArg Fin.val h
    simp [ScalingInverseExecution.destinationSlot,SignedScalingExecution.inverseSourceSlot,ScalingExecution.SplitTapes] at hv
    omega
  simp only [SignedScalingExecution.unsignedOutput,SignedScalingExecution.destinationSlot,Tapes.append,
    Fin.addCases_left,Fin.addCases_right,SignedScalingExecution.stripSource,setTape,Function.update_of_ne hne]
  simp [SignedScalingExecution.inverseOutput,ScalingInverseExecution.output,ScalingInverseExecution.destinationSlot,
    ScalingSplit.bank,Tapes.append,CountedCopyReuse.bank]


/-- The negative branch includes both shared-intermediate cleanup passes and
retains every coefficient and sign descriptor. -/
theorem negative_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B)
    (A : Controls a) (D : Controls d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B) (hS : S.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (negativeProgram ha hd)
      (fun v => v = negativeInput ha A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = negativeOutput ha hd A D S Q B source p middle r signMiddle t dest q payload)
      (852*(Q*B)+120*(a+d)+516) := by
  let ui := SignedScalingExecution.unsignedInput ha A D Q source p middle r signMiddle t payload
  let uo := SignedScalingExecution.unsignedOutput ha hd A D Q B source p middle r signMiddle t payload
  let sb := signBank S A.blockBits dest q
  let span := CountedSpanSeek.bank empty 0 A.blockBits A.countBits
  let i := SignedScalingExecution.destinationSlot a d
  let blocks := unsignedBlocks ha Q d payload
  let raw := putWord signMiddle t blocks.flatten
  let sb' := signBank S A.blockBits (putWord dest q (BlockNegationData.negate blocks).flatten)
    (q+((Q*B : ℕ) : ℤ))
  have hft : uo.tape i = raw :=
    SignedScalingExecution.unsigned_output_tape ha hd A D Q B source p middle r signMiddle t payload
  have hfh : uo.head i = t+((Q*B : ℕ) : ℤ) := core_head ha hd A D Q B source p middle r signMiddle t payload
  have h0 := ((SignedScalingExecution.unsigned_hoare hQ ha hd hcopA hcopD hB A D hA hD source p middle r
    signMiddle t payload hwidth hblank).extend sb).extend span
  have hu : HoareTime (extend (extend (SignedScalingExecution.unsignedProgram ha hd) 8) 5)
      (fun v => v = (ui.append sb).append span) (fun v => v = (uo.append sb).append span)
      (448*(Q*B)+120*(a+d)+200) := by
    apply h0.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,⟨_,rfl,rfl⟩,rfl⟩
    · rintro v ⟨w,⟨x,rfl,rfl⟩,rfl⟩; rfl
  have hr := span_shared_hoare (CountedSpanSeek.rewind_hoare_linear raw t B Q A.blockBits A.countBits
    hA.block_value hA.count_value hB hA.block_canonical hA.count_canonical) (uo.append sb) (Fin.castAdd 8 i)
    (by simpa [Tapes.append] using hft) (by simpa [Tapes.append] using hfh)
  rw [SignedScalingExecution.setTape_append_left] at hr
  have hn₀ := shared_hoare
    (negate_hoare Q B hQ hB signMiddle dest t q blocks (blocks_length ha Q d payload)
      (blocks_uniform ha Q d B payload hwidth) A.blockBits hA.block_value hA.block_canonical S hS)
    (setTape uo i raw t) i (0 : Fin 8) empty 0 (by simp [setTape]; rfl) (by simp [setTape]; rfl)
  simp only [bank_set] at hn₀
  have hn : HoareTime (Placement.placed BlockNegationReuse.program (sharedPlacement i (0 : Fin 8)))
      (fun v => v = (setTape uo i raw t).append sb)
      (fun v => v = uo.append sb') (210*(Q*B)+219) := by
    apply hn₀.consequence (fun _ h => h) _ le_rfl
    intro v hv
    change v = (setTape (setTape uo i raw t) i raw (t+((Q*B : ℕ) : ℤ))).append sb' at hv
    rw [SignedScalingExecution.setTape_setTape,← hft,← hfh,SignedScalingExecution.setTape_self] at hv
    exact hv
  have hn₁ := hn.extend span
  have hneg : HoareTime (extend (Placement.placed BlockNegationReuse.program (sharedPlacement i (0 : Fin 8))) 5)
      (fun v => v = ((setTape uo i raw t).append sb).append span)
      (fun v => v = (uo.append sb').append span) (210*(Q*B)+219) := by
    apply hn₁.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,rfl,rfl⟩
    · rintro v ⟨w,rfl,rfl⟩; rfl
  have hlen : blocks.flatten.length = Q*B := blocks_volume ha Q d B payload hwidth
  have hc₀ := CountedSpanReset.reset_word_hoare_linear signMiddle t blocks.flatten B Q A.blockBits A.countBits
    hlen hA.block_value hA.count_value hB hA.block_canonical hA.count_canonical (by simpa only [hlen] using hsblank)
  rw [hlen] at hc₀
  have hclean := span_shared_hoare hc₀ (uo.append sb') (Fin.castAdd 8 i)
    (by simpa [Tapes.append] using hft) (by simpa [Tapes.append] using hfh)
  rw [SignedScalingExecution.setTape_append_left] at hclean
  apply (((hu.seq hr).seq hneg).seq hclean).consequence (fun _ h => h) (fun _ h => h) _
  omega

/-- The positive branch simply retains the unused sign banks as a frame. -/
def positiveInput {a d : ℕ} (ha : 0 < a) (A : Controls a) (D : Controls d) (S : SignControls) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((SignedScalingExecution.unsignedInput ha A D Q source p middle r dest q payload).append
    (signBank S A.blockBits empty 0)).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

def positiveOutput {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d)
    (S : SignControls) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((SignedScalingExecution.unsignedOutput ha hd A D Q B source p middle r dest q payload).append
    (signBank S A.blockBits empty 0)).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

theorem positive_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B)
    (A : Controls a) (D : Controls d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank) :
    HoareTime (positiveProgram ha hd)
      (fun v => v = positiveInput ha A D S Q source p middle r dest q payload)
      (fun v => v = positiveOutput ha hd A D S Q B source p middle r dest q payload)
      (448*(Q*B)+120*(a+d)+200) := by
  have h := ((SignedScalingExecution.unsigned_hoare hQ ha hd hcopA hcopD hB A D hA hD source p middle r
    dest q payload hwidth hblank).extend (signBank S A.blockBits empty 0)).extend
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)
  apply h.consequence _ _ le_rfl
  · rintro v rfl; exact ⟨_,⟨_,rfl,rfl⟩,rfl⟩
  · rintro v ⟨w,⟨x,rfl,rfl⟩,rfl⟩; rfl


def states (a d : ℕ) (negative : Bool) : ℕ :=
  if negative then CoreStates a d+32+202+98 else CoreStates a d

/-- The sign is fixed at compilation, so false performs no sign payload pass. -/
def program {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) :
    Program (TapeCount a d) (states a d negative) 0 :=
  match negative with
  | false => positiveProgram ha hd
  | true => negativeProgram ha hd

def input {a d : ℕ} (ha : 0 < a) (negative : Bool) (A : Controls a) (D : Controls d) (S : SignControls) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  if negative then negativeInput ha A D S Q source p middle r signMiddle t dest q payload
  else positiveInput ha A D S Q source p middle r dest q payload

def output {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) (A : Controls a) (D : Controls d)
    (S : SignControls) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  if negative then negativeOutput ha hd A D S Q B source p middle r signMiddle t dest q payload
  else positiveOutput ha hd A D S Q B source p middle r dest q payload

def bound (Q B a d : ℕ) (negative : Bool) : ℕ :=
  if negative then 852*(Q*B)+120*(a+d)+516 else 448*(Q*B)+120*(a+d)+200

/-- Full signed rational scaling with a compile-time sign and reusable complete
banks. Extra tail descriptors and sign scratch are required only when negative. -/
theorem scaling_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → S.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input ha negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      (bound Q B a d negative) := by
  cases negative
  · exact positive_hoare hQ ha hd hcopA hcopD hB A D S hA hD source p middle r dest q payload hwidth hblank
  · exact negative_hoare hQ ha hd hcopA hcopD hB A D S hA hD (hS rfl)
      source p middle r signMiddle t dest q payload hwidth hblank (hsblank rfl)

/-- Which physical output slot is active is fixed by the compile-time sign. -/
def destinationSlot (a d : ℕ) (negative : Bool) : Fin (TapeCount a d) :=
  if negative then Fin.castAdd 5 (Fin.natAdd (SignedScalingExecution.TapeCount a d) (1 : Fin 8))
  else Fin.castAdd 5 (Fin.castAdd 8 (SignedScalingExecution.destinationSlot a d))

/-- The exact physical destination is the signed rational block recipe used by
the affine semantic theorem, with no payload-order convention left implicit. -/
theorem output_tape {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcop : a.Coprime Q) (negative : Bool) (A : Controls a) (D : Controls d) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (output ha hd negative A D S Q B source p middle r signMiddle t dest q payload).tape
      (destinationSlot a d negative) =
      putWord dest q (ScalingAffineBridge.signedBlocks ha Q d negative payload).flatten := by
  rw [← signed_blocks hQ ha hcop d negative payload]
  cases negative
  · simp only [output,destinationSlot,Bool.false_eq_true,ite_false,positiveOutput,Tapes.append,
      Fin.addCases_left]
    exact SignedScalingExecution.unsigned_output_tape ha hd A D Q B source p middle r dest q payload
  · simp [output,destinationSlot,negativeOutput,Tapes.append,signBank,BlockNegationReuse.bank]

/-- The additional shared intermediate is restored completely after negation. -/
theorem negative_output_middle {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d)
    (S : SignControls) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    let v := negativeOutput ha hd A D S Q B source p middle r signMiddle t dest q payload
    let slot := Fin.castAdd 5 (coreSlot a d)
    v.tape slot = signMiddle ∧ v.head slot = t := by
  simp [negativeOutput,coreSlot,Tapes.append,setTape]

theorem tapeCount_eq (a d : ℕ) : TapeCount a d = 38+4*(a+d) := by
  dsimp only [TapeCount]
  rw [SignedScalingExecution.tapeCount_eq]
  omega

theorem stateCount_eq (a d : ℕ) (negative : Bool) :
    states a d negative = 98*(a+d)+(if negative then 545 else 213) := by
  dsimp only [states,CoreStates]
  rw [SignedScalingExecution.unsigned_stateCount_eq]
  cases negative <;> simp

end IntegerMultBounds.Machine.SignedScalingSign
