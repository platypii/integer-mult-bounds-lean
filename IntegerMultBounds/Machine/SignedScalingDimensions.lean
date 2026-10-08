import IntegerMultBounds.Machine.SignedScalingPrepared
import IntegerMultBounds.Machine.NegationDescriptors

/-! Signed rational scaling from canonical Q/B descriptors. A literal bootstrap
writes its own one and derives canonical negation-tail metadata; the two piece
families are then synthesized by the prepared signed executor. Every descriptor
handoff is fixed transition-table wiring, with generated metadata retained. -/
namespace IntegerMultBounds.Machine.SignedScalingDimensions

open CountedCopyReuse (empty binary)
open SignedScalingPrepared (Setup)
open SignedScalingSign (SignControls)

/-- Negation scratch needs an origin/background, but no supplied tail counts. -/
structure Scratch where
  tape : ℤ → Fin 4
  origin : ℤ

def generated (S : Scratch) (Q B : ℕ) : SignControls where
  scratch := S.tape
  origin := S.origin
  tailBits := NegationDescriptors.tailVolume Q B
  tailCountBits := NegationDescriptors.tailCount Q

theorem generated_valid (S : Scratch) (Q B : ℕ)
    (hblank : ∀ z, S.origin ≤ z → z < S.origin+(((Q-1)*B : ℕ) : ℤ) → S.tape z = blank) :
    (generated S Q B).Valid Q B :=
  ⟨NegationDescriptors.tailVolume_value Q B,NegationDescriptors.tailCount_value Q,
    NegationDescriptors.tailVolume_canonical Q B,NegationDescriptors.tailCount_canonical Q,hblank⟩

/-- Active sign slots 5 and 7 are the actual synthesized slots 1 and 10. -/
def signPlacement : Fin (8+9) ≃ Fin (11+6) where
  toFun := ![11,12,13,14,15,1,16,10,0,2,3,4,5,6,7,8,9]
  invFun := ![8,5,9,10,11,12,13,14,15,16,7,0,1,2,3,4,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def signFrame (S : Scratch) (bs : List Bool) (dest : ℤ → Fin 4) (q : ℤ) : Tapes 6 0 :=
  ⟨![0,q,S.origin,1,1,1],![empty,dest,S.tape,empty,binary bs,empty]⟩

def ready (Q B : ℕ) (bs qs : List Bool) : Tapes 11 0 :=
  NegationDescriptors.bank (TranslationDescriptors.descriptors Q 1 B) bs qs
    (BinarySubReuse.difference qs [true]) (NegationDescriptors.tailCount Q)

/-- Other generated lengths, padded difference and fixed one are retained. -/
def metadata (Q B : ℕ) (bs qs : List Bool) : Tapes 9 0 :=
  ⟨fun i => (ready Q B bs qs).head (![0,2,3,4,5,6,7,8,9] i),
   fun i => (ready Q B bs qs).tape (![0,2,3,4,5,6,7,8,9] i)⟩

private theorem sign_handoff (S : Scratch) (Q B : ℕ) (bs qs : List Bool) (dest : ℤ → Fin 4) (q : ℤ) :
    (ready Q B bs qs).append (signFrame S bs dest q) =
      Placement.combine signPlacement (SignedScalingSign.signBank (generated S Q B) bs dest q) (metadata Q B bs qs) := by
  have ha : Placement.active signPlacement ((ready Q B bs qs).append (signFrame S bs dest q)) =
      SignedScalingSign.signBank (generated S Q B) bs dest q := by
    unfold Placement.active signPlacement
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra signPlacement ((ready Q B bs qs).append (signFrame S bs dest q)) = metadata Q B bs qs := by
    unfold Placement.extra signPlacement
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  simpa only [ha,he] using (Placement.view signPlacement ((ready Q B bs qs).append (signFrame S bs dest q))).symm

/-- Preserve a whole active prefix while placing a following bank. -/
private def withLeft {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t) : Fin ((r+s)+u) ≃ Fin (r+t) where
  toFun := Fin.addCases (Fin.addCases (Fin.castAdd t) (fun i => Fin.natAdd r (e (Fin.castAdd u i))))
    (fun i => Fin.natAdd r (e (Fin.natAdd s i)))
  invFun := Fin.addCases (fun i => Fin.castAdd u (Fin.castAdd s i))
    (fun i => Fin.addCases (fun j => Fin.castAdd u (Fin.natAdd r j)) (Fin.natAdd (r+s)) (e.symm i))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i => obtain ⟨j,rfl⟩ := e.surjective i; induction j using Fin.addCases <;> simp

private theorem combine_left {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t)
    (x : Tapes r 0) (y : Tapes s 0) (a : Tapes u 0) :
    Placement.combine (withLeft e) (x.append y) a = x.append (Placement.combine e y a) := by
  have ha : Placement.active (withLeft e) (x.append (Placement.combine e y a)) = x.append y := by
    unfold Placement.active withLeft
    congr 1 <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,Placement.combine,Tapes.reindex]
  have he : Placement.extra (withLeft e) (x.append (Placement.combine e y a)) = a := by
    unfold Placement.extra withLeft
    congr 1 <;> funext i <;> simp [Tapes.append,Placement.combine,Tapes.reindex]
  simpa only [ha,he] using Placement.view (withLeft e) (x.append (Placement.combine e y a))

abbrev FrontTapes (a d : ℕ) := ScalingPreparedExecution.TapeCount a+ScalingPreparedExecution.TapeCount d+5
abbrev TapeCount (a d : ℕ) := (FrontTapes a d+(11+6))+5

def executionPlacement (a d : ℕ) : Fin (SignedScalingPrepared.TapeCount a d+9) ≃ Fin (TapeCount a d) :=
  FamilyPlacement.withFrame (withLeft (r := FrontTapes a d) signPlacement)

private def coefficientInput {c : ℕ} (C : Setup c) (f : ℤ → Fin 4) (p : ℤ) (left : Tapes 2 0) :
    Tapes (ScalingPreparedExecution.TapeCount c) 0 :=
  (ScalingDescriptors.initial C.blockBits C.countBits C.modulus C.current).append
    (((CountedCopyReuse.bank f (fun _ => blank) empty (fun _ => blank) p 0 1 0).append
      (⟨C.origins,C.background⟩ : Tapes c 0)).append left)

private def front {a d : ℕ} (negative : Bool) (A : Setup a) (D : Setup d) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (FrontTapes a d) 0 :=
  ((coefficientInput A (putWord source p (ScalingExecution.inputWord Q payload)) p (CountedLoopReuse.controls empty middle 0 r)).append
    (coefficientInput D (if negative then signMiddle else dest) (if negative then t else q)
      (CountedLoopReuse.controls empty empty 0 0))).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

private def selectedFrame (negative : Bool) (S : Scratch) (bs : List Bool) (dest : ℤ → Fin 4) (q : ℤ) : Tapes 6 0 :=
  signFrame S bs (if negative then dest else empty) (if negative then q else 0)

/-- All derived sign lengths and their helper constant start blank. The only
variable supplied descriptors are canonical Q/B; fixed inherited sentinels are
explicit in the coefficient/sign frame and no new sentinel is assumed. -/
def input {a d : ℕ} (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((front negative A D Q source p middle r signMiddle t dest q payload).append
    ((NegationDescriptors.initial A.blockBits A.countBits).append (selectedFrame negative S A.blockBits dest q))).append
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

private theorem handoff {a d : ℕ} (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    ((front negative A D Q source p middle r signMiddle t dest q payload).append
      ((ready Q B A.blockBits A.countBits).append (selectedFrame negative S A.blockBits dest q))).append
      (CountedSpanSeek.bank empty 0 A.blockBits A.countBits) =
    Placement.combine (executionPlacement a d)
      (SignedScalingPrepared.input negative A D (generated S Q B) Q source p middle r signMiddle t dest q payload)
      (metadata Q B A.blockBits A.countBits) := by
  unfold executionPlacement SignedScalingPrepared.input
  rw [FamilyPlacement.combine_withFrame,combine_left]
  cases negative <;> simp only [selectedFrame,Bool.false_eq_true,ite_false,ite_true]
  · rw [sign_handoff]
    rfl
  · rw [sign_handoff]
    rfl

private theorem leftFrame_hoare {s q r : ℕ} {M : Program s q 0} {v w : Tapes s 0} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (frame : Tapes r 0) :
    HoareTime (Placement.placed M (finAddFlip : Fin (s+r) ≃ Fin (r+s)))
      (fun x => x = frame.append v) (fun x => x = frame.append w) cost := by
  let e : Fin (s+r) ≃ Fin (r+s) := finAddFlip
  have ha (x : Tapes s 0) : Placement.active e (frame.append x) = x := by
    cases x; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
  have he (x : Tapes s 0) : Placement.extra e (frame.append x) = frame := by
    cases frame; simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
  apply (Placement.hoare_at h e (frame.append v) (ha v)).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  rw [Placement.replace,he]
  simpa only [ha,he] using Placement.view e (frame.append w)

private def bootstrapProgram (a d : ℕ) : Program (TapeCount a d) 160 0 :=
  extend (Placement.placed (extend NegationDescriptors.program 6)
    (finAddFlip : Fin ((11+6)+FrontTapes a d) ≃ Fin (FrontTapes a d+(11+6)))) 5

private theorem bootstrap_hoare {Q a d B : ℕ} (hQ : 0 < Q) (hB : 0 < B)
    (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch) (hA : A.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    HoareTime (bootstrapProgram a d)
      (fun v => v = input negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = Placement.combine (executionPlacement a d)
        (SignedScalingPrepared.input negative A D (generated S Q B) Q source p middle r signMiddle t dest q payload)
        (metadata Q B A.blockBits A.countBits)) (216*(Q*B)+121) := by
  have h := FamilyPlacement.extend_hoare (leftFrame_hoare
    (FamilyPlacement.extend_hoare (NegationDescriptors.descriptors_hoare Q B hQ hB A.blockBits A.countBits
      hA.block_value hA.count_value hA.block_canonical hA.count_canonical)
      (selectedFrame negative S A.blockBits dest q))
    (front negative A D Q source p middle r signMiddle t dest q payload))
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact handoff negative A D S Q B source p middle r signMiddle t dest q payload

open ScalingPreparedExecution (SynthesisStates)

def program {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) :
    Program (TapeCount a d) (160+(SynthesisStates a+SynthesisStates d+SignedScalingSign.states a d negative)) 0 :=
  seq (bootstrapProgram a d)
    (Placement.placed (SignedScalingPrepared.program ha hd negative) (executionPlacement a d))

def output {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  Placement.combine (executionPlacement a d)
    (SignedScalingPrepared.output ha hd negative A D (generated S Q B) Q B source p middle r signMiddle t dest q payload)
    (metadata Q B A.blockBits A.countBits)

/-- The complete signed transform now starts with dimensions only. Tail and
coefficient-piece descriptors are physically synthesized, and every join and
initialization transition is charged. -/
theorem scaling_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → ∀ z, S.origin ≤ z → z < S.origin+(((Q-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      (SignedScalingSign.bound Q B a d negative+356*(Q*B)+226) := by
  let before := SignedScalingPrepared.input negative A D (generated S Q B) Q source p middle r signMiddle t dest q payload
  let saved :=  metadata Q B A.blockBits A.countBits
  have he := Placement.hoare_at
    (SignedScalingPrepared.scaling_hoare hQ ha hd hcopA hcopD hB negative A D (generated S Q B) hA hD
      (fun hn => generated_valid S Q B (hS hn)) source p middle r signMiddle t dest q payload hwidth hblank hsblank)
    (executionPlacement a d) (Placement.combine (executionPlacement a d) before saved) (Placement.active_combine _ _ _)
  have he' : HoareTime (Placement.placed (SignedScalingPrepared.program ha hd negative) (executionPlacement a d))
      (fun v => v = Placement.combine (executionPlacement a d) before saved)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      (SignedScalingSign.bound Q B a d negative+140*(Q*B)+104) := by
    apply he.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    simp only [Placement.replace,Placement.extra_combine]
    rfl
  have h := (bootstrap_hoare hQ hB negative A D S hA source p middle r signMiddle t dest q payload).seq he'
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Absorb fixed coefficient work and all initialization into payload volume. -/
theorem linear_bound (Q B a d : ℕ) (negative : Bool) (hQ : 0 < Q) (hB : 0 < B) :
    SignedScalingSign.bound Q B a d negative+356*(Q*B)+226 ≤ (1950+120*(a+d))*(Q*B) := by
  have hv : 1 ≤ Q*B := by nlinarith
  have hm := Nat.mul_le_mul_left (120*(a+d)+742) hv
  unfold SignedScalingSign.bound
  split_ifs <;> nlinarith

theorem scaling_hoare_linear {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → ∀ z, S.origin ≤ z → z < S.origin+(((Q-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      ((1950+120*(a+d))*(Q*B)) :=
  (scaling_hoare hQ ha hd hcopA hcopD hB negative A D S hA hD hS source p middle r signMiddle t dest q
    payload hwidth hblank hsblank).consequence (fun _ h => h) (fun _ h => h) (linear_bound Q B a d negative hQ hB)

def destinationSlot (a d : ℕ) (negative : Bool) : Fin (TapeCount a d) :=
  executionPlacement a d (Fin.castAdd 9 (SignedScalingPrepared.destinationSlot a d negative))

theorem output_tape {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcop : a.Coprime Q) (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (output ha hd negative A D S Q B source p middle r signMiddle t dest q payload).tape
      (destinationSlot a d negative) =
      putWord dest q (ScalingAffineBridge.signedBlocks ha Q d negative payload).flatten := by
  rw [output,destinationSlot,Placement.combine_tape_active]
  exact SignedScalingPrepared.output_tape hQ ha hd hcop negative A D (generated S Q B)
    source p middle r signMiddle t dest q payload

theorem output_metadata {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    Placement.extra (executionPlacement a d)
      (output ha hd negative A D S Q B source p middle r signMiddle t dest q payload) =
      metadata Q B A.blockBits A.countBits := Placement.extra_combine _ _ _

/-- The extra negation scratch tape is restored, including its head. -/
def scratchSlot (a d : ℕ) : Fin (TapeCount a d) :=
  executionPlacement a d (Fin.castAdd 9 (SignedScalingPrepared.executionPlacement a d
    (Fin.castAdd 2 (Fin.castAdd 5 (Fin.natAdd (SignedScalingExecution.TapeCount a d) (2 : Fin 8))))))

theorem output_scratch {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    let v := output ha hd negative A D S Q B source p middle r signMiddle t dest q payload
    v.tape (scratchSlot a d) = S.tape ∧ v.head (scratchSlot a d) = S.origin := by
  dsimp only
  simp only [output,scratchSlot,Placement.combine_tape_active,Placement.combine_head_active,
    SignedScalingPrepared.output]
  cases negative <;> simp [SignedScalingSign.output,SignedScalingSign.negativeOutput,
    SignedScalingSign.positiveOutput,Tapes.append,SignedScalingSign.signBank,BlockNegationReuse.bank,generated]

theorem tapeCount_eq (a d : ℕ) : TapeCount a d = 49+4*(a+d) := by
  dsimp only [TapeCount,FrontTapes]
  rw [ScalingPreparedExecution.tapeCount_eq,ScalingPreparedExecution.tapeCount_eq]
  omega

theorem stateCount_eq (a d : ℕ) (negative : Bool) :
    160+(SynthesisStates a+SynthesisStates d+SignedScalingSign.states a d negative) =
      117*(a+d)+(if negative then 787 else 455) := by
  rw [SignedScalingPrepared.stateCount_eq]
  cases negative <;> simp <;> omega

end IntegerMultBounds.Machine.SignedScalingDimensions
