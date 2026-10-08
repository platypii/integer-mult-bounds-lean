import IntegerMultBounds.Machine.RecursiveScalingDimensions
import IntegerMultBounds.Machine.RecursiveScalingInstall

/-! Physical heterogeneous H/D scaling from six canonical original headers and
one flat payload: construct all dimensions, install descriptors, then scale and
normalize the same source/scratch pair. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeScalingConstruct
open Networks
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Target view prefixSize suffix)
open RecursiveScalingInstall (LocalTapes)
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
noncomputable section
private theorem hprime : 2 ≤ prime := Shared50ModularControl.prime_prime.two_le

abbrev blockBits (v : Descriptor) (hs : Fin 6 → List Bool) (t : Target) :=
  RecursiveScalingDimensions.blockBits (q := prime) v hs t
abbrev countBits (v : Descriptor) := RecursiveDimensionBank.qBits hprime v
abbrev prefixBits (v : Descriptor) (t : Target) := RecursiveScalingDimensions.prefixBits (q := prime) v t

private def source {v : Descriptor} (a : Fin (volume prime v) → Fin 4) (t : Target) : ℤ → Fin 4 :=
  putWord (fun _ => blank) 0 (List.ofFn (view a t))

def workspace {v : Descriptor} {r : ℚ} (a : Fin (volume prime v) → Fin 4) (t : Target) :=
  RecursiveScalingInstall.liftedBank prime r.num.natAbs r.den (source a t) [] [] []

def input {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :=
  (RecursiveScalingDimensions.input hs).append (workspace (r := r) a t)

theorem input_target {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t u : Target) :
    input (r := r) hs a t = input (r := r) hs a u := by
  unfold input workspace source
  rw [RecursiveInterchangeScaling.view_word,RecursiveInterchangeScaling.view_word]

def output {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :=
  (RecursiveScalingDimensions.output hprime hs v t).append
    (RecursiveInterchangeScaling.output hr a t (blockBits v hs t) (countBits v) (prefixBits v t))

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Target) :=
  seq (seq (extend (RecursiveScalingDimensions.program hprime t) (LocalTapes r.num.natAbs r.den))
    (RecursiveScalingInstall.program t prime r.num.natAbs r.den))
    (Placement.placed (RecursiveInterchangeScaling.program hr) finAddFlip)

private theorem left_frame {n s q radix k : ℕ} {M : Program n s radix} {x y : Tapes n radix}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes q radix) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n radix) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

private theorem dimensions_ready (v : Descriptor) (hs : Fin 6 → List Bool) (t : Target)
    (k : FlatAffineScalingInputLayout.Kind) :
    (RecursiveScalingDimensions.output hprime hs v t).head (RecursiveScalingInstall.sourceSlot t k) = 1 ∧
    (RecursiveScalingDimensions.output hprime hs v t).tape (RecursiveScalingInstall.sourceSlot t k) =
      RadixZeroFill.encodedBinary
        (RecursiveScalingInstall.sourceWords t (blockBits v hs t) (countBits v) (prefixBits v t)
          (RecursiveScalingInstall.sourceSlot t k)) := by
  cases t <;> cases k <;> exact ⟨rfl,rfl⟩

theorem dimensions (v : Descriptor) (hs : Fin 6 → List Bool) (t : Target)
    (hv : RecursiveDimensionBank.Headers v hs) :
    Counter.value (blockBits v hs t) = suffix v t ∧
    Counter.value (countBits v) = modulus v.width ∧
    Counter.value (prefixBits v t) = prefixSize v t ∧
    GrowingCounterData.Canonical (blockBits v hs t) ∧
    GrowingCounterData.Canonical (countBits v) ∧
    GrowingCounterData.Canonical (prefixBits v t) := by
  have hb : Counter.value (blockBits v hs t) = suffix v t := by
    cases t
    · simp [blockBits,RecursiveScalingDimensions.blockBits,RecursiveScalingDimensions.cqeBits,
        DimensionProductDescriptor.bits_value,suffix,modulus,Nat.mul_assoc]
    · exact hv.1 5
  have hp : Counter.value (prefixBits v t) = prefixSize v t := by
    cases t <;> exact DimensionProductDescriptor.bits_value _ _
  have cb : GrowingCounterData.Canonical (blockBits v hs t) := by
    cases t
    · exact DimensionProductDescriptor.bits_canonical _ _
    · exact hv.2 5
  have cp : GrowingCounterData.Canonical (prefixBits v t) := by
    cases t <;> exact DimensionProductDescriptor.bits_canonical _ _
  exact ⟨hb,RadixPowerDescriptor.bits_value _ _,hp,cb,RadixPowerDescriptor.bits_canonical _ _,cp⟩

theorem dimension_lengths (v : Descriptor) (hs : Fin 6 → List Bool) (t : Target)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    (blockBits v hs t).length ≤ 2*volume prime v ∧
    (countBits v).length ≤ 2*volume prime v ∧
    (prefixBits v t).length ≤ 2*volume prime v := by
  obtain ⟨hb,hq,hp,cb,cq,cp⟩ := dimensions v hs t hv
  have hQ := ActualAffineScaling.modulus_pos v.width
  have hP : 0 < prefixSize v t := by
    rcases hvpos with ⟨ha,hr,hb,hc,he⟩
    cases t <;> simp only [prefixSize] <;> positivity
  have hB : 0 < suffix v t := by
    rcases hvpos with ⟨ha,hr,hb,hc,he⟩
    cases t <;> simp only [suffix] <;> positivity
  have hV : 0 < volume prime v := by
    rw [RecursiveInterchangeScaling.split_volume v t]
    positivity
  have bound (xs : List Bool) (hc : GrowingCounterData.Canonical xs) (hx : Counter.value xs ≤ volume prime v) :
      xs.length ≤ 2*volume prime v := by
    have hw := GrowingCounterData.canonical_width xs hc
    have hl := Nat.log2_le_self (Counter.value xs)
    omega
  refine ⟨bound _ cb ?_,bound _ cq ?_,bound _ cp ?_⟩
  · rw [hb,RecursiveInterchangeScaling.split_volume v t]
    exact (Nat.le_mul_of_pos_left _ hQ).trans (Nat.le_mul_of_pos_left _ hP)
  · rw [hq,RecursiveInterchangeScaling.split_volume v t]
    exact (Nat.le_mul_of_pos_right _ hB).trans (Nat.le_mul_of_pos_left _ hP)
  · rw [hp,RecursiveInterchangeScaling.split_volume v t]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ hB)

/-- The complete program consumes only original layout headers and payload. -/
theorem constructs_hoare {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hr t) (fun w => w = input (r := r) hs a t)
      (fun w => w = output hr hs a t)
      ((2428+120*(r.num.natAbs+r.den)+22*LocalTapes r.num.natAbs r.den)*volume prime v+401) := by
  have hd := hoare_extend_eq (RecursiveScalingDimensions.constructs_hoare hprime v hs t hv hvpos)
    (workspace (r := r) a t)
  have hi := RecursiveScalingInstall.installs_hoare t prime r.num.natAbs r.den
    (RecursiveScalingDimensions.output hprime hs v t) (source a t)
    (blockBits v hs t) (countBits v) (prefixBits v t) (dimensions_ready v hs t)
  have hin : RecursiveScalingInstall.liftedBank prime r.num.natAbs r.den (source a t)
      (blockBits v hs t) (countBits v) (prefixBits v t) =
      RecursiveInterchangeScaling.input hr a t (blockBits v hs t) (countBits v) (prefixBits v t) :=
    (FlatAffineScalingInputLayout.payload_input hr (view a t) _ _ _).symm
  rw [hin] at hi
  obtain ⟨hb,hq,hp,cb,cq,cp⟩ := dimensions v hs t hv
  have he := RecursiveInterchangeScaling.realizes_hoare hr a t hvpos _ _ _ hb hq hp cb cq cp
  have hh := (hd.seq hi).seq (left_frame he (RecursiveScalingDimensions.output hprime hs v t))
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  have hV : 0 < volume prime v := by
    rcases hvpos with ⟨ha,hr,hb,hc,he⟩
    unfold volume
    have := ActualAffineScaling.modulus_pos v.width
    change 0 < v.beforeRows*v.rows*v.beforeH*modulus v.width*v.between*modulus v.width*v.afterD
    positivity
  obtain ⟨hbl,hql,hpl⟩ := dimension_lengths v hs t hv hvpos
  have hc := RecursiveScalingInstall.cost_volume t r.num.natAbs r.den (2*volume prime v)
    (blockBits v hs t) (countBits v) (prefixBits v t) (by omega) hbl hql hpl
  nlinarith

abbrev TapeCount (r : ℚ) := RecursiveScalingInstall.TapeCount r.num.natAbs r.den
def sourceSlot (r : ℚ) : Fin (TapeCount r) := Fin.natAdd 16 (FlatAffineScaling.sourceSlot r)
def destSlot (r : ℚ) : Fin (TapeCount r) := Fin.natAdd 16 (ActualAffineScalingStream.destinationSlot r)
def headerSlot (r : ℚ) (j : Fin 6) : Fin (TapeCount r) :=
  Fin.castAdd _ (Fin.castAdd 3 (Fin.castAdd 4 (Fin.natAdd 3 j)))

theorem input_payload {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :
    SharedPayload.payload (input (r := r) hs a t) (sourceSlot r) (destSlot r) =
      FlatAffineScalingPayload.pair a := by
  have hw : workspace (r := r) a t = RecursiveInterchangeScaling.input hr a t [] [] [] :=
    (FlatAffineScalingInputLayout.payload_input hr (view a t) [] [] []).symm
  simpa only [input,sourceSlot,destSlot,SharedPayload.payload,Tapes.append,Fin.addCases_right,hw] using
    RecursiveInterchangeScaling.input_payload hr a t [] [] []

theorem output_payload {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :
    SharedPayload.payload (output hr hs a t) (sourceSlot r) (destSlot r) =
      FlatAffineScalingPayload.pair (RecursiveInterchangeScaling.array hr a t) := by
  simpa only [output,sourceSlot,destSlot,SharedPayload.payload,Tapes.append,Fin.addCases_right] using
    RecursiveInterchangeScaling.output_payload hr a t (blockBits v hs t) (countBits v) (prefixBits v t)

theorem input_header {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (j : Fin 6) :
    (input (r := r) hs a t).head (headerSlot r j) = 1 ∧
    (input (r := r) hs a t).tape (headerSlot r j) = RadixZeroFill.encodedBinary (hs j) := by
  unfold input RecursiveScalingDimensions.input RecursiveScalingDimensions.bank headerSlot
  simp only [Tapes.append,Fin.addCases_left]
  exact RecursiveDimensionBank.headers_preserved hs _ j

theorem headers_preserved {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) (j : Fin 6) :
    (output hr hs a t).head (headerSlot r j) = 1 ∧
    (output hr hs a t).tape (headerSlot r j) = RadixZeroFill.encodedBinary (hs j) := by
  unfold output RecursiveScalingDimensions.output RecursiveScalingDimensions.bank headerSlot
  simp only [Tapes.append,Fin.addCases_left]
  exact RecursiveDimensionBank.headers_preserved hs _ j

/-- All local tapes other than the payload are genuinely blank before setup. -/
theorem input_workspace_blank {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (i : Fin (LocalTapes r.num.natAbs r.den))
    (hi : FlatAffineScalingInputLayout.kinds r.num.natAbs r.den i ≠ .payload) :
    (input (r := r) hs a t).head (Fin.natAdd 16 i) = 0 ∧
    (input (r := r) hs a t).tape (Fin.natAdd 16 i) = fun _ => blank := by
  simp only [input,Tapes.append,Fin.addCases_right]
  constructor
  · rfl
  · unfold workspace RecursiveScalingInstall.liftedBank Alphabet.mapTapes FlatAffineScalingInputLayout.bank
    dsimp only
    funext z
    cases hk : FlatAffineScalingInputLayout.kinds r.num.natAbs r.den i
    all_goals first
      | exact (hi hk).elim
      | (by_cases hz : z = 0 <;>
          simp [FlatAffineScalingInputLayout.word,BinaryDescriptorInstallRaw.rawWord,
            RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding,CountedCopyReuse.binary,
            CountedCopyReuse.empty,putBits,hz,blank])

theorem input_dimension_blank {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (i : Fin 16)
    (hi : ¬ (3 ≤ i.val ∧ i.val < 9)) :
    (input (r := r) hs a t).head (Fin.castAdd _ i) = 0 ∧
    (input (r := r) hs a t).tape (Fin.castAdd _ i) = fun _ => blank := by
  simp only [input,Tapes.append,Fin.addCases_left]
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | (exfalso; exact hi (by decide))

theorem constructs_array {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hr t) (fun w => w = input (r := r) hs a t)
      (fun w => w = output hr hs a t ∧
        SharedPayload.payload w (sourceSlot r) (destSlot r) =
          FlatAffineScalingPayload.pair (RecursiveInterchangeScaling.array hr a t) ∧
        ∀ x : RecursiveInterchangeScaling.Address v,
          RecursiveInterchangeScaling.array hr a t
            (RecursiveInterchangeScaling.index (RecursiveInterchangeScaling.scaleAddress r x t)) =
              a (RecursiveInterchangeScaling.index x))
      ((2428+120*(r.num.natAbs+r.den)+22*LocalTapes r.num.natAbs r.den)*volume prime v+401) := by
  apply (constructs_hoare hr hs a t hv hvpos).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,output_payload hr hs a t,RecursiveInterchangeScaling.array_entry hr a t⟩

end
end IntegerMultBounds.Machine.RecursiveInterchangeScalingConstruct
