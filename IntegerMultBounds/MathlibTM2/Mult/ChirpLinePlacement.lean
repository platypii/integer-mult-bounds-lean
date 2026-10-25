module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputPlacement
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardBankPlacement
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixed
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchLayout
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.ChirpRawGatherData

/-! # Static placement for the retained-setup forward line

Reuse the checked 146-tape output arithmetic and 117-tape shared product.
The source and consumer banks occupy 193 separate tapes; raw gathering and
extraction receive disjoint finite ranges. No allocation depends on dimensions.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Spec.SignedRingProduct

def outputTape (i : Fin 146) : Fin 640 := ⟨i.val, by omega⟩
def bankTape (i : Fin 193) : Fin 640 := ⟨176 + i.val, by omega⟩
def productTape (i : Fin 117) : Fin 640 := ⟨369 + i.val, by omega⟩

theorem outputTape_inj : Function.Injective outputTape := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 640 => x.val) h)
theorem bankTape_inj : Function.Injective bankTape := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; simp only [bankTape] at hv; omega
theorem productTape_inj : Function.Injective productTape := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; simp only [productTape] at hv; omega

def output : ChirpOutputLayout 640 where
  cr := outputTape ∘ OutputPlacement.layout.cr
  nr := outputTape ∘ OutputPlacement.layout.nr
  mul := outputTape ∘ OutputPlacement.layout.mul
  bank := outputTape ∘ OutputPlacement.layout.bank
  cr_inj := outputTape_inj.comp OutputPlacement.layout.cr_inj
  nr_inj := outputTape_inj.comp OutputPlacement.layout.nr_inj
  mul_inj := outputTape_inj.comp OutputPlacement.layout.mul_inj
  bank_inj := outputTape_inj.comp OutputPlacement.layout.bank_inj
  cr_mul := fun r i h => OutputPlacement.layout.cr_mul r i (outputTape_inj h)
  nr_mul := fun r i h => OutputPlacement.layout.nr_mul r i (outputTape_inj h)
  bank_cr := fun r i h => OutputPlacement.layout.bank_cr r i (outputTape_inj h)
  bank_nr := fun r i h => OutputPlacement.layout.bank_nr r i (outputTape_inj h)
  bank_mul := fun r i h => OutputPlacement.layout.bank_mul r i (outputTape_inj h)
  link := congrArg outputTape OutputPlacement.layout.link
  input_frame := fun r h => OutputPlacement.layout.input_frame r (outputTape_inj h)

theorem output_cross : output.Cross :=
  fun r s hr h => OutputPlacement.layout_cross r s hr (outputTape_inj h)

def processor (r : CR) : Fin 640 := ⟨146 + (OutputPlacement.code r).val, by have := (OutputPlacement.code r).isLt; omega⟩

theorem processor_inj : Function.Injective processor := by
  intro r s h
  apply OutputPlacement.code_injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [processor] at hv
  omega

theorem processor_mul (r : CR) (i : Fin 64) : processor r ≠ output.mul i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [processor, output, Function.comp_apply, OutputPlacement.layout, OutputPlacement.mul, outputTape] at hv
  omega

def source := bankTape ∘ ForwardBankPlacement.source
def gather := bankTape ∘ ForwardBankPlacement.gather
def convolution := bankTape ∘ ForwardBankPlacement.convolution
def dimensions := bankTape ∘ ForwardBankPlacement.output
def coefficient := bankTape ∘ ForwardBankPlacement.coefficient
def multiplier := bankTape ∘ ForwardBankPlacement.multiplier

def ring := productTape ∘ Fixed.ringReg
def host := productTape ∘ Fixed.hostReg
def setup := productTape ∘ Fixed.setupReg
def batch := productTape ∘ Fixed.batchReg

theorem ringLayout : RpLayout ring host := by
  refine ⟨productTape_inj.comp Fixed.layout.rg_inj, productTape_inj.comp Fixed.layout.ι_inj,
    congrArg productTape Fixed.layout.d0, congrArg productTape Fixed.layout.d1,
    congrArg productTape Fixed.layout.d2, congrArg productTape Fixed.layout.d3, ?_⟩
  exact fun r i hi h => Fixed.layout.priv r i hi (productTape_inj h)

def extraction : CorrelationReg → Fin 640
  | .l => setup .l | .w => setup .w | .batch => batch .records | .src => ring .out
  | .dst => output.cr .xs
  | .triples => 486 | .batchSaved => 487 | .skip => 488 | .savedSkip => 489
  | .m => 490 | .recordSaved => 491 | .recordSymbols => 492 | .acc => 493
  | .current => 494 | .savedSource => 495 | .saved => 496 | .buf => 497 | .tmp => 498

theorem extraction_inj : Function.Injective extraction := by
  intro r s h
  cases r <;> cases s <;>
    simp_all [extraction, setup, batch, ring, output, outputTape, productTape,
      OutputPlacement.layout, OutputPlacement.cr, OutputPlacement.code, Fixed.setupReg,
      Fixed.batchReg, Fixed.ringReg]

theorem batchLayout : ChirpBatchLayout setup ring host extraction
    (batch .records) (batch .recordSaved) (batch .srcX) (batch .srcY)
    (batch .saved) (batch .acc) (batch .buf) (batch .savedBlock) (batch .tmp) := by
  refine ⟨productTape_inj.comp Fixed.setupReg_injective, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    extraction_inj, rfl, rfl, rfl, rfl⟩
  · exact fun s hs r h => Fixed.counts_off s hs r (productTape_inj h)
  · exact fun s hs i h => Fixed.counts_private s hs i (productTape_inj h)
  · simpa only [batch, setup, ring, Function.comp_apply, List.map_cons, List.map_nil] using Fixed.packX_distinct.map productTape_inj
  · simpa only [batch, setup, ring, Function.comp_apply, List.map_cons, List.map_nil] using Fixed.packY_distinct.map productTape_inj
  · intro k hk he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Fixed.packY_off _ (by simp) (productTape_inj he)
  · intro k hk s hs he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Fixed.data_off _ (by simp) s hs (productTape_inj he)

def rawCode : ChirpRawReg → Fin 20
  | .counter i => ⟨i.val, by omega⟩
  | .raw => 5 | .dst => 6 | .extension => 7 | .count => 8 | .saved => 9
  | .control => 10 | .advance => 11 | .acc => 12 | .current => 13 | .savedSource => 14
  | .buf => 15 | .tmp => 16 | .front => 17 | .back => 18 | .expanded => 19

theorem rawCode_inj : Function.Injective rawCode := by
  intro r s h
  have hv := congrArg Fin.val h
  cases r <;> cases s <;> simp_all [rawCode, Fin.ext_iff] <;> omega

def raw (r : ChirpRawReg) : Fin 640 :=
  if r = .dst then processor .xs else ⟨500 + (rawCode r).val, by have := (rawCode r).isLt; omega⟩

theorem raw_inj : Function.Injective raw := by
  intro r s h
  by_cases hr : r = .dst
  · subst r
    by_cases hs : s = .dst
    · exact hs.symm
    · have hv := congrArg Fin.val h
      simp [raw, hs, processor, OutputPlacement.code] at hv
      omega
  · by_cases hs : s = .dst
    · subst s
      have hv := congrArg Fin.val h
      simp [raw, hr, processor, OutputPlacement.code] at hv
      omega
    · apply rawCode_inj
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [raw, ite_eq_right hr, ite_eq_right hs] at hv
      omega

theorem raw_link : raw .dst = processor .xs := by simp [raw]
theorem correlation_link : extraction .dst = output.cr .xs := rfl

/-- Controls generated and erased by the shared correlation call. -/
def correlationDimensions : Fin 7 → Fin 640 := chirpBatchDimensions setup (batch .records) extraction

def correlationEmpty : List (Fin 640) :=
  chirpBatchEmpty setup ring extraction (batch .recordSaved) (batch .saved) (batch .acc)
    (batch .buf) (batch .savedBlock) (batch .tmp)

theorem correlationDimensions_inj : Function.Injective correlationDimensions := by decide +kernel

private theorem checkedDisjoint (xs ys : List (Fin 640))
    (h : xs.all (fun x => !ys.contains x) = true) : List.Disjoint xs ys := by
  rw [List.disjoint_left]
  intro x hx hy
  have hcheck := List.all_eq_true.mp h x hx
  simp [hy] at hcheck

/-- The finite checks inspect only the two structural support lists. -/
theorem empty_dimensions : List.Disjoint correlationEmpty (List.ofFn correlationDimensions) := checkedDisjoint _ _ (by decide +kernel)

theorem empty_operands : List.Disjoint correlationEmpty [batch .srcX, processor .xs] := checkedDisjoint _ _ (by decide +kernel)

theorem dimensions_operands : List.Disjoint (List.ofFn correlationDimensions)
    [batch .srcX, batch .srcY, extraction .dst, processor .xs] := checkedDisjoint _ _ (by decide +kernel)

theorem extraction_operand : ∀ r, extraction r ≠ batch .srcX := by
  intro r
  cases r <;> decide +kernel

theorem private_dimensions (i : Fin 91) (j : Fin 7) : host i ≠ correlationDimensions j := by
  intro h
  have hv := congrArg Fin.val h
  fin_cases j <;>
    simp [host, productTape, Fixed.hostReg, correlationDimensions, chirpBatchDimensions,
      setup, Fixed.setupReg, batch, Fixed.batchReg, extraction] at hv <;> omega

theorem private_operands (i : Fin 91) : host i ≠ batch .srcX ∧ host i ≠ processor .xs := by
  constructor <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp [host, productTape, Fixed.hostReg, batch, Fixed.batchReg, processor, OutputPlacement.code] at hv
    omega

theorem bank_range (i : Fin 193) : 176 ≤ (bankTape i).val ∧ (bankTape i).val < 369 := by
  simp only [bankTape]
  omega

theorem processor_range (r : CR) : 146 ≤ (processor r).val ∧ (processor r).val < 176 := by
  have := (OutputPlacement.code r).isLt
  simp only [processor]
  omega

/-- Every table bank is separate from the raw gather's destination and private work. -/
theorem bank_raw (i : Fin 193) (r : ChirpRawReg) : bankTape i ≠ raw r := by
  intro h
  have hv := congrArg Fin.val h
  have hb := bank_range i
  by_cases hr : r = .dst
  · subst r
    rw [raw_link] at h
    have hp := processor_range .xs
    have hv := congrArg Fin.val h
    omega
  · simp only [raw, ite_eq_right hr] at hv
    omega

theorem gather_inj : Function.Injective gather := bankTape_inj.comp (ForwardBankPlacement.place_injective _ (by decide))
theorem convolution_inj : Function.Injective convolution := bankTape_inj.comp (ForwardBankPlacement.place_injective _ (by decide))
theorem source_inj : Function.Injective source := bankTape_inj.comp ForwardBankPlacement.source_injective

theorem gather_raw : ∀ r b, gather b ≠ raw r := fun r _ => bank_raw _ r

theorem dimensions_source : ∀ r, convolution r ≠ batch .srcX := by
  intro r h
  have hv := congrArg Fin.val h
  have hb := bank_range (ForwardBankPlacement.convolution r)
  change (bankTape (ForwardBankPlacement.convolution r)).val = _ at hv
  simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv
  omega

theorem dimensions_input : ∀ r, convolution r ≠ processor .xs := by
  intro r h
  have hv := congrArg Fin.val h
  have hb := bank_range (ForwardBankPlacement.convolution r)
  have hp := processor_range .xs
  change (bankTape (ForwardBankPlacement.convolution r)).val = _ at hv
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
