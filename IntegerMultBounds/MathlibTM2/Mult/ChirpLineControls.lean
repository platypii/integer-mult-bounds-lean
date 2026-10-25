module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLinePlacement

/-! # Remaining producer and control separation for the fixed forward line -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Spec.SignedRingProduct

def producer (i : Fin 11) : Fin 640 := ⟨521 + i.val, by omega⟩
def producerCounters : Fin 3 → Fin 640 := ![producer 0, producer 2, producer 4]
def wordCounter : Fin 640 := coefficient .wn

def producerSupport : List (Fin 640) :=
  [batch .srcX, wordCounter, producer 0, producer 2, producer 4, producer 1,
    producer 5, producer 7, producer 3, producer 6, producer 8, producer 9, producer 10]

theorem producer_registers :
    [batch .srcX, producer 0, producer 1, producer 2, producer 3, wordCounter,
      producer 4, processor .out, producer 5, producer 6, producer 7, producer 8,
      producer 9, producer 10].Nodup := by decide +kernel

theorem producer_input : ∀ k ∈ producerSupport, k ≠ processor .xs := by
  intro k hk he
  subst k
  have hn : processor .xs ∉ producerSupport := by decide +kernel
  exact hn hk

theorem producer_counter_range (i : Fin 3) : 521 ≤ (producerCounters i).val := by
  fin_cases i <;> simp [producerCounters, producer]

theorem gather_counters (i : Fin 3) (r : TblR 10) : gather r ≠ producerCounters i := by
  intro h
  have hb := bank_range (ForwardBankPlacement.gather r)
  have hc := producer_counter_range i
  have hv := congrArg Fin.val h
  change (bankTape (ForwardBankPlacement.gather r)).val = _ at hv
  omega

theorem processor_counters (i : Fin 3) (r : CR) : processor r ≠ producerCounters i := by
  intro h
  have hb := processor_range r
  have hc := producer_counter_range i
  have hv := congrArg Fin.val h
  omega

theorem multiplier_counters (i : Fin 3) (r : Fin 64) : output.mul r ≠ producerCounters i := by
  intro h
  have hc := producer_counter_range i
  have hv := congrArg Fin.val h
  simp only [output, Function.comp_apply, OutputPlacement.layout, OutputPlacement.mul, outputTape] at hv
  omega

theorem dimensions_bank (i : Fin 7) (r : TblR 10) : convolution r ≠ correlationDimensions i := by
  intro h
  have hb := bank_range (ForwardBankPlacement.convolution r)
  have hv := congrArg Fin.val h
  change (bankTape (ForwardBankPlacement.convolution r)).val = _ at hv
  fin_cases i <;>
    simp [correlationDimensions, chirpBatchDimensions, setup, batch, extraction,
      Function.comp_apply, Fixed.setupReg, Fixed.batchReg, productTape] at hv <;> omega

theorem dimensions_operand (i : Fin 7) :
    batch .srcX ≠ correlationDimensions i ∧ batch .srcY ≠ correlationDimensions i ∧
      extraction .dst ≠ correlationDimensions i ∧ correlationDimensions i ≠ processor .xs := by
  have hd := List.disjoint_left.mp dimensions_operands
  have hi : correlationDimensions i ∈ List.ofFn correlationDimensions := List.mem_ofFn.mpr ⟨i, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact hd hi (by simp [← h])
  · intro h; exact hd hi (by simp [← h])
  · intro h; exact hd hi (by simp [← h])
  · intro h; exact hd hi (by simp [h])

theorem workspace_dimensions (k : Fin 640) (hk : k ∈ correlationEmpty) (i : Fin 7) :
    k ≠ correlationDimensions i := by
  intro h
  exact List.disjoint_left.mp empty_dimensions hk (List.mem_ofFn.mpr ⟨i, h.symm⟩)

theorem workspace_operands (k : Fin 640) (hk : k ∈ correlationEmpty) :
    k ≠ batch .srcX ∧ k ≠ processor .xs := by
  have hd := List.disjoint_left.mp empty_operands hk
  constructor <;> intro h <;> exact hd (by simp [h])

theorem kernel_operand : batch .srcY ≠ batch .srcX := by decide +kernel
theorem output_input : extraction .dst ≠ processor .xs := by decide +kernel
theorem kernel_input : batch .srcY ≠ processor .xs := by decide +kernel

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
