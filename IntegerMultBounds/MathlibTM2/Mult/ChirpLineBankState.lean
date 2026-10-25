module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardRawSetup

/-! # Read the fixed line's consumer interfaces from the computed source bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

def liftConsumer (b : ChirpBankTarget 16 193) : ChirpBankTarget 16 640 :=
  ⟨b.vars, bankTape ∘ b.rg, b.index⟩

def consumers : List (ChirpBankTarget 16 640) := ForwardBankPlacement.consumers.map liftConsumer

theorem consumers_eq : consumers = chirpForwardConsumers gather convolution dimensions coefficient multiplier := rfl

theorem consumers_inj : ∀ b ∈ consumers, Function.Injective b.rg := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact bankTape_inj.comp (ForwardBankPlacement.consumers_injective c hc)

theorem consumers_source : ∀ b ∈ consumers, ∀ r s, b.rg r ≠ source s := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact fun r s h => ForwardBankPlacement.consumers_source c hc r s (bankTape_inj h)

theorem consumers_pairwise : consumers.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s) := by
  rw [consumers, List.pairwise_map]
  exact ForwardBankPlacement.consumers_pairwise.imp (fun h r s he => h r s (bankTape_inj he))

def coefficientState (σ : Fin 16 → ℕ) : TblSt 48 A := ⟨fun i => σ (ForwardParameters.coefficient i), []⟩

/-- Each generated consumer bank has the exact concrete interface its program reads. -/
theorem consumer_state (W w : ℕ) (σ : Fin 16 → ℕ) (S : Stacks 640 A)
    (h : ∀ b ∈ consumers, tblHolds b.rg S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨fun i => σ (b.index i), []⟩)) :
    tblHolds gather S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![σ 14, σ 15, σ 5, σ 11, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13], []⟩) ∧
    tblHolds convolution S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![σ 10, σ 15, σ 5, σ 11, σ 8, σ 13, σ 13, σ 13, σ 13, σ 13], []⟩) ∧
    tblHolds dimensions S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![σ 0, σ 10, σ 8, σ 9, σ 11, σ 15, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13], []⟩) ∧
    tblHolds multiplier S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![σ 10, σ 11, σ 13, σ 13, σ 13], []⟩) ∧
    tblHolds coefficient S (tblRho W (List.replicate W tick) (List.replicate w tick) (coefficientState σ)) := by
  have hb (b : ChirpBankTarget 16 640) (hm : b ∈ chirpForwardConsumers gather convolution dimensions coefficient multiplier) :=
    h b (by rwa [consumers_eq])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hh := hb ⟨10, gather, ForwardParameters.gather⟩ (by simp [chirpForwardConsumers])
    rw [chirpForwardGather_values] at hh
    exact hh
  · have hh := hb ⟨10, convolution, ForwardParameters.convolution⟩ (by simp [chirpForwardConsumers])
    rw [chirpForwardConvolution_values] at hh
    exact hh
  · have hh := hb ⟨14, dimensions, ForwardParameters.output⟩ (by simp [chirpForwardConsumers])
    have hv : (fun i => σ (ForwardParameters.output i)) =
        ![σ 0, σ 10, σ 8, σ 9, σ 11, σ 15, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13, σ 13] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at hh
    exact hh
  · have hh := hb ⟨5, multiplier, ForwardParameters.multiplier⟩ (by simp [chirpForwardConsumers])
    have hv : (fun i => σ (ForwardParameters.multiplier i)) = ![σ 10, σ 11, σ 13, σ 13, σ 13] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at hh
    exact hh
  · exact hb ⟨48, coefficient, ForwardParameters.coefficient⟩ (by simp [chirpForwardConsumers])

/-- The one computed zero source establishes all evaluator-owned workspace slots. -/
theorem coefficientState_owned (σ : Fin 16 → ℕ) (hzero : σ 13 = 0) :
    ∀ i ∈ chirpTableOwned, (coefficientState (A := A) σ).val i = 0 := by
  intro i hi
  fin_cases i <;> first
    | (simp [chirpTableOwned_mem] at hi; done)
    | simpa [coefficientState, ForwardParameters.coefficient] using hzero

/-- Every coefficient variable inherits its fit from a computed source word. -/
theorem coefficientState_fit (W : ℕ) (σ : Fin 16 → ℕ) (hfit : ∀ i, σ i < 2 ^ W) :
    ∀ i, (coefficientState (A := A) σ).val i < 2 ^ W := fun i => hfit (ForwardParameters.coefficient i)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
