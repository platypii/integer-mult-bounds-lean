module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseHeadersReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBankFacts

/-! A clean native bank constructed from ten ordinary unary master headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

variable {A : ℕ}

theorem inverseMasterCorePort_injective : Function.Injective inverseMasterCorePort := by
  intro i j h
  apply inverseMasterPort_injective
  exact congrArg inverseCoreReg h

theorem inverseMasterCorePort_source (i : Fin 10) : inverseMasterCorePort i ≠ (110 : Fin 224) := by
  fin_cases i <;> decide

/-- Empty storage, one input word and ten unary master words. -/
def masterHeaderBank (values : Fin 10 → ℕ) (input : List (Fin (A+4))) : Stacks 224 A :=
  ⟨[], [], (fun _ => []),
    descriptorBankR (List.ofFn (fun i => (inverseMasterCorePort i, List.replicate (values i) Node.tick)))
      (Function.update (fun _ => []) 110 input)⟩

theorem masterHeaderBank_headers (values : Fin 10 → ℕ) (input : List (Fin (A+4))) (i : Fin 10) :
    (masterHeaderBank values input).R (inverseMasterCorePort i) = List.replicate (values i) Node.tick := by
  have h := descriptorBankR_ofFn inverseMasterCorePort inverseMasterCorePort_injective
    (fun i => List.replicate (values i) Node.tick) (Function.update (fun _ => []) 110 input) i
  simpa only [masterHeaderBank, Function.update_of_ne (inverseMasterCorePort_source i),
    List.append_nil] using h

theorem masterHeaderBank_off (values : Fin 10 → ℕ) (input : List (Fin (A+4)))
    (k : Fin 224) (hk : ∀ i, inverseMasterCorePort i ≠ k) :
    (masterHeaderBank values input).R k = if k = 110 then input else [] := by
  change descriptorBankR _ _ k = _
  rw [descriptorBankR_frame _ _ k (by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact hk i)]
  simp [Function.update_apply]

theorem masterHeaderBank_source (values : Fin 10 → ℕ) (input : List (Fin (A+4))) :
    (masterHeaderBank values input).R 110 = input := by
  rw [masterHeaderBank_off values input 110 inverseMasterCorePort_source]
  simp

/-- Readiness follows from the actual constructed words; it is not an input premise. -/
theorem masterHeaderBank_ready (P N q l s t u band a b : ℕ) (input : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool) := []) (out : List Bool := []) :
    LengthKeyReady P N q l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg
          {masterHeaderBank (masterHeaderValues P N q l s t u band a b) input with inp := inp, out := out})))) := by
  apply masterHeaders_ready
    {masterHeaderBank (masterHeaderValues P N q l s t u band a b) input with inp := inp, out := out}
    input (by intro k; rfl)
    (masterHeaderBank_headers (masterHeaderValues P N q l s t u band a b) input)
  · intro k hk h110 _
    rw [masterHeaderBank_off (masterHeaderValues P N q l s t u band a b) input k hk, ite_eq_right h110]
  · exact masterHeaderBank_source (masterHeaderValues P N q l s t u band a b) input

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
