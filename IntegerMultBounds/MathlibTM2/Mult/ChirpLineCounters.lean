module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLinePrepared

/-! # Install the fixed line's nine output controls after arithmetic preparation -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

theorem dimensions_inj : Function.Injective dimensions :=
  bankTape_inj.comp (ForwardBankPlacement.place_injective _ (by decide))

theorem output_dimension_range (i : Fin 9) : (output.dim i).val < 146 :=
  (OutputPlacement.layout.dim i).isLt

theorem dimensions_counter (i : Fin 9) (r : TblR 14) : dimensions r ≠ output.dim i := by
  intro h
  have hb := bank_range (ForwardBankPlacement.output r)
  have hc := output_dimension_range i
  have hv := congrArg Fin.val h
  change (bankTape (ForwardBankPlacement.output r)).val = _ at hv
  omega

theorem processor_counter (r : CR) (i : Fin 9) : processor r ≠ output.dim i := by
  intro h
  have hp := processor_range r
  have hc := output_dimension_range i
  have hv := congrArg Fin.val h
  omega

theorem kernel_counter (i : Fin 9) : batch .srcY ≠ output.dim i := by
  intro h
  have hc := output_dimension_range i
  have hv := congrArg Fin.val h
  simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv
  omega

def counters : Pr P 640 Q A U := chirpOutputDimensionSetup dimensions output.dim

def countersR (p q l Γ w t : ℕ) (R : Regs 640 A) : Regs 640 A :=
  unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) R (chirpOutputAssignments output.dim)

def countersCost (W p q l Γ w t : ℕ) : ℕ :=
  25 * tblC W w + unaryCopiesCost W (chirpOutputDimensionValues p q l Γ w t) (chirpOutputAssignments output.dim)

/-- Compute, install and retain every output control, restoring its binary source bank. -/
theorem counters_exec (W p q l Γ w t : ℕ) (hwW : w ≤ W) (hpq : p ≤ q)
    (hwidth : q + l + Γ + 5 ≤ w) (hvolume : t * (p + l + Γ + 5) < 2 ^ W)
    (hfit : ∀ i : Fin 6, (![p, q, l, Γ, w, t] : Fin 6 → ℕ) i < 2 ^ W)
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hS : tblHolds dimensions S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![p, q, l, Γ, w, t, 0, 0, 0, 0, 0, 0, 0, 0], []⟩)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ countersCost W p q l Γ w t ∧
      Exec body counters (mk v S) n (mk v' { S with R := countersR p q l Γ w t S.R }) := by
  apply chirpOutputDimensionSetup_exec (body := body) dimensions_inj output.dim dimensions_counter
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW
    ⟨![p, q, l, Γ, w, t, 0, 0, 0, 0, 0, 0, 0, 0], []⟩ p q l Γ w t
    rfl rfl rfl rfl rfl rfl hpq hwidth hvolume
    (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl) _ v S hS
  intro i
  fin_cases i <;> first
    | exact hfit 0 | exact hfit 1 | exact hfit 2 | exact hfit 3 | exact hfit 4 | exact hfit 5 | simp

/-- Counter installation preserves the entire producer and kernel data, plus output readiness. -/
theorem counters_prepared (p q l Γ w t s α m : ℕ) (S : Stacks 640 A)
    (hready : Ready (fun r => S.R (processor r)) w q)
    (houtput : ChirpOutputState output S q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α))
    (hblank : ∀ i, S.R (output.dim i) = [])
    (hwork : ∀ i : Fin 22, 9 ≤ i.val → S.R (output.bank i) = []) :
    let S' : Stacks 640 A := { S with R := countersR p q l Γ w t S.R }
    Ready (fun r => S'.R (processor r)) w q ∧
      (∀ r, S'.R (processor r) = S.R (processor r)) ∧
      S'.R (batch .srcY) = S.R (batch .srcY) ∧
      ChirpOutputState output S' q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α) ∧
      (∀ i, (S'.R (output.dim i)).length = chirpOutputDimensionCount p q l Γ w t i) ∧
      (∀ i : Fin 22, 9 ≤ i.val → S'.R (output.bank i) = []) := by
  dsimp only
  have hp (r : CR) : countersR p q l Γ w t S.R (processor r) = S.R (processor r) :=
    chirpOutputDimensions_off _ _ _ _ _ _ _ _ _ (processor_counter r)
  refine ⟨?_, hp, chirpOutputDimensions_off _ _ _ _ _ _ _ _ _ kernel_counter,
    houtput.install p l Γ t, ?_, ?_⟩
  · rw [funext hp]
    exact hready
  · intro i
    unfold countersR
    rw [chirpOutputDimensions_at output.dim output.dim_inj, hblank i, List.append_nil, List.length_replicate]
  · intro i hi
    unfold countersR
    rw [chirpOutputDimensions_off output.dim p q l Γ w t S.R _ (by
      intro j h
      have he : i = Fin.castLE (by decide) j := output.bank_inj h
      have hv := congrArg Fin.val he
      have hj := j.isLt
      change i.val = j.val at hv
      omega)]
    exact hwork i hi

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
