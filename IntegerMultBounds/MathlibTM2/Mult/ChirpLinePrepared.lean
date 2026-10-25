module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineArithmeticSetup

/-! # Arithmetic interfaces established by the executed retained-table setup -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

private theorem processor_kernel (r : CR) : processor r ≠ batch .srcY := by
  intro h
  have hp := processor_range r
  have hv := congrArg Fin.val h
  simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv
  omega

private theorem output_kernel (r : CR) : output.cr r ≠ batch .srcY ∧ output.nr r ≠ batch .srcY := by
  have hc : (output.cr r).val < 146 := (OutputPlacement.layout.cr r).isLt
  have hn : (output.nr r).val < 146 := (OutputPlacement.layout.nr r).isLt
  constructor <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv
    omega

private theorem multiplier_kernel (i : Fin 64) : output.mul i ≠ batch .srcY := by
  intro h
  have hc : (output.mul i).val < 64 := i.isLt
  have hv := congrArg Fin.val h
  simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv
  omega

/-- The generated four tables establish the producer and both output multiplication interfaces. -/
theorem tables_prepared (w q s t α m M Γ : ℕ) (S : Stacks 640 A)
    (hready : Ready (fun r => S.R (processor r)) w q)
    (hbase : ChirpOutputBase output S q w [])
    (hG0 : S.R (processor .ys) = []) (hK0 : S.R (batch .srcY) = []) :
    let S' : Stacks 640 A := { S with R := tablesR w q s t α m M Γ S.R }
    Ready (fun r => S'.R (processor r)) w q ∧
      S'.R (processor .ys) = chirpScheduledStream A w q s t α m M false ∧
      S'.R (batch .srcY) = chirpScheduledStream A w q s t α m M true ∧
      ChirpOutputState output S' q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α) := by
  dsimp only
  let G := chirpScheduledStream A w q s t α m M false
  let K := chirpScheduledStream A w q s t α m M true
  have hp : (fun r => tablesR w q s t α m M Γ S.R (processor r)) =
      Function.update (fun r => S.R (processor r)) CR.ys G := by
    funext r
    simp only [tablesR, Function.update_of_ne (processor_output r .ys).2,
      Function.update_of_ne (processor_output r .ys).1, Function.update_of_ne (processor_kernel r)]
    by_cases hr : r = .ys
    · subst r; simp [G, hG0]
    · simp [Function.update_of_ne (processor_inj.ne hr), hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact hready.update .ys (by simp) G
  · simp only [tablesR, Function.update_of_ne (processor_output .ys .ys).2,
      Function.update_of_ne (processor_output .ys .ys).1,
      Function.update_of_ne (processor_kernel .ys), Function.update_self, hG0, List.append_nil]
  · simp only [tablesR,
      Function.update_of_ne (show batch .srcY ≠ output.nr .ys from (output_kernel .ys).2.symm),
      Function.update_of_ne (show batch .srcY ≠ output.cr .ys from (output_kernel .ys).1.symm),
      Function.update_self, hK0, List.append_nil]
  · let SGK : Stacks 640 A := { S with R := (Function.update
      (Function.update S.R (processor .ys) (G ++ S.R (processor .ys)))
      (batch .srcY) (K ++ S.R (batch .srcY))) }
    have hcr (r : CR) : SGK.R (output.cr r) = S.R (output.cr r) := by
      simp only [SGK, Function.update_of_ne (output_kernel r).1,
        Function.update_of_ne (processor_output .ys r).1.symm]
    have hnr (r : CR) : SGK.R (output.nr r) = S.R (output.nr r) := by
      simp only [SGK, Function.update_of_ne (output_kernel r).2,
        Function.update_of_ne (processor_output .ys r).2.symm]
    have hb : ChirpOutputBase output SGK q w [] := by
      refine ⟨?_, ?_, ?_, (hcr .xs).trans hbase.input,
        fun r hr => (hcr r).trans (hbase.cr_empty r hr),
        fun r hr => (hnr r).trans (hbase.nr_empty r hr)⟩
      · rw [funext hcr]
        exact hbase.cr_ready
      · rw [funext hnr]
        exact hbase.nr_ready
      · intro i
        refine ⟨(hbase.mul_clean i).1, ?_⟩
        simpa only [SGK, Function.update_of_ne (multiplier_kernel i),
          Function.update_of_ne (processor_mul .ys i).symm] using (hbase.mul_clean i).2
    have hE0 : S.R (output.cr .ys) = [] := hbase.cr_empty .ys (by simp)
    have hN0 : S.R (output.nr .ys) = [] := hbase.nr_empty .ys (by simp)
    have hout := hb.installFactors output_cross (chirpOutputFactors s t α q Γ m) (chirpNormalization q α)
    simpa only [SGK, tablesR, G, K, hE0, hN0, List.append_nil] using hout

/-- Executed readiness followed by tables establishes the line's complete arithmetic interface. -/
theorem arithmeticSetup_prepared (w q s t α m M Γ : ℕ) (S : Stacks 640 A)
    (hproc : ∀ r, S.R (processor r) = [])
    (hcr : ∀ r, S.R (output.cr r) = []) (hnr : ∀ r, S.R (output.nr r) = [])
    (hclean : CClean output.mul S) (hK0 : S.R (batch .srcY) = []) :
    let S' : Stacks 640 A := { S with R := tablesR w q s t α m M Γ (readinessR q w S.R) }
    Ready (fun r => S'.R (processor r)) w q ∧
      S'.R (processor .ys) = chirpScheduledStream A w q s t α m M false ∧
      S'.R (batch .srcY) = chirpScheduledStream A w q s t α m M true ∧
      ChirpOutputState output S' q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α) := by
  let S₁ : Stacks 640 A := { S with R := readinessR q w S.R }
  have hr := readiness_ready q w S (fun r _ => hproc r) hcr hnr hclean
  have hG : S₁.R (processor .ys) = [] := by
    rw [show S₁.R (processor .ys) = _ from readiness_processor q w S.R .ys]
    rw [chirpMultiplierSetup_off processor S.R q w _
      (processor_inj.ne (show CR.ys ≠ .wn by decide))
      (processor_inj.ne (show CR.ys ≠ .pn by decide))
      (processor_inj.ne (show CR.ys ≠ .nn by decide))]
    exact hproc .ys
  have hK : S₁.R (batch .srcY) = [] :=
    (readiness_off q w S.R _ (fun r _ => (processor_kernel r).symm)
      (fun r _ => (output_kernel r).1.symm) (fun r _ => (output_kernel r).2.symm)).trans hK0
  exact tables_prepared w q s t α m M Γ S₁ hr.1 hr.2 hG hK

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
