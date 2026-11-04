module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassSetup
public import IntegerMultBounds.MathlibTM2.Host.RestoringSequence

/-! Initialize and retire around a restoring class execution. Prove host-state,
resource and boundary-size composition once, independently of numerical rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.FormattedClassSetup
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A D p u l target s t B W N radius width : ℕ} {P U ι : Type} {S : Stacks T A}

private theorem time_add {m n k : ℕ} {a b : ℝ} (hm : (m : ℝ) ≤ a) (hn : (n : ℝ) ≤ b) :
    ((m+(n+k) : ℕ) : ℝ) ≤ a+b+(k : ℝ) := by
  rw [Nat.cast_add,Nat.cast_add,←add_assoc]
  exact add_le_add (add_le_add hm hn) le_rfl

theorem wrap_exec_within (body : P → Pr P T Q A U)
    (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (output : Fin T) (hc : output ≠ c.core) (hh : output ≠ c.halo)
    (hoff : ∀ r ∈ c.formats, r.2 ≠ output)
    (run : Pr P T Q A U) (runTime : ℝ) (runStock depth : ℕ)
    (result : ι → List (Fin (A+4))) (Cert : ι → Prop)
    (hRun : ∀ v : HS T Q A U, ∃ v', ∃ n : ℕ, ∃ i,
      v'.user = v.user ∧ (n : ℝ) ≤ runTime ∧ Cert i ∧
      mnSize (Host.mk v' {c.loaded with R := Function.update c.loaded.R output (result i)}) =
        mnSize (Host.mk v c.loaded) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v c.loaded)+depth+runStock)
        depth run (Host.mk v c.loaded) n
        (Host.mk v' {c.loaded with R := Function.update c.loaded.R output (result i)}))
    (v : HS T Q A U) :
    ∃ v', ∃ n : ℕ, ∃ i, v'.user = v.user ∧
      (n : ℝ) ≤ (c.timeCost : ℝ)+runTime+(c.retireCost : ℝ) ∧ Cert i ∧
      mnSize (Host.mk v' {S with R := Function.update S.R output (result i)}) = mnSize (Host.mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(c.stock+runStock))
        depth (.seq c.program (.seq run c.retire)) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R output (result i)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := c.exec_within body v depth
  obtain ⟨v₂,n₂,i,hu₂,hn₂,hcert,hsize,he₂⟩ := hRun v₁
  obtain ⟨v₃,hu₃,he₃⟩ := c.retire_exec_within body output hc hh hoff (result i) v₂ depth
  have hbalance : mnSize (Host.mk v₂ {c.loaded with R := Function.update c.loaded.R output (result i)})+
      (c.loaded.R output).length = mnSize (Host.mk v₁ c.loaded)+(result i).length := by
    simpa only [Host.mk,Host.update_rt,Host.get_rt] using
      mn_size_update (Host.mk v₁ c.loaded) v₂ (.rt output) (result i)
  have hlen : (result i).length = (S.R output).length := by
    have hh' : (result i).length = (c.loaded.R output).length := by omega
    exact hh'.trans (congrArg List.length (c.loaded_off output hc hh hoff))
  refine ⟨v₃,n₁+(n₂+c.retireCost),i,hu₃.trans (hu₂.trans hu₁),?_,hcert,
    mn_replace_right_size_of_length v v₃ S output (result i) hlen,?_⟩
  · exact time_add (by exact_mod_cast hn₁) hn₂
  · simpa only [Nat.add_zero] using mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.FormattedClassSetup
