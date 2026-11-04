module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! The concrete dimension setup changes four working headers. All other
metadata and both publication data ports retain their pre-setup meaning. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
namespace PublicationDimensionReg
variable {T T' A : ℕ}

theorem loaded_update_off (e : PublicationDimensionReg → Fin T) (a b L w N C B : ℕ)
    (S : Stacks T A) (k : Fin T) (xs : List (Fin (A+4)))
    (hoff : ∀ r ∈ outputs, e r ≠ k) :
    loaded e a b L w N C B {S with R := Function.update S.R k xs} =
      {loaded e a b L w N C B S with R := (Function.update (loaded e a b L w N C B S).R k xs)} := by
  refine Stacks.ext rfl rfl rfl ?_
  simp only [loaded]
  rw [Function.update_comm (hoff exponent (by simp [outputs])).symm,
    Function.update_comm (hoff packet (by simp [outputs])).symm,
    Function.update_comm (hoff clock (by simp [outputs])).symm,
    Function.update_comm (hoff padding (by simp [outputs])).symm]

theorem loaded_project (placement : Fin T → Fin T') (hplacement : Function.Injective placement)
    (e : PublicationDimensionReg → Fin T) (a b L w N C B : ℕ) (S : Stacks T' A) :
    embStk placement (loaded (placement ∘ e) a b L w N C B S) =
      loaded e a b L w N C B (embStk placement S) := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [loaded,embStk,Function.comp_apply,Function.update_apply,hplacement.eq_iff]

end PublicationDimensionReg
namespace PackedTranspose
open FixedStreamedBank
noncomputable section
variable {A : ℕ}

def publicationBeforeOrAfterDimensions (i : Fin 117) : Prop := i.val < 51 ∨ 55 ≤ i.val

instance (i : Fin 117) : Decidable (publicationBeforeOrAfterDimensions i) := by
  unfold publicationBeforeOrAfterDimensions
  infer_instance

theorem publicationDimensionIndex_bound (r : PublicationDimensionReg) : (publicationDimensionIndex r).val < 95 := by
  cases r <;> decide +kernel

theorem publicationDimensionBank_off_ports (r : PublicationDimensionReg) :
    publicationDimensionBank r ≠ numericalPort ∧ publicationDimensionBank r ≠ ambientPort := by
  change publicationReg (publicationDimensionIndex r) ≠ publicationReg 95 ∧
    publicationReg (publicationDimensionIndex r) ≠ publicationReg 96
  simp only [publicationReg_injective.ne_iff]
  have hr := publicationDimensionIndex_bound r
  constructor <;> intro h <;> have hv := congrArg (fun i : Fin 117 => i.val) h <;> omega

theorem publicationDimensionLoaded_off (a b L w N C B : ℕ) (S : Stacks tapeCount A) (i : Fin tapeCount)
    (hoff : ∀ r ∈ PublicationDimensionReg.outputs, i ≠ publicationDimensionBank r) :
    (PublicationDimensionReg.loaded publicationDimensionBank a b L w N C B S).R i = S.R i := by
  simp only [PublicationDimensionReg.loaded,
    Function.update_of_ne (hoff .padding (by simp [PublicationDimensionReg.outputs])),
    Function.update_of_ne (hoff .clock (by simp [PublicationDimensionReg.outputs])),
    Function.update_of_ne (hoff .packet (by simp [PublicationDimensionReg.outputs])),
    Function.update_of_ne (hoff .exponent (by simp [PublicationDimensionReg.outputs]))]

theorem publicationDimensionOutput_bounds (r : PublicationDimensionReg) (hr : r ∈ PublicationDimensionReg.outputs) :
    51 ≤ (publicationDimensionIndex r).val ∧ (publicationDimensionIndex r).val ≤ 54 := by
  simp only [PublicationDimensionReg.outputs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel

theorem publicationDimensionLoaded_generator (a b L w N C B : ℕ) (S : Stacks tapeCount A) (i : Fin 117)
    (hi : publicationBeforeOrAfterDimensions i) :
    (PublicationDimensionReg.loaded publicationDimensionBank a b L w N C B S).R (publicationReg i) = S.R (publicationReg i) := by
  apply publicationDimensionLoaded_off
  intro r hr h
  have hv := congrArg (fun j : Fin 117 => j.val) (publicationReg_injective h)
  have hb := publicationDimensionOutput_bounds r hr
  dsimp only [publicationBeforeOrAfterDimensions] at hi
  omega

theorem publicationDimensionLoaded_worker (a b L w N C B : ℕ) (S : Stacks tapeCount A)
    (i : Fin FixedStreamedBank.tapeCount) :
    (PublicationDimensionReg.loaded publicationDimensionBank a b L w N C B S).R (base (FixedStreamedBank.callerWorker i)) =
      S.R (base (FixedStreamedBank.callerWorker i)) := by
  apply publicationDimensionLoaded_off
  intro r hr
  apply base_injective.ne
  have hb := publicationDimensionOutput_bounds r hr
  have hne : publicationDimensionIndex r ≠ 109 := by intro h; rw [h] at hb; norm_num at hb
  exact (TransposeRegisterPlacement.generator_off_worker _ _ hne i).symm

theorem publicationDimensionLoaded_extra (a b L w N C B : ℕ) (S : Stacks tapeCount A) (i : Fin 7) :
    (PublicationDimensionReg.loaded publicationDimensionBank a b L w N C B S).R (extra i) = S.R (extra i) := by
  apply publicationDimensionLoaded_off
  intro r _
  exact (base_extra _ _).symm


theorem publicationGeometryIndex_outsideDimensions (r : Fast.TableVM.TblR 3) :
    publicationBeforeOrAfterDimensions (publicationGeometryIndex r) := by
  unfold publicationBeforeOrAfterDimensions
  cases r <;> dsimp only [publicationGeometryIndex,publicationGeometryVariable]
  all_goals (try split_ifs) <;> omega

theorem publicationGeometryInput_outsideDimensions (i : Fin 3) :
    publicationBeforeOrAfterDimensions ⟨82+i.val,by have := i.isLt; omega⟩ := by
  dsimp only [publicationBeforeOrAfterDimensions]
  omega

theorem publicationPageIndex_outsideDimensions_fresh (i : Fin 117)
    (hi : i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107]) :
    publicationBeforeOrAfterDimensions (publicationPageIndex i) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem publicationDimensionLoaded_codec (a b L w N C B : ℕ) (S : Stacks tapeCount A) (i : Fin tapeCount)
    (hi : i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6]) :
    (PublicationDimensionReg.loaded publicationDimensionBank a b L w N C B S).R i = S.R i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact publicationDimensionLoaded_worker a b L w N C B S _
  all_goals exact publicationDimensionLoaded_extra a b L w N C B S _

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
