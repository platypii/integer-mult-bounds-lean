module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationBinaryDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationDimensionFrame

/-! The generated binary words occupy three existing retained slots. Their
frame preserves the worker, codec, pages and unary publication controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
open FixedStreamedBank
noncomputable section
variable {A : ℕ}

def publicationOutsideBinaryDimensions (i : Fin 117) : Prop := i.val < 82 ∨ 84 < i.val

instance (i : Fin 117) : Decidable (publicationOutsideBinaryDimensions i) := by
  unfold publicationOutsideBinaryDimensions
  infer_instance

theorem publicationBinaryLoaded_generator (a b packet V : ℕ) (S : Stacks tapeCount A)
    (i : Fin 117) (hi : publicationOutsideBinaryDimensions i) :
    (PublicationBinaryDimensions.loaded publicationReg a b packet V S).R (publicationReg i) = S.R (publicationReg i) := by
  apply PublicationBinaryDimensions.loaded_off
  all_goals
    apply publicationReg_injective.ne
    intro he
    have hv := congrArg (fun k : Fin 117 => k.val) he
    unfold publicationOutsideBinaryDimensions at hi
    omega

theorem publicationBinaryLoaded_worker (a b packet V : ℕ) (S : Stacks tapeCount A)
    (i : Fin FixedStreamedBank.tapeCount) :
    (PublicationBinaryDimensions.loaded publicationReg a b packet V S).R (base (callerWorker i)) = S.R (base (callerWorker i)) := by
  apply PublicationBinaryDimensions.loaded_off
  all_goals
    apply base_injective.ne
    exact (TransposeRegisterPlacement.generator_off_worker _ _ (by decide +kernel) i).symm

theorem publicationBinaryLoaded_extra (a b packet V : ℕ) (S : Stacks tapeCount A) (i : Fin 7) :
    (PublicationBinaryDimensions.loaded publicationReg a b packet V S).R (extra i) = S.R (extra i) := by
  apply PublicationBinaryDimensions.loaded_off
  all_goals exact (base_extra _ _).symm

theorem publicationBinaryLoaded_codec (a b packet V : ℕ) (S : Stacks tapeCount A)
    (i : Fin tapeCount) (hi : i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6]) :
    (PublicationBinaryDimensions.loaded publicationReg a b packet V S).R i = S.R i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact publicationBinaryLoaded_worker _ _ _ _ _ _
  all_goals exact publicationBinaryLoaded_extra _ _ _ _ _ _

theorem publicationGeometryIndex_outsideBinary (r : TblR 3) :
    publicationOutsideBinaryDimensions (publicationGeometryIndex r) := by
  unfold publicationOutsideBinaryDimensions
  cases r <;> simp only [publicationGeometryIndex,publicationGeometryVariable]
  all_goals (try split_ifs) <;> omega

theorem publicationPageIndex_outsideBinary_fresh (i : Fin 117)
    (hi : i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107]) :
    publicationOutsideBinaryDimensions (publicationPageIndex i) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
