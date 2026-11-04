module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableLoad

/-! The concrete geometry loader preserves the retained unary page language.
Its shared V counter is produced by loading; all other page reads are framed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {A : ℕ}

def publicationRetainedIndex (i : Fin 117) : Prop :=
  i.val < 31 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 36 ∨ i.val = 109 ∨ i.val = 116 ∨
    (88 ≤ i.val ∧ i.val ≤ 92) ∨ (103 ≤ i.val ∧ i.val ≤ 107) ∨
    (51 ≤ i.val ∧ i.val ≤ 84) ∨ i.val = 35

instance (i : Fin 117) : Decidable (publicationRetainedIndex i) := by
  unfold publicationRetainedIndex
  infer_instance

theorem publicationGeometryBank_off_retained (r : TblR 3) (i : Fin 117)
    (hi : publicationRetainedIndex i) : publicationGeometryBank r ≠ publicationReg i := by
  apply publicationReg_injective.ne
  intro h
  have hv := congrArg (fun j : Fin 117 => j.val) h
  dsimp only [publicationRetainedIndex] at hi
  cases r <;> simp only [publicationGeometryIndex,publicationGeometryVariable] at hv
  all_goals (try split_ifs at hv) <;> omega

theorem publicationPageIndex_small (i : Fin 117) (hi : i.val < 31) : publicationPageIndex i = i := by
  apply publicationReg_injective
  exact publicationPageBank_small i hi

theorem publicationPageIndex_fresh (i : Fin 117)
    (hi : i ∈ [(88 : Fin 117),89,90,91,92,103,104,105,106,107]) :
    publicationRetainedIndex (publicationPageIndex i) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel


theorem publicationGeometryLoad_generator (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A) (i : Fin 117)
    (hi : publicationRetainedIndex i) :
    (loadedInputTable publicationGeometryBank input V value S).R (publicationReg i) = S.R (publicationReg i) := by
  apply loadedInputTable_off
  intro r
  exact (publicationGeometryBank_off_retained r i hi).symm

theorem publicationGeometryBank_off_worker (r : TblR 3) (i : Fin FixedStreamedBank.tapeCount) :
    publicationGeometryBank r ≠ base (FixedStreamedBank.callerWorker i) := by
  have hindex : publicationGeometryIndex r ≠ 109 := by
    intro h
    exact publicationGeometryBank_off_retained r 109 (by decide +kernel) (congrArg publicationReg h)
  apply base_injective.ne
  exact TransposeRegisterPlacement.generator_off_worker _ _ hindex i

theorem publicationGeometryLoad_worker (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A) (i : Fin FixedStreamedBank.tapeCount) :
    (loadedInputTable publicationGeometryBank input V value S).R (base (FixedStreamedBank.callerWorker i)) =
      S.R (base (FixedStreamedBank.callerWorker i)) := by
  apply loadedInputTable_off
  intro r
  exact (publicationGeometryBank_off_worker r i).symm

theorem publicationGeometryLoad_extra (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A) (i : Fin 7) :
    (loadedInputTable publicationGeometryBank input V value S).R (extra i) = S.R (extra i) := by
  apply loadedInputTable_off
  intro r
  exact (base_extra _ _).symm

theorem publicationGeometryLoad_ambient (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A) :
    (loadedInputTable publicationGeometryBank input V value S).R ambientPort = S.R ambientPort := by
  apply loadedInputTable_off
  intro r
  exact (publicationGeometryBank_off_ports r).2.symm

theorem publicationGeometryLoad_codec (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A) (i : Fin tapeCount)
    (hi : i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6]) :
    (loadedInputTable publicationGeometryBank input V value S).R i = S.R i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact publicationGeometryLoad_worker input V value S _
  all_goals exact publicationGeometryLoad_extra input V value S _

theorem publicationGeometryLoad_page (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A) (i : Fin 117)
    (hi : publicationRetainedIndex (publicationPageIndex i)) :
    (loadedInputTable publicationGeometryBank input V value S).R (publicationPageBank i) =
      S.R (publicationPageBank i) := by
  apply loadedInputTable_off
  intro r
  exact (publicationGeometryBank_off_retained r (publicationPageIndex i) hi).symm

theorem publicationGeometryLoad_pageWidth (input : Fin 3 → Fin tapeCount) (V : ℕ)
    (value : Fin tapeCount → ℕ) (S : Stacks tapeCount A)
    (hblank : ∀ r, S.R (publicationGeometryBank r) = []) :
    ((loadedInputTable publicationGeometryBank input V value S).R (publicationPageBank 115)).length = V := by
  let M := loadedInputTable publicationGeometryBank input V value S
  have hh : tblHolds publicationGeometryBank M
      (tblRho V (List.replicate V tick) [] ⟨fun i => value (input i),[]⟩) := by
    simpa only [M,loadedInputTable,List.replicate_zero] using
      chirpBankLoad_holds publicationGeometryBank publicationGeometryBank_injective input V 0 value S hblank
  rw [publicationPageBank_width,←publicationGeometryBank_width,hh .wr]
  simp [tblRho]

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
