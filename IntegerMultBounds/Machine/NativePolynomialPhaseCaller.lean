import IntegerMultBounds.Machine.CompactPolynomialPhasePlacement

/-! The phase source contract is derived from the literal original native
basis-word caller, including its full appended converter and header workspace.
No supplied serialization or alphabet compatibility premise is needed. -/
namespace IntegerMultBounds.Machine.NativePolynomialPhaseCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows flattenArray)
variable {s : Shape} {R w : ℕ}

def source : Fin ActivePrefixStageNativePairSchedule.count :=
  Fin.castAdd 1 ActivePrefixStageNative.raw

theorem source_val : source.val=65 := rfl

/-- The source required by the actual physical phase caller is precisely the
source installed at the boundary of every literal native basis-word stage. -/
theorem source_word (d : Inputs s)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (ActivePrefixStageNativePairRun.bank d (rows d xs hw)).tape source=
      SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0
          (UnitPhaseFullStreamNormalized.serialized (flattenArray xs))) := by
  change (ActivePrefixStageNativeRows.core d (rows d xs hw)).tape 65=_
  exact ActivePrefixStageNativePolynomial.source_word d xs hw

theorem source_head (d : Inputs s)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (ActivePrefixStageNativePairRun.bank d (rows d xs hw)).head source=0 := rfl

private theorem raw_setTape {k t a : ℕ} (c : Tapes k a) (j : Fin k) (i : Fin t)
    (hij : i.val=j.val) (f : ℤ → Fin (a+4)) (p : ℤ) :
    SharedPlacementAlphabet.setTape (SharedBankStageInput.raw c t) i f p=
      SharedBankStageInput.raw (SharedPlacementAlphabet.setTape c j f p) t := by
  apply congrArg₂ Tapes.mk <;> funext r
  all_goals by_cases hr : r.val<k
  all_goals simp [SharedPlacementAlphabet.setTape,SharedBankStageInput.raw,Function.update_apply,Fin.ext_iff,hr,hij]
  all_goals intro he; have := j.isLt; omega

/-- A physical replacement of the sole native source has exactly the bank
needed by the next basis instruction; every original header and private tape
remains unchanged. -/
theorem replace_rows {B : ℕ} (d : Inputs s) (xs ys : ActivePrefixStageNativeRows.Rows d B) :
    SharedPlacementAlphabet.setTape (ActivePrefixStageNativePairRun.bank d xs) source
      (SymbolTriplePlaced.native ActivePrefixStageNative.ha (ActivePrefixStageNativeRows.flat ys)) 0=
      ActivePrefixStageNativePairRun.bank d ys := by
  unfold ActivePrefixStageNativePairRun.bank source
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun z : Tapes ActivePrefixStageNative.tapes Networks.Shared50ModularControl.prime => z.append (SharedBank.empty 1 Networks.Shared50ModularControl.prime))
  unfold ActivePrefixStageNativeRows.bank
  rw [raw_setTape _ (65 : Fin 66) ActivePrefixStageNative.raw rfl]
  apply congrArg (fun z : Tapes 66 Networks.Shared50ModularControl.prime => SharedBankStageInput.raw z ActivePrefixStageNative.tapes)
  unfold ActivePrefixStageNativeRows.core
  rw [show (65 : Fin 66)=Fin.natAdd 65 (0 : Fin 1) from rfl,
    SharedPlacementAlphabet.setTape_append_right]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.NativePolynomialPhaseCaller
