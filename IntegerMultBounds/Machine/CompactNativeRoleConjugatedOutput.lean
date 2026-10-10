import IntegerMultBounds.Machine.CompactNativeRoleConjugatedPorts
import IntegerMultBounds.Machine.AlphabetTapeReplacement

/-! Actual conjugated phase output is again the encoding of a literal native
role bank. Thus lifted binary controller routines can consume the result
without a payload conversion or an assumed alphabet correspondence. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleConjugatedOutput
noncomputable section
open CompactNativeRoleSourcePorts (external roles replaceSource callerTapes)
open CompactNativeRoleConjugatedPorts (encoding selected)
open SharedPlacementAlphabet (setTape)
variable {t c : ℕ}

def roleSlot (j : Fin c) : Fin (1+c) := ⟨j.val+1,by omega⟩

theorem roles_set (payload : Tapes (1+c) 2) (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    roles (setTape payload (roleSlot j) f p)=setTape (roles payload) j f p := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp [roles,setTape,roleSlot,Function.update_apply,Fin.ext_iff]

theorem source_unchanged (old : Tapes t 2) (ht : 43<t)
    (payload : Tapes (1+c) 2) (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    replaceSource old ht (setTape payload (roleSlot j) f p)=replaceSource old ht payload := by
  have hn : (0 : Fin (1+c))≠roleSlot j := by
    intro h; have hv := congrArg Fin.val h; simp only [roleSlot,Fin.val_zero] at hv; omega
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [setTape,hn]

theorem external_set (old : Tapes t 2) (ht : 43<t)
    (st : ActiveRepairRankHeadersCommands.State) (payload : Tapes (1+c) 2)
    (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    external old ht st (setTape payload (roleSlot j) f p)=
      setTape (external old ht st payload) (selected t j) f p := by
  unfold external selected
  rw [source_unchanged,roles_set,SharedPlacementAlphabet.setTape_append_right]

theorem installed_word (old : Tapes t 2) (ht : 43<t)
    (st : ActiveRepairRankHeadersCommands.State) (payload : Tapes (1+c) 2) (j : Fin c)
    {s : CompactGadgetReservationShape.Shape} (d : ActivePrefixStageFullData.Inputs s)
    {B : ℕ} (ys : ActivePrefixStageNativeRows.Rows d B) (ell : ℕ) :
    setTape (Alphabet.mapTapes encoding (external old ht st payload)) (selected t j)
      ((CompactNativeConjugatedPhase.bank d ell ys).tape CompactNativeConjugatedHeaderBank.source)
      ((CompactNativeConjugatedPhase.bank d ell ys).head CompactNativeConjugatedHeaderBank.source)=
      Alphabet.mapTapes encoding (external old ht st
        (setTape payload (roleSlot j)
          (SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat ys))) 0)) := by
  rw [(CompactNativeConjugatedHeaderBank.bank_source d ys ell).1,
    (CompactNativeConjugatedHeaderBank.bank_source d ys ell).2,
    external_set,AlphabetTapeReplacement.map_setTape]
  rfl

end
end IntegerMultBounds.Machine.CompactNativeRoleConjugatedOutput
