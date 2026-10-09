import IntegerMultBounds.Machine.ActiveRepairRankFieldsRun
import IntegerMultBounds.Machine.SharedBankFrames

/-! The complete genuine-rank field/source parser placed on arbitrary caller
slots, with literal retained descriptors and clean private storage. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankParserPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
open ActiveRepairRankFieldsBank
open SelectedSourceBitsScan (word)
variable {t : ℕ}

def ports : Fin 18 → Fin 27 := Fin.castAdd 9

def sources (cs : List Bool) (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool) :=
  bank cs ActiveRepairRankFieldsRun.empty hs ss

def result (caller : Tapes t 1) (focus : Fin 18 → Fin t) (ws : Fin 5 → List Bool) :=
  setTape (setTape (setTape (setTape (setTape caller (focus 1) (word (ws 0)) 0)
    (focus 2) (word (ws 1)) 0) (focus 3) (word (ws 2)) 0)
    (focus 4) (word (ws 3)) 0) (focus 5) (word (ws 4)) 0

def program (focus : Fin 18 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActiveRepairRankFieldsRun.program (CleanSubbank.placement ports focus hf)

theorem native_payload (v : Tapes 18 1) :
    SharedBank.payload (CleanSubbank.bank (s := 9) v) ports=v := CleanSubbank.payload_bank v

theorem native_clean (v : Tapes 18 1) :
    SharedBank.strip (CleanSubbank.bank (s := 9) v) ports=SharedBank.empty 27 1 :=
  SharedBankFrames.strip_common_single_blank v 9

theorem result_payload (caller : Tapes t 1) (focus : Fin 18 → Fin t)
    (hf : Function.Injective focus) (cs : List Bool) (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources cs hs ss) (ws : Fin 5 → List Bool) :
    SharedBank.payload (result caller focus ws) focus=bank cs ws hs ss := by
  simp only [result,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t 1) (focus : Fin 18 → Fin t) (hf : Function.Injective focus)
    (cs : List Bool) (starts widths : Fin 4 → ℕ) (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources cs hs ss)
    (hv0 : ∀ i, Counter.value (hs (offsetSlot i))=starts i)
    (hv1 : ∀ i, Counter.value (hs (widthSlot i))=widths i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (q rho n f A : ℕ) (hwidth : widths 3=f*q) (hnf : n+1=f) (hr : rho<q)
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i)) (hfit : ∀ i, starts i+widths i≤A) :
    HoareTime (program focus hf) (fun z => z=CleanSubbank.bank (s := 27) caller)
      (fun z => z=CleanSubbank.bank (s := 27)
        (result caller focus (ActiveRepairRankFieldsRun.finished cs starts widths q rho n)))
      (1200*(A+1)+4) := by
  refine CleanSubbank.realizes _ ports focus (Fin.castAdd_injective _ _) hf caller
    (result caller focus (ActiveRepairRankFieldsRun.finished cs starts widths q rho n)) _ _ _ ?_ ?_
    (native_clean _) (native_clean _) ?_
    (ActiveRepairRankFieldsRun.runs_linear cs starts widths hs ss hv0 hv1 hc q rho n f A hwidth hnf hr sv sc hfit)
  · rw [native_payload]
    exact hsrc.symm
  · rw [native_payload,result_payload caller focus hf cs hs ss hsrc]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActiveRepairRankParserPlaced
