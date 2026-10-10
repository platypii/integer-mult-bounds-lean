import IntegerMultBounds.Machine.NativeEndpointCharacterHeaders
import IntegerMultBounds.Machine.NativePolynomialStageHeaderBudget

/-! Private endpoint-character geometry is synthesized from copied original
raw descriptors. Actual parent rows are physically divided by the fixed role
count; codec payload is computed from ell and precision, and both immutable
inputs are erased after ell is copied to its retained phase port. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterPrepare
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActiveRepairRankHeadersCommands (State bank)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def raw (v : Stage s) (parentRows ell p : ℕ) :=
  CompactSpectatorLeafSetup.raw s parentRows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val

def prepared (v : Stage s) (parentRows ell p : ℕ) :=
  NativePolynomialStageHeaders.prepared s parentRows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val

def input (v : Stage s) (parentRows ell p : ℕ) : Tapes 67 2 :=
  (bank (raw v parentRows ell p)).append (FixedHeaderBankCopy.empty 24)
def middle (v : Stage s) (parentRows ell p : ℕ) : Tapes 67 2 :=
  (bank (prepared v parentRows ell p)).append (NativeEndpointCharacterHeaders.tail ell)

def finishSchedule (c : ℕ) : List Op :=
  [cmd (.erase 26),.base (.constant 19 c),.base (.quotient ![4,19,26] (by decide)),
    cmd (.erase 4),cmd (.copy 26 4 (by decide)),cmd (.erase 26),cmd (.erase 19),
    cmd (.erase 17),cmd (.erase 18)]

theorem finish_valid (c : ℕ) (hc : 0<c) (v : Stage s) (parentRows ell p : ℕ) :
    validSchedule (finishSchedule c) (prepared v parentRows ell p) := by
  simp [finishSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,prepared,NativePolynomialStageHeaders.prepared,
    CompactSpectatorLeafSetup.raw,ActiveRepairRankHeadersCommands.put,Function.update,hc]

theorem finish_eval (c : ℕ) (v : Stage s) (parentRows ell p : ℕ) :
    execute (finishSchedule c) (prepared v parentRows ell p)=
      ActivePrefixStageHeadersData.initial (NativePolynomialStageShape.stage v ell p) (parentRows/c) := by
  funext i
  fin_cases i <;> simp [finishSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    prepared,NativePolynomialStageHeaders.prepared,CompactSpectatorLeafSetup.raw,
    ActiveRepairRankHeadersCommands.put,Function.update,ActivePrefixStageHeadersData.initial,
    ActivePrefixStageHeadersData.originalValues,NativePolynomialStageShape.stage,NativePolynomialStageShape.shape]

def setup := extend (NativePolynomialStageHeaders.program (a:=2)) 24
def copyEll := BinaryDescriptorInstall.program 2 (17 : Fin 67) 65 (by decide)
def finish (c : ℕ) := extend (compile (a:=2) (finishSchedule c)).2 24
def program (c : ℕ) := seq setup (seq copyEll (finish c))

def cost (c : ℕ) (v : Stage s) (parentRows ell p : ℕ) :=
  NativePolynomialStageHeaders.cost s parentRows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val+1+
    (2*(RecursiveChildQuotientsConstant.bits ell).length+6+1+
      scheduleCost (finishSchedule c) (prepared v parentRows ell p))

theorem copy_ell_runs (v : Stage s) (parentRows ell p : ℕ) :
    HoareTime copyEll
      (fun z => z=(bank (prepared v parentRows ell p)).append (FixedHeaderBankCopy.empty 24))
      (fun z => z=middle v parentRows ell p)
      (2*(RecursiveChildQuotientsConstant.bits ell).length+6) := by
  have hs := NativePolynomialStageHeaders.prepared_immutable s parentRows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val
  have hh := BinaryDescriptorInstall.install_hoare (17 : Fin 67) 65 (by decide)
    ((bank (a:=2) (prepared v parentRows ell p)).append (FixedHeaderBankCopy.empty 24))
    (RecursiveChildQuotientsConstant.bits ell)
    (by
      rw [show (17 : Fin 67)=Fin.castAdd 24 (Fin.castAdd 15 (17 : Fin 28)) from rfl]
      simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
        ActiveRepairRankHeadersCommands.caller,prepared,hs.1])
    (by
      rw [show (17 : Fin 67)=Fin.castAdd 24 (Fin.castAdd 15 (17 : Fin 28)) from rfl]
      simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
        ActiveRepairRankHeadersCommands.caller,prepared,hs.1]
      all_goals rfl)
    (by rfl) (by rfl)
  change HoareTime copyEll _ (fun z => z=setTape
    ((bank (prepared v parentRows ell p)).append (FixedHeaderBankCopy.empty 24))
    (Fin.natAdd 43 (22 : Fin 24)) (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits ell)) 1) _ at hh
  rw [SharedPlacementAlphabet.setTape_append_right] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs (c : ℕ) (hc : 0<c) (v : Stage s) (parentRows ell p : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime (program c) (fun z => z=input v parentRows ell p)
      (fun z => z=NativeEndpointCharacterHeaders.initial
        (NativePolynomialStageShape.stage v ell p) (parentRows/c) ell)
      (cost c v parentRows ell p) := by
  have hsetup := hoare_extend_eq
    (NativePolynomialStageHeaders.runs (a:=2) s parentRows ell p v.rho v.left v.f v.slots v.right
      v.source.val v.target.val hG hA hK) (FixedHeaderBankCopy.empty 24)
  have hcopy := copy_ell_runs v parentRows ell p
  have hfinish := schedule_runs (a:=2) (finishSchedule c) (prepared v parentRows ell p)
    (finish_valid c hc v parentRows ell p)
  rw [finish_eval] at hfinish
  have hf := hoare_extend_eq hfinish (NativeEndpointCharacterHeaders.tail ell)
  exact hsetup.seq (hcopy.seq hf)

end
end IntegerMultBounds.Machine.NativeEndpointCharacterPrepare
