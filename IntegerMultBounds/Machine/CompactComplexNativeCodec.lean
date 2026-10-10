import IntegerMultBounds.Machine.CompactNativeRolePrecisionHeaders
import IntegerMultBounds.Machine.CompactNativeRoleScalarBudget
import IntegerMultBounds.Machine.BinaryDescriptorInstall
import IntegerMultBounds.Machine.CompactNativeRoleConjugatedLifecycle

/-! Original retained scalar descriptors physically regenerate the corrected
stored signed width reservation. Only then are ell and corrected precision
copied into stage17/18; all scalar arithmetic workspace is erased. -/
namespace IntegerMultBounds.Machine.CompactComplexNativeCodec
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open ActivePrefixStageHeadersData (initial)
open ActivePrefixStageParameters (Stage)
open CompactGadgetReservationShape (Shape)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
open CompactNativeRoleReservedBridge (precision)
variable {s : Shape}

def withEll (v : Stage s) (rows ell : ℕ) := put (initial v rows) 17 ell
def raw (v : Stage s) (rows ell p : ℕ) := CompactNativeRoleConjugatedLifecycle.rawState v rows ell p

theorem raw_eq (v : Stage s) (rows ell p : ℕ) : raw v rows ell p=put (withEll v rows ell) 18 p := by
  funext i
  fin_cases i <;> simp [raw,CompactNativeRoleConjugatedLifecycle.rawState,CompactSpectatorLeafSetup.raw,
    withEll,initial,ActivePrefixStageHeadersData.originalValues,put,Function.update]

def copyEll := BinaryDescriptorInstall.program 2 (3 : Fin 86) 60 (by decide)
def copyPrecision := BinaryDescriptorInstall.program 2 (19 : Fin 86) 61 (by decide)
def copyProgram := seq copyEll copyPrecision

def prepareProgram (c m : ℕ) :=
  seq (seq (extend (CompactGlobalRowHeaderOps.compile (a:=2) (CompactNativeRolePrecisionHeaders.schedule c m)).2 43)
    copyProgram) (extend (CompactGlobalRowHeaderOps.compile (a:=2) CompactNativeRolePrecisionHeaders.cleanup).2 43)

def copyCost (ell p : ℕ) := 2*(bits ell).length+5+1+(2*(bits p).length+5)

def prepareCost (c m D K rho ell q d G : ℕ) :=
  CompactGlobalRowHeaderOps.scheduleCost (CompactNativeRolePrecisionHeaders.schedule c m)
    (CompactReservedHeaders.initial D K rho ell q d G)+copyCost ell (precision c m d D K q)+
  CompactGlobalRowHeaderOps.scheduleCost CompactNativeRolePrecisionHeaders.cleanup
    (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)+2

private theorem bank_put (st : State) (i : Fin 28) (n : ℕ) :
    setTape (bank (a:=2) st) (Fin.castAdd 15 i) (RadixZeroFill.encodedBinary (bits n)) 1=bank (put st i n) := by
  simp only [bank,CleanSubbank.bank]
  rw [SharedPlacementAlphabet.setTape_append_left,←ActiveRepairRankHeadersCommands.put_caller]

private theorem copy_one (st su : State) (src dst : Fin 28) (n : ℕ)
    (hs : st src=some n) (hd : su dst=none) :
    HoareTime (BinaryDescriptorInstall.program 2 (Fin.castAdd 43 (Fin.castAdd 15 src))
      (Fin.natAdd 43 (Fin.castAdd 15 dst)) (by
        intro h;have hv := congrArg Fin.val h;simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega))
      (fun z => z=(bank st).append (bank su))
      (fun z => z=(bank st).append (bank (put su dst n))) (2*(bits n).length+5) := by
  have h := BinaryDescriptorInstall.install_hoare
    (Fin.castAdd 43 (Fin.castAdd 15 src)) (Fin.natAdd 43 (Fin.castAdd 15 dst))
    (by intro h;have hv := congrArg Fin.val h;simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega)
    ((bank (a:=2) st).append (bank (a:=2) su)) (bits n)
    (by simp only [Tapes.append,Fin.addCases_left,bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,hs])
    (by simp only [Tapes.append,Fin.addCases_left,bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,hs]; rfl)
    (by simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,hd])
    (by simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,hd]; rfl)
  rw [SharedPlacementAlphabet.setTape_append_right,bank_put] at h
  exact h

theorem copy_runs (c m D K rho ell q d G : ℕ) (v : Stage s) (rows : ℕ) :
    HoareTime copyProgram
      (fun z => z=(bank (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)).append (bank (initial v rows)))
      (fun z => z=(bank (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)).append
        (bank (raw v rows ell (precision c m d D K q)))) (copyCost ell (precision c m d D K q)) := by
  have h0 := copy_one (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)
    (initial v rows) 3 17 ell (by simp [CompactNativeRolePrecisionHeaders.prepared,
      CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,put,Function.update])
    (by simp [initial])
  have h1 := copy_one (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)
    (withEll v rows ell) 19 18 (precision c m d D K q)
    (by simp [CompactNativeRolePrecisionHeaders.prepared,put])
    (by simp [withEll,put,Function.update,initial])
  rw [raw_eq]
  exact h0.seq h1

theorem prepare_runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hrow : CompactGlobalRowPadding.rowAxes c m d≤D) (hDp : 0<D)
    (v : Stage s) (rows : ℕ) :
    HoareTime (prepareProgram c m)
      (fun z => z=(bank (CompactReservedHeaders.initial D K rho ell q d G)).append (bank (initial v rows)))
      (fun z => z=(bank (CompactReservedHeaders.initial D K rho ell q d G)).append
        (bank (raw v rows ell (precision c m d D K q)))) (prepareCost c m D K rho ell q d G) := by
  have h0 := hoare_extend_eq (CompactNativeRolePrecisionHeaders.runs c m D K rho ell q d G hc hm hd hK hrow hDp)
    (bank (initial v rows))
  have h1 := copy_runs c m D K rho ell q d G v rows
  have h2 := hoare_extend_eq (CompactNativeRolePrecisionHeaders.cleanup_runs c m D K rho ell q d G)
    (bank (raw v rows ell (precision c m d D K q)))
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
    (by unfold prepareCost;omega)

def cleanupSchedule : List CompactChildHeadersArithmetic.Op :=
  [.existing (.command (.erase 17)),.existing (.command (.erase 18))]
def cleanupProgram := (CompactChildHeadersArithmetic.compile (a:=2) cleanupSchedule).2
def cleanupCost (ell p : ℕ) := 100*(ell+1)+1+(100*(p+1)+1)

theorem cleanup_runs (v : Stage s) (rows ell p : ℕ) :
    HoareTime cleanupProgram (fun z => z=bank (raw v rows ell p))
      (fun z => z=bank (initial v rows)) (cleanupCost ell p) := by
  have hv : CompactChildHeadersArithmetic.validSchedule cleanupSchedule (raw v rows ell p) := by
    simp [cleanupSchedule,CompactChildHeadersArithmetic.validSchedule,CompactChildHeadersArithmetic.valid,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,raw_eq,withEll,put,Function.update]
  have he : CompactChildHeadersArithmetic.execute cleanupSchedule (raw v rows ell p)=initial v rows := by
    funext i
    fin_cases i <;> simp [cleanupSchedule,CompactChildHeadersArithmetic.execute,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,raw_eq,withEll,put,Function.update,initial]
  have ht : CompactChildHeadersArithmetic.scheduleCost cleanupSchedule (raw v rows ell p)=cleanupCost ell p := by
    simp [cleanupSchedule,CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,raw_eq,withEll,put,Function.update,cleanupCost]
  have h := CompactChildHeadersArithmetic.schedule_runs (a:=2) cleanupSchedule (raw v rows ell p) hv
  rw [he,ht] at h
  exact h


def cleanupLocalProgram := reindex (extend cleanupProgram 43) (finAddFlip (m:=43) (n:=43))

private theorem flip_append (x y : Tapes 43 2) :
    (x.append y).reindex (finAddFlip (m:=43) (n:=43))=y.append x := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=43) (n:=43) with
  | left i =>
    have he : (finAddFlip (m:=43) (n:=43)).symm (Fin.castAdd 43 i)=Fin.natAdd 43 i := by
      exact (Equiv.symm_apply_eq (finAddFlip (m:=43) (n:=43))).mpr
        (finAddFlip_apply_natAdd i 43).symm
    simp only [he,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i =>
    have he : (finAddFlip (m:=43) (n:=43)).symm (Fin.natAdd 43 i)=Fin.castAdd 43 i := by
      exact (Equiv.symm_apply_eq (finAddFlip (m:=43) (n:=43))).mpr
        (finAddFlip_apply_castAdd i 43).symm
    simp only [he,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem cleanup_local_runs (scalar : State) (v : Stage s) (rows ell p : ℕ) :
    HoareTime cleanupLocalProgram
      (fun z => z=(bank scalar).append (bank (raw v rows ell p)))
      (fun z => z=(bank scalar).append (bank (initial v rows))) (cleanupCost ell p) := by
  have h := hoare_reindex_eq (hoare_extend_eq (cleanup_runs v rows ell p) (bank scalar))
    (finAddFlip (m:=43) (n:=43))
  simpa only [flip_append,cleanupLocalProgram] using h

/-- The complete scalar synthesis, two physical installs and native cleanup
fit one uniform original native-volume allowance. -/
theorem lifecycle_linear (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    prepareCost c m D K rho ell q d G+cleanupCost ell (precision c m d D K q)≤
      (CompactReservationPaddingHeaderBudget.constant c m+5000)*CompactFallbackAxisRun.volume D K ell q := by
  let V := CompactFallbackAxisRun.volume D K ell q
  have hsyn := CompactNativeRoleScalarBudget.precision_linear c m D K rho ell q d G hc hm hd hG hK hD
  have hq := CompactNativeRoleScalarBudget.q_le_volume D K ell q
  have hs := CompactReservedVolumeBudget.dimension_square_le D K ell q
  change (D*K+1)^2≤V at hs
  have hB : D*K≤V := by nlinarith
  have hrow : CompactGlobalRowPadding.rowAxes c m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD;omega
  have hr := Nat.mul_le_mul_right K hrow
  have hp : precision c m d D K q≤5*V := by unfold precision;omega
  have hpol : 2^ell≤V := by
    have h := Nat.le_mul_of_pos_left (2^ell) (pow_pos (by decide : 0<2) (D*K))
    have h' := Nat.le_mul_of_pos_right (2^(D*K)*2^ell)
      (show 0<ButterflyAxisHeadersData.recordLength (D*K) (q+2*(D*K)) from by unfold ButterflyAxisHeadersData.recordLength;omega)
    exact h.trans h'
  have hel : ell≤V := (Nat.lt_two_pow_self (n:=ell)).le.trans hpol
  have hV : 0<V := ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  have hl0 := ActiveRepairRankHeadersCommands.bits_length ell
  have hl1 := ActiveRepairRankHeadersCommands.bits_length (precision c m d D K q)
  unfold prepareCost copyCost cleanupCost
  simp only [Nat.add_mul] at hsyn ⊢
  omega

end
end IntegerMultBounds.Machine.CompactComplexNativeCodec
