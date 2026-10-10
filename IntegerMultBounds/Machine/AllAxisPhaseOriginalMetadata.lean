import IntegerMultBounds.Machine.AllAxisPhaseOriginalScalar

/-! Complete paid physical setup of the aggregate phase metadata from native
original13 and retained ell. Numeric setup runs solely on the appended phase
bank; the native coefficient source and full caller workspace remain framed.
Cleanup erases computed headers, copied originals and copied ell. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseOriginalMetadata
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open Networks.Shared50ModularControl (prime)
open ActivePrefixStageHeadersData (Order)
open SharedPlacementAlphabet (setTape)
open AllAxisPhaseOriginalScalar (outer caller scalar initial words)
variable {s : Shape} {B : ℕ}

def tail (ell : ℕ) : Tapes 24 prime :=
  setTape (FixedHeaderBankCopy.empty 24) 22
    (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits ell)) 1

theorem initial_numeric (d : Inputs s) (ell : ℕ) :
    initial d ell=(ActiveRepairRankHeadersCommands.bank
      (ActivePrefixStageHeadersData.initial d.stage d.rows)).append (tail ell) := by
  unfold initial AllAxisPhaseOriginalPorts.phaseInitial
  rw [show (65 : Fin 67)=Fin.natAdd 43 (22 : Fin 24) from rfl,SharedPlacementAlphabet.setTape_append_right]
  rfl

def ready (order : Order) (d : Inputs s) (ell : ℕ) :=
  (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.finished order d.stage d.rows)).append (tail ell)
def metadataSetup (order : Order) :=
  Placement.placed (AllAxisPhaseStageMetadata.setup (a:=prime) (extra:=24) order)
    (finAddFlip : Fin (67+outer) ≃ Fin (outer+67))
def metadataCleanup :=
  Placement.placed (AllAxisPhaseStageMetadata.cleanup (a:=prime) (extra:=24))
    (finAddFlip : Fin (67+outer) ≃ Fin (outer+67))

private theorem right_frame {n q t a k : ℕ} {M : Program n q a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v=x) (fun v => v=y) k) (v : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+t) ≃ Fin (t+n)))
      (fun w => w=v.append x) (fun w => w=v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v=v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

theorem metadata_setup_runs (order : Order) (d : Inputs s) (xs : Rows d B) (ell : ℕ)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    HoareTime (metadataSetup order)
      (fun z => z=(caller d xs ell).append (initial d ell))
      (fun z => z=(caller d xs ell).append (ready order d ell))
      (ActivePrefixStageHeadersRun.cost order d.stage d.rows) := by
  have h := right_frame (AllAxisPhaseStageMetadata.setup_runs order d.stage d.rows (tail ell) d.hG ho)
    (caller d xs ell)
  simpa only [metadataSetup,initial_numeric,ready] using h

theorem metadata_cleanup_runs (order : Order) (d : Inputs s) (xs : Rows d B) (ell : ℕ) :
    HoareTime metadataCleanup
      (fun z => z=(caller d xs ell).append (ready order d ell))
      (fun z => z=(caller d xs ell).append (initial d ell))
      (AllAxisPhaseStageMetadata.cleanupCost order d.stage d.rows) := by
  have h := right_frame (AllAxisPhaseStageMetadata.cleanup_runs order d.stage d.rows (tail ell))
    (caller d xs ell)
  simpa only [metadataCleanup,initial_numeric,ready] using h

def setup (order : Order) := seq AllAxisPhaseOriginalScalar.setup (metadataSetup order)
def cleanup := seq metadataCleanup AllAxisPhaseOriginalScalar.cleanup

theorem setup_runs (order : Order) (d : Inputs s) (xs : Rows d B) (ell : ℕ)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    HoareTime (setup order)
      (fun z => z=(caller d xs ell).append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(caller d xs ell).append (ready order d ell))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words d ell)+1+
        ActivePrefixStageHeadersRun.cost order d.stage d.rows) :=
  (AllAxisPhaseOriginalScalar.setup_runs d xs ell).seq (metadata_setup_runs order d xs ell ho)

theorem cleanup_runs (order : Order) (d : Inputs s) (xs : Rows d B) (ell : ℕ) :
    HoareTime cleanup
      (fun z => z=(caller d xs ell).append (ready order d ell))
      (fun z => z=(caller d xs ell).append (FixedHeaderBankCopy.empty 67))
      (AllAxisPhaseStageMetadata.cleanupCost order d.stage d.rows+1+
        FixedHeaderBankCopy.cleanupCost (t:=outer) (words d ell)) :=
  (metadata_cleanup_runs order d xs ell).seq (AllAxisPhaseOriginalScalar.cleanup_runs d xs ell)

/-- Header copies, numeric synthesis and both cleanup lifecycles are paid. -/
theorem lifecycle_bound (order : Order) (d : Inputs s) (ell : ℕ)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (hR : 2^ell≤s.payload) :
    FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words d ell)+1+
      ActivePrefixStageHeadersRun.cost order d.stage d.rows+
      AllAxisPhaseStageMetadata.cleanupCost order d.stage d.rows+1+
      FixedHeaderBankCopy.cleanupCost (t:=outer) (words d ell)≤804268*(d.rows*s.recordWidth) := by
  have hs := AllAxisPhaseOriginalScalar.setup_bound order d ho ell hR
  have hc := AllAxisPhaseOriginalScalar.cleanup_bound order d ho ell hR
  have hm := AllAxisPhaseStageMetadata.lifecycle_bound order d.stage d.rows d.hG d.hGK ho d.hr d.hrecord
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  omega

end
end IntegerMultBounds.Machine.AllAxisPhaseOriginalMetadata
