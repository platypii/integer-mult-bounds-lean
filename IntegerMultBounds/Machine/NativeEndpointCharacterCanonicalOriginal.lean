import IntegerMultBounds.Machine.NativeEndpointCharacterCanonical

namespace IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyAxisHeadersArithmetic
open NativeEndpointCharacterCanonical
variable {s : Shape} {t : ℕ}

private theorem right_frame {n q k : ℕ} {M : Program n q 2} {x y : Tapes n 2}
    (h : HoareTime M (fun z => z=x) (fun z => z=y) k) (caller : Tapes t 2) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+t) ≃ Fin (t+n)))
      (fun z => z=caller.append x) (fun z => z=caller.append y) k := by
  have he (z : Tapes n 2) : Placement.combine finAddFlip z caller=caller.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x caller)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun z hz => hz.trans (he x).symm) _ le_rfl
  rintro z ⟨u,hu,rfl⟩
  subst u
  simpa only [Placement.replace,Placement.extra_combine] using he y

def normalization := Placement.placed normalize (finAddFlip : Fin (67+t) ≃ Fin (t+67))
def program (focus : Fin 15 → Fin t) (src : Fin t) (c m : ℕ) (ws : List (ZMod 4)) :=
  seq (NativeEndpointCharacterCopy.program focus) (seq normalization
    (seq (NativeEndpointCharacterOriginal.prepare c)
      (seq (NativeEndpointCharacterLifecycle.metadataSetup .early)
        (seq (NativeEndpointCharacterLifecycle.call src m ws)
          (seq NativeEndpointCharacterLifecycle.metadataCleanup
            (NativeEndpointCharacterHeaders.erase (t:=t)))))))

def cost (c : ℕ) (v : Stage s) (rows ell p : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15)
    (NativeEndpointCharacterCopy.words v rows ell p)+1+
  (scheduleCost schedule (NativeEndpointCharacterPrepare.raw v rows ell p)+1+
  (NativeEndpointCharacterPrepare.cost c (stage v) rows ell p+1+
  (ActivePrefixStageHeadersRun.cost .early (NativePolynomialStageShape.stage (stage v) ell p) (rows/c)+1+
  (AllAxisPolynomialNative.cost .early (NativePolynomialStageShape.stage (stage v) ell p)
    (rows/c) v.slots ell (NativePolynomialStageShape.width s p)+1+
  (AllAxisPhaseStageMetadata.cleanupCost .early (NativePolynomialStageShape.stage (stage v) ell p) (rows/c)+1+
    FixedHeaderBankCopy.cleanupCost (t:=t) (NativeEndpointCharacterHeaders.words
      (NativePolynomialStageShape.stage (stage v) ell p) (rows/c) ell))))))

theorem runs (focus : Fin 15 → Fin t) (src : Fin t) (caller : Tapes t 2)
    (c : ℕ) (hc : 0<c) (v : Stage s) (rows ell p : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) (hr : 0<rows/c)
    (ws : List (ZMod 4)) (hl : v.slots=ws.length)
    (xs : Fin (((rows/c)*2^s.bits)*2^ell) → ButterflyStreamData.Coefficient)
    (hw : ∀ i,(xs i).1.length=NativePolynomialStageShape.width s p ∧
      (xs i).2.length=NativePolynomialStageShape.width s p)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v rows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : caller.tape src=putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs))
    (hhead : caller.head src=0) :
    HoareTime (program focus src c v.slots ws)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(NativeEndpointCharacterLifecycle.resultCaller caller src
        (NativePolynomialStageShape.stage v ell p) v.slots ws xs).append (FixedHeaderBankCopy.empty 67))
      (cost (t:=t) c v rows ell p) := by
  let v' := NativePolynomialStageShape.stage (stage v) ell p
  have hcopy := NativeEndpointCharacterCopy.runs focus caller v rows ell p hs hh
  have hnorm := right_frame (normalize_runs v rows ell p) caller
  have hprep := right_frame (NativeEndpointCharacterPrepare.runs c hc (stage v) rows ell p hG hA hK) caller
  have hsetup := right_frame (AllAxisPhaseStageMetadata.setup_runs .early v' (rows/c)
    (NativeEndpointCharacterHeaders.tail ell) hG (ordered v)) caller
  have hcall := NativeEndpointCharacterLifecycle.call_runs src caller .early v' (rows/c) hr v.slots ws
    (by have := two_slots v; omega) le_rfl hl (NativeEndpointCharacterAddress.span v') ell
    (NativePolynomialStageShape.width s p) xs hw hsource hhead
  have hclean := right_frame (AllAxisPhaseStageMetadata.cleanup_runs .early v' (rows/c)
    (NativeEndpointCharacterHeaders.tail ell)) (NativeEndpointCharacterLifecycle.resultCaller caller src v' v.slots ws xs)
  have herase := NativeEndpointCharacterHeaders.erase_runs
    (NativeEndpointCharacterLifecycle.resultCaller caller src v' v.slots ws xs) v' (rows/c) ell
  exact hcopy.seq (hnorm.seq (hprep.seq (hsetup.seq (hcall.seq (hclean.seq herase)))))

end
end IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginal
