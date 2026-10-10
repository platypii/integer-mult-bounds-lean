import IntegerMultBounds.Machine.NativeEndpointCharacterCopy
import IntegerMultBounds.Machine.NativeEndpointCharacterLifecycle
import IntegerMultBounds.Machine.NativeEndpointCharacterAddress

/-! One original-input endpoint character machine: physically copy retained
raw geometry, synthesize codec and role-row quotient privately, traverse the
actual selected role polynomial, and reclaim every private tape. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open NativeEndpointCharacterHeaders (tail)
open NativeEndpointCharacterLifecycle (metadataSetup metadataCleanup call resultCaller)
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

def prepare (c : ℕ) := Placement.placed (NativeEndpointCharacterPrepare.program c)
  (finAddFlip : Fin (67+t) ≃ Fin (t+67))
def program (focus : Fin 15 → Fin t) (src : Fin t) (c : ℕ) (order : Order)
    (m : ℕ) (ws : List (ZMod 4)) :=
  seq (NativeEndpointCharacterCopy.program focus) (seq (prepare c)
    (seq (metadataSetup order) (seq (call src m ws)
      (seq metadataCleanup (NativeEndpointCharacterHeaders.erase (t:=t))))))

def cost (c : ℕ) (order : Order) (v : Stage s) (parentRows ell p : ℕ) :=
  let v' := NativePolynomialStageShape.stage v ell p
  let rows := parentRows/c
  let w := NativePolynomialStageShape.width s p
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15)
    (NativeEndpointCharacterCopy.words v parentRows ell p)+1+
    (NativeEndpointCharacterPrepare.cost c v parentRows ell p+1+
      (ActivePrefixStageHeadersRun.cost order v' rows+1+
        (AllAxisPolynomialNative.cost order v' rows v.slots ell w+1+
          (AllAxisPhaseStageMetadata.cleanupCost order v' rows+1+
            FixedHeaderBankCopy.cleanupCost (t:=t) (NativeEndpointCharacterHeaders.words v' rows ell)))))

theorem runs (focus : Fin 15 → Fin t) (src : Fin t) (caller : Tapes t 2)
    (c : ℕ) (hc : 0<c) (order : Order) (v : Stage s) (parentRows ell p : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v) (hr : 0<parentRows/c)
    (ws : List (ZMod 4)) (hl : v.slots=ws.length)
    (xs : Fin (((parentRows/c)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=NativePolynomialStageShape.width s p ∧
      (xs i).2.length=NativePolynomialStageShape.width s p)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : caller.tape src=putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs))
    (hhead : caller.head src=0) :
    HoareTime (program focus src c order v.slots ws)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(resultCaller caller src (NativePolynomialStageShape.stage v ell p)
        v.slots ws xs).append (FixedHeaderBankCopy.empty 67))
      (cost (t:=t) c order v parentRows ell p) := by
  let v' := NativePolynomialStageShape.stage v ell p
  let rows := parentRows/c
  have hcopy := NativeEndpointCharacterCopy.runs focus caller v parentRows ell p hs hh
  have hprepare := right_frame (NativeEndpointCharacterPrepare.runs c hc v parentRows ell p hG hA hK) caller
  have ho' : ActivePrefixStageHeadersSchedule.Ordered order v' := ho
  have hg' : 1≤(NativePolynomialStageShape.shape s ell p).guard := hG
  have hsetup := right_frame (AllAxisPhaseStageMetadata.setup_runs order v' rows (tail ell) hg' ho') caller
  have hm : 0<v.slots := by have := v.source.isLt; omega
  have hcall := NativeEndpointCharacterLifecycle.call_runs src caller order v' rows hr v.slots ws
    hm le_rfl hl (NativeEndpointCharacterAddress.span v') ell (NativePolynomialStageShape.width s p)
    xs hw hsource hhead
  have hclean := right_frame (AllAxisPhaseStageMetadata.cleanup_runs order v' rows (tail ell))
    (resultCaller caller src v' v.slots ws xs)
  have herase := NativeEndpointCharacterHeaders.erase_runs (resultCaller caller src v' v.slots ws xs) v' rows ell
  exact hcopy.seq (hprepare.seq (hsetup.seq (hcall.seq (hclean.seq herase))))

end
end IntegerMultBounds.Machine.NativeEndpointCharacterOriginal
