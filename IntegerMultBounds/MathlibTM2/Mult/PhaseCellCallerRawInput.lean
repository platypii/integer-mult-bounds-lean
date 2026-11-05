module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerMovementControls

/-! The raw retained-counter contract is stable while movement controls are
allocated. This packages the shared hypotheses for connected caller execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

structure RawInput (T A D p u l target s t B W N radius width Vg Vr : ℕ)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T)
    (S : Stacks (MachineTapes T) A) : Prop where
  widthOff : ∀ i, src i ≠ widthSource
  widthLength : (S.R (unarySource T widthSource)).length = D
  values : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i
  widths : ∀ f, (S.R (unarySource T (widths f))).length = formatWidths B Vg Vr f
  scalarBlank : ∀ i, S.R (globals T i) = []
  rulerBlank : ∀ f, S.R (rulers T f) = []
  geometryBlank : ∀ f i, S.R (fullHeader T (.geometry f i)) = []
  ownedBlank : ∀ r ∈ ownedRoles, S.R (fullHeader T r) = []
  zeroBlank : S.R (fullHeader T .zero) = []
  routingBlank : ∀ i, S.R (Fin.natAdd ((T+headerCount)+175) i) = []
  widthPositive : 0 < width
  geometryFit : width+2*radius < 2^D
  fit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D
  bitsFit : ∀ f, formatWidths B Vg Vr f ≤ D

namespace RawInput

theorem reframeMovement {src : Fin 11 → Fin T} {widthSource : Fin T} {widths : Fin 3 → Fin T}
    {S F : Stacks (MachineTapes T) A}
    (raw : RawInput T A D p u l target s t B W N radius width Vg Vr src widthSource widths S)
    (hframe : ∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume → F.R k = S.R k) :
    RawInput T A D p u l target s t B W N radius width Vg Vr src widthSource widths F := by
  have hp (k : Fin T) : F.R (unarySource T k) = S.R (unarySource T k) :=
    hframe _ (fullHeader_ne_bank id .word k).symm (fullHeader_ne_bank id .replicas k).symm
      (fullHeader_ne_bank id .volume k).symm
  have hh (r : Role) (hw : r ≠ .word) (hr : r ≠ .replicas) (hv : r ≠ .volume) :
      F.R (fullHeader T r) = S.R (fullHeader T r) :=
    hframe _ ((fullHeader_injective T).ne hw) ((fullHeader_injective T).ne hr) ((fullHeader_injective T).ne hv)
  refine {raw with
    widthLength := (congrArg List.length (hp widthSource)).trans raw.widthLength
    values := fun i => (congrArg List.length (hp (src i))).trans (raw.values i)
    widths := fun f => (congrArg List.length (hp (widths f))).trans (raw.widths f)
    scalarBlank := ?_
    rulerBlank := ?_
    geometryBlank := ?_
    ownedBlank := ?_
    zeroBlank := ?_
    routingBlank := ?_}
  · intro i
    exact (hh (.scalar i) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)).trans (raw.scalarBlank i)
  · intro f
    exact (hh (.ruler f) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)).trans (raw.rulerBlank f)
  · intro f i
    exact (hh (.geometry f i) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)).trans (raw.geometryBlank f i)
  · intro r hr
    exact (hh r (retained_ne_owned .word rfl r hr).symm (retained_ne_owned .replicas rfl r hr).symm
      (retained_ne_owned .volume rfl r hr).symm).trans (raw.ownedBlank r hr)
  · exact (hh .zero (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)).trans raw.zeroBlank
  · intro i
    exact (hframe _ (prefix_ne_routing (Fin.castAdd 175 (header T .word)) i).symm
      (prefix_ne_routing (Fin.castAdd 175 (header T .replicas)) i).symm
      (prefix_ne_routing (Fin.castAdd 175 (header T .volume)) i).symm).trans (raw.routingBlank i)

end RawInput
end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
