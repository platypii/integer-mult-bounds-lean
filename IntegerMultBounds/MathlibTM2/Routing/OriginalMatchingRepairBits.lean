module

public import IntegerMultBounds.MathlibTM2.Routing.ProfilePlacedMatching
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInputSemantics

/-! Physical matching semantics of the actual generated/placed rank permutation.
The alignment premises connect table-generation geometry to executed placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {t₀ Q K : ℕ} {P P' U : Type}

/-- Width equality forces the middle-table producer and repair to use the same
field; the slot equality ties their actual physical placement together. -/
theorem GeneratedPlacedInput.originalMatching_perm_shear
    (input : GeneratedPlacedInput t₀ Q K P P' U)
    (hslot : input.slotWidth = input.p.wc)
    (hwidth : input.p.wy = fieldsLen (selectiveLen input.p input.X) - 3 * input.p.wc)
    (mate : Fin (fieldsLen (selectiveLen input.p input.X)) → Fin (fieldsLen (selectiveLen input.p input.X)))
    (hinv : Function.Involutive mate)
    (hsource : input.source = fun q => Fin.cast hwidth.symm
      (reservoirClassLocalMatching (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit
        input.p.wc (by rw [← hslot]; exact input.hslotWidth) input.reservoir mate hinv (Fin.cast hwidth q)))
    (reverse : Bool) (htargets : input.targets = matchingDirectionTargets input.source reverse)
    (i : Fin (input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))) :
    let e := reservoirPlacement (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit
      input.p.wc (by rw [← hslot]; exact input.hslotWidth) input.reservoir
    (fun q => (input.perm i).val.testBit q.val) =
      shear (placedSelectiveTargets input.p input.X input.hK (profileActive input.p input.hK input.targets) e)
        (matchingClass (routingReservoir (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit)
          mate input.reservoir) (fun q => i.val.testBit q.val) := by
  have hw : input.p.wc ≤ input.Hslot := by rw [← hslot]; exact input.hslotWidth
  let n := fieldsLen (selectiveLen input.p input.X)
  have hsourceInv : Function.Involutive input.source := by
    rw [hsource]
    intro q
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
    rw [reservoirClassLocalMatching_involutive]
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  have hallowed : ∀ q ∈ input.targets, input.source q ∉ input.targets := by
    rw [htargets]
    exact matchingDirectionTargets_source input.source hsourceInv reverse
  let e := reservoirPlacement n input.Hslot input.hplacementFit input.p.wc hw input.reservoir
  let f := reservoirExchangeRank n input.Hslot input.hplacementFit input.p.wc hw input.reservoir input.R
  let cls := matchingClass (routingReservoir n input.Hslot input.hplacementFit) mate input.reservoir
  have hcoordinate : ∀ q, e (profileMiddleCoordinate input.p input.X (input.source q)) =
      cls (e (profileMiddleCoordinate input.p input.X q)) := by
    intro q
    rw [hsource]
    exact reservoirProfileClassSource_coordinate input.p input.X input.Hslot input.hplacementFit hw
      input.reservoir mate hinv hwidth q
  have he := profilePlacedPerm_matching_shear input.hK input.targets input.source hallowed e f
    (reservoirExchangeRank_bit n input.Hslot input.hplacementFit input.p.wc hw input.reservoir input.R)
    cls hcoordinate i
  simpa only [GeneratedPlacedInput.perm, input.hactive, input.hsources, hslot] using he


/-- State physical matching semantics at the external record width. This avoids
forcing concrete router stages to rebuild their source table after a width cast. -/
theorem GeneratedPlacedInput.originalMatching_perm_shear_cast
    (input : GeneratedPlacedInput t₀ Q K P P' U) (n : ℕ)
    (hrecord : fieldsLen (selectiveLen input.p input.X) = n)
    (hslot : input.slotWidth = input.p.wc)
    (hwidth : input.p.wy = n - 3 * input.p.wc)
    (hfit : 9 * input.Hslot ≤ n) (hw : input.p.wc ≤ input.Hslot)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hsource : input.source = fun q => Fin.cast hwidth.symm
      (reservoirClassLocalMatching n input.Hslot hfit input.p.wc hw input.reservoir mate hinv (Fin.cast hwidth q)))
    (reverse : Bool) (htargets : input.targets = matchingDirectionTargets input.source reverse)
    (i : Fin (input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))) :
    (fun q : Fin n => (input.perm i).val.testBit q.val) =
      shear ((placedSelectiveTargets input.p input.X input.hK
        (profileActive input.p input.hK input.targets)
        (reservoirPlacement (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit
          input.p.wc hw input.reservoir)).image (Fin.cast hrecord))
        (matchingClass (routingReservoir n input.Hslot hfit) mate input.reservoir)
        (fun q => i.val.testBit q.val) := by
  subst n
  simpa only [Fin.cast_refl, Finset.image_id] using
    input.originalMatching_perm_shear hslot hwidth mate hinv hsource reverse htargets i


end
end IntegerMultBounds.MathlibTM2.Routing
