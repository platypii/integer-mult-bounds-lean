module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSeedLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryNormalizationLayout

/-! Borrow selector geometry for scalar generation before selection starts.
Computed masters occupy the initially blank selector table and are retired
before selection. The numerical and physical seed banks are disjoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast.TableVM
noncomputable section

private theorem geometry_injective : Function.Injective geometry :=
  selector_injective.comp LocalRecoveryLayout.geometry_injective

def seedScalar (r : TblR 25) : Fin tapes :=
  geometry ⟨32+(PackedRecoveryNormalization.scalar r).val, by
    have h := PackedRecoveryNormalization.scalar_range r
    omega⟩

def seedMaster (i : Fin 10) : Fin tapes := geometry ⟨i.val,by omega⟩
def seedParameter (i : Fin 8) : Fin tapes := geometry ⟨80+i.val,by omega⟩

theorem seedScalar_injective : Function.Injective seedScalar := by
  intro r t h
  have hv := congrArg Fin.val (geometry_injective h)
  apply PackedRecoveryNormalization.scalar_injective
  exact Fin.ext (by simpa only [seedScalar,Fin.val_mk,Nat.add_right_inj] using hv)

theorem seedMaster_injective : Function.Injective seedMaster := by
  intro i j h
  exact Fin.ext (congrArg (Fin.val : Fin 117 → ℕ) (geometry_injective h))

theorem seedScalar_ne_master (i : Fin 10) (r : TblR 25) : seedScalar r ≠ seedMaster i := by
  intro h
  have hv := congrArg Fin.val (geometry_injective h)
  have hr := PackedRecoveryNormalization.scalar_range r
  change 32+(PackedRecoveryNormalization.scalar r).val = i.val at hv
  omega

theorem seedScalar_ne_queue (r : TblR 25) : seedScalar r ≠ geometry 90 := by
  intro h
  have hv := congrArg Fin.val (geometry_injective h)
  have hr := PackedRecoveryNormalization.scalar_range r
  change 32+(PackedRecoveryNormalization.scalar r).val = 90 at hv
  omega

def seedGenerator : CyclicSeedLayout tapes where
  rg := seedScalar
  rgInjective := seedScalar_injective
  source := seedParameter
  masters := seedMaster
  mastersInjective := seedMaster_injective
  word := geometry 88
  saved := caller.saved
  tmp := caller.tmp
  queue := geometry 90
  carry := geometry 89
  zero := geometry 37
  precision := geometry 31
  packet := geometry 94
  replicas := aux 7
  separated := seedScalar_ne_master
  registers := by
    intro i
    simp [seedParameter,seedScalar,PackedRecoveryNormalization.scalar,caller,
      geometry,selector,aux,port_injective.eq_iff,LocalRecoveryLayout.geometry_injective.eq_iff,
      List.nodup_cons,Fin.ext_iff]
    omega
  queueOff := seedScalar_ne_queue
  zeroOff := by
    intro i h
    have hv := congrArg Fin.val (geometry_injective h)
    change i.val = 37 at hv
    omega
  seedOff := by
    intro i
    simp [seedMaster,geometry,selector,aux,port_injective.eq_iff,
      LocalRecoveryLayout.geometry_injective.eq_iff,Fin.ext_iff]
    omega

/-- All generated seed sources live in selector geometry or the retained ruler. -/
theorem seedGenerator_sources_ne (r : Fin tapes)
    (hgeometry : ∀ i, geometry i ≠ r) (hreplicas : aux 7 ≠ r) :
    (∀ i, seedGenerator.left i ≠ r) ∧ (∀ i, seedGenerator.right i ≠ r) := by
  constructor
  · intro i
    apply recoverySeedSources_ne
    · intro j; exact hgeometry _
    · exact hgeometry _
    · exact hgeometry _
    · exact hreplicas
  · intro i
    apply recoverySeedSources_ne
    · intro j
      change (if j.val < 8 then seedMaster j else geometry 37) ≠ r
      split_ifs <;> exact hgeometry _
    · exact hgeometry _
    · exact hgeometry _
    · exact hreplicas

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
