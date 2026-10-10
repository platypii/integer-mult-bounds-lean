import IntegerMultBounds.Machine.CompactComplexScalarRowBlock
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid

/-! Actual dependency growth pays the signed guard of the complete scalar row
machine on unchanged retained-role fields. The denominator is independent of
baseline width metadata. Current scalar-prefix growth and pending axis work
are included; physical precision propagation remains separate. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarPathGuard
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactRecursiveDependencyBudget
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open CompactComplexScalarIntegerRows (RowIndex guardBits signedRows gate)
open CompactComplexScalarRowBlock (wireCount records)
open ButterflySigned Networks.GaussianPrecision

/-- One current-node scalar-prefix allowance and pending axis work are added
to the actual ancestor/sibling dependency budget. -/
def budget (p C levels frames returned axes : ℕ) :=
  CompactRecursiveGridBudget.bound p C (levels+1) (frames+2*returned+axes)
def power (s : Shape) (p C axes : ℕ) :=
  p+dependencyCoefficient C*s.active+1+Nat.clog 2 (C+1)+2*axes

theorem growth_power {s : Shape} {left k levels frames returned : ℕ}
    (path : Path s.active left k levels frames returned) (p C axes : ℕ) :
    budget p C levels frames returned axes < 2^(power s p C axes) := by
  have hpath := path.guard p C
  have hC : C≤2^(Nat.clog 2 (C+1)) := (Nat.le_succ C).trans
    (Nat.le_pow_clog (by decide : 1<2) (C+1))
  have hpos : 0<2^(Nat.clog 2 (C+1))*4^axes := by positivity
  have he : budget p C levels frames returned axes=
      CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*(C*4^axes) := by
    unfold budget CompactRecursiveGridBudget.bound
    rw [pow_succ,pow_add]
    ring
  rw [he]
  calc
    _ ≤ CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*
        (2^(Nat.clog 2 (C+1))*4^axes) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hC)
    _ < 2^(p+dependencyCoefficient C*s.active+1)*
        (2^(Nat.clog 2 (C+1))*4^axes) := Nat.mul_lt_mul_of_pos_right hpath hpos
    _ = 2^(power s p C axes) := by
      rw [show 4^axes=2^(2*axes) by rw [show (4:ℕ)=2^2 by decide,pow_mul],
        ←Nat.mul_assoc,←pow_add,←pow_add]
      rfl

/-- The corrected retained width pays both dependency and current-prefix
work; no row-specific overflow allowance is supplied. -/
theorem stored_guard (s : Shape) (p C axes metadataP : ℕ) (ha : 0<s.active)
    (hp : p+2*s.bits≤metadataP) (haxes : axes≤s.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+guardBits≤s.chunk) :
    power s p C axes+guardBits≤ButterflyGuard.halfWidth metadataP s.bits := by
  have hm := Nat.mul_le_mul_right s.active
    (show dependencyCoefficient C≤s.chunk from by omega)
  have hdep : dependencyCoefficient C*s.active≤s.bits := by unfold Shape.bits; nlinarith
  have hK := Nat.le_mul_of_pos_left s.chunk ha
  have hbits : s.chunk≤s.bits := by unfold Shape.bits; nlinarith
  unfold power ButterflyGuard.halfWidth
  omega

/-- The real complete row machine runs with its uniform paid width bound and
its emitted Gaussian words have exact scalar semantics at inherited n+1.
The actual Path/grid and retained metadata supply every signed overflow guard. -/
theorem row_from_path {s : Shape} {left k levels frames returned : ℕ}
    (path : Path s.active left k levels frames returned) (r : RowIndex)
    (p C axes metadataP n : ℕ) (ha : 0<s.active)
    (hp : p+2*s.bits≤metadataP) (haxes : axes≤s.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+guardBits≤s.chunk)
    (xs ys : ℕ → List (Fin 2))
    (hx : ∀ j,(xs j).length=CompactNativeRoleHeaders.recordWidth s metadataP)
    (hy : ∀ j,(ys j).length=CompactNativeRoleHeaders.recordWidth s metadataP)
    (hg : ∀ i,BoundedGrid n (budget p C levels frames returned axes)
      (complexValue (signedRows (ButterflyGuard.halfWidth metadataP s.bits) xs i)
        (signedRows (ButterflyGuard.halfWidth metadataP s.bits) ys i) n))
    (fs : Fin wireCount → ℤ → Fin 6) (ps : Fin wireCount → ℤ) :
    HoareTime (CompactComplexScalarRowBlock.program r)
      (fun v => v=CompactComplexScalarRowBlock.bank r xs ys fs ps)
      (fun v => v=CompactComplexScalarRowBlock.output r xs ys fs ps)
      (CompactComplexScalarRowBlock.timeConstant*(CompactNativeRoleHeaders.recordWidth s metadataP+1)) ∧
    ∀ i : Fin wireCount,
      complexValue (signedValue (ButterflyGuard.halfWidth metadataP s.bits)
        (CompactComplexScalarWireEmit.word r (CompactComplexScalarIntegerRows.wireIndex.symm i) xs))
        (signedValue (ButterflyGuard.halfWidth metadataP s.bits)
          (CompactComplexScalarWireEmit.word r (CompactComplexScalarIntegerRows.wireIndex.symm i) ys)) (n+1)=
        (Networks.RationalScalarGrid.castGate (gate r)).run
          (fun j => complexValue (signedRows (ButterflyGuard.halfWidth metadataP s.bits) xs j)
            (signedRows (ButterflyGuard.halfWidth metadataP s.bits) ys j) n)
          (CompactComplexScalarIntegerRows.wireIndex.symm i) := by
  have hbudget := growth_power path p C axes
  have hguard := stored_guard s p C axes metadataP ha hp haxes hroom
  have hnum := fun i => ButterflyGuard.represented_bound _ _ n _ (hg i)
  have hreal : ∀ i,|signedRows (ButterflyGuard.halfWidth metadataP s.bits) xs i|≤
      ((2^(power s p C axes):ℕ):ℤ) := by
    intro i
    exact (hnum i).1.trans (Int.ofNat_le.mpr hbudget.le)
  have himag : ∀ i,|signedRows (ButterflyGuard.halfWidth metadataP s.bits) ys i|≤
      ((2^(power s p C axes):ℕ):ℤ) := by
    intro i
    exact (hnum i).2.trans (Int.ofNat_le.mpr hbudget.le)
  constructor
  · exact (CompactComplexScalarRowBlock.runs r xs ys _ hx hy fs ps).consequence
      (fun _ hv => hv) (fun _ hv => hv) (CompactComplexScalarRowBlock.time_bound r _)
  · intro i
    exact (CompactComplexScalarRowBlock.output_semantics r _ (power s p C axes) n xs ys
      hx hy hreal himag hguard i).1

/-- The fixed scalar/dependency room is eventually supplied by the original
chunk choice, rather than a permanent sufficiently-wide-fields premise. -/
theorem eventually_chunk_room (R : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, R≤Sizes.K n := by
  have hx := ((tendsto_rpow_atTop (mul_pos Sizes.epsilon_pos Sizes.spacing_pos)).comp
    TimeBound.tendsto_precision).eventually_ge_atTop (24*(R:ℝ))
  filter_upwards [hx,Sizes.eventually_K_ge] with n hlarge hk
  change 24*(R:ℝ)≤TimeBound.precision n^(Parameters.epsilon*Parameters.spacing) at hlarge
  have h : (R:ℝ)≤Sizes.K n := by nlinarith
  exact_mod_cast h

theorem eventually_scalar_room (C : ℕ) : ∀ᶠ n : ℕ in Filter.atTop,
    dependencyCoefficient C+Nat.clog 2 (C+1)+guardBits≤Sizes.K n :=
  eventually_chunk_room _

/-- Original corrected reservation metadata supplies the width baseline;
no extra per-row relation between that metadata and the true denominator is
assumed. The denominator itself remains the inherited grid's n. -/
theorem actual_retained_guard (c m d D G K p C axes : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (ha : 0<(CompactReservationNativeRows.shape c m d D G K).active)
    (haxes : axes≤(CompactReservationNativeRows.shape c m d D G K).bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+guardBits≤K) :
    power (CompactReservationNativeRows.shape c m d D G K) p C axes+guardBits≤
      ButterflyGuard.halfWidth (CompactNativeRoleReservedBridge.precision c m d D K p)
        (CompactReservationNativeRows.shape c m d D G K).bits := by
  have hw := CompactNativeRoleChildPrecision.actual_precision c m d D G K p hK hD
  have hp : p+2*(CompactReservationNativeRows.shape c m d D G K).bits≤
      CompactNativeRoleReservedBridge.precision c m d D K p := by omega
  exact stored_guard _ _ _ _ _ ha hp haxes hroom

end
end IntegerMultBounds.Machine.CompactComplexScalarPathGuard
