import IntegerMultBounds.Machine.CompactNativeRoleReservedBridge
import IntegerMultBounds.Machine.CompactComplexChildGridPromoted
import IntegerMultBounds.Machine.CompactFramedScalarGrid
import IntegerMultBounds.Machine.CompactComplexScalarPathGuard

/-! Reconstruct the genuine globally reserved coefficient array from current
role streams. Stopped child arithmetic retains the exact scalar prefix rather
than replacing it by a fresh whole-network growth allowance. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedEventProgress
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open ButterflyStreamData (Coefficient)
open RecursiveInterchangeRows (pack)

def join {n c L : ℕ} (before : Fin c → Fin (n*L) → Coefficient) :
    CompactNativeRoleGeometry.Array n c L := fun z =>
  let ijk := finProdFinEquiv.symm z
  let ij := finProdFinEquiv.symm ijk.1
  before ij.2 (pack ij.1 ijk.2)

theorem role_join {n c L : ℕ} (before : Fin c → Fin (n*L) → Coefficient)
    (j : Fin c) : CompactNativeRoleGeometry.role (join before) j = before j := by
  funext z
  simp only [CompactNativeRoleGeometry.role,join,pack,Equiv.symm_apply_apply]
  exact congrArg (before j) (finProdFinEquiv.apply_symm_apply z)

def reserved (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (before : Fin c → Array s (rows/c) ell) : Array s rows ell := fun z =>
  join before (Fin.cast
    (CompactNativeRoleReservedBridge.grouped_cardinality rows c
      (CompactNativeRoleOriginal.inner s ell) hd).symm z)

theorem grouped_reserved (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (before : Fin c → Array s (rows/c) ell) :
    CompactNativeRoleReservedBridge.grouped s rows c ell hd
      (reserved s rows c ell hd before) = join before := by
  funext i
  unfold CompactNativeRoleReservedBridge.grouped reserved
  exact congrArg (join before) (Fin.ext rfl)

theorem reserved_role (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (before : Fin c → Array s (rows/c) ell) (j : Fin c) :
    CompactNativeRoleReservedBridge.role s rows c ell hd
      (reserved s rows c ell hd before) j = before j := by
  unfold CompactNativeRoleReservedBridge.role
  rw [grouped_reserved,role_join]

theorem reserved_width (s : Shape) (rows c ell w : ℕ) (hd : c ∣ rows)
    (before : Fin c → Array s (rows/c) ell)
    (hw : ∀ j i,(before j i).1.length=w ∧ (before j i).2.length=w) :
    ∀ i,(reserved s rows c ell hd before i).1.length=w ∧
      (reserved s rows c ell hd before i).2.length=w := by
  intro i
  exact hw _ _

theorem reserved_grid (s : Shape) (rows c ell q n M : ℕ) (hd : c ∣ rows)
    (before : Fin c → Array s (rows/c) ell)
    (hg : ∀ j,Grid s (rows/c) ell q n M (before j)) :
    Grid s rows ell q n M (reserved s rows c ell hd before) := by
  intro i
  exact hg _ _

def payload (s : Shape) (rows c ell : ℕ)
    (before : Fin c → Array s rows ell) :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (before j)))
    0 (fun _ => 0)

theorem reserved_payload (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (before : Fin c → Array s (rows/c) ell) :
    CompactNativeRoleReservedBridge.rolePayload s rows c ell hd
      (reserved s rows c ell hd before) = payload s (rows/c) c ell before := by
  unfold CompactNativeRoleReservedBridge.rolePayload payload
  simp only [reserved_role]

theorem prefix_return_bound (g p C levels frames returned axes gap : ℕ) :
    CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*4^gap ≤
    CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+gap)+axes)) := by
  have he : CompactRecursiveGridBudget.bound p C levels
      (frames+2*(returned+gap)+axes) =
      CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)*4^(2*gap) := by
    unfold CompactRecursiveGridBudget.bound
    rw [show frames+2*(returned+gap)+axes =
      (frames+2*returned+axes)+2*gap by omega,pow_add]
    ring
  unfold CompactFramedScalarGrid.bound
  rw [he]
  conv_lhs => rw [Networks.GaussianPrecision.scalarBound_linear]
  conv_rhs => rw [Networks.GaussianPrecision.scalarBound_linear]
  have hp : 4^gap ≤ 4^(2*gap) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ ≤ (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)*
      Networks.GaussianPrecision.scalarBound 1 52
        (Networks.RationalScalarGrid.castRows (CompactFramedScalarGrid.rows g)) 1)*4^(2*gap) :=
      Nat.mul_le_mul_left _ hp
    _ = _ := by ring

/-- Retained original precision and the dependency Path pay the stopped
child guard even after the current node's actual scalar-prefix growth. -/
theorem prefix_guard_from_path {s : Shape} {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path s.active left k levels frames returned)
    (g p C axes gap metadataP : ℕ) (ha : 0<s.active)
    (hp : p+2*s.bits≤metadataP) (haxes : axes+gap≤s.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤s.chunk) :
    4*(CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*4^gap) <
      2^(half s (metadataP-2*s.bits)) := by
  have hprefix := CompactFramedScalarGrid.bound_le g
    (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)) C hC
  have he : CompactRecursiveGridBudget.bound p C levels
      (frames+2*returned+axes)*C*4^gap =
      CompactComplexScalarPathGuard.budget p C levels frames returned (axes+gap) := by
    unfold CompactComplexScalarPathGuard.budget CompactRecursiveGridBudget.bound
    rw [pow_succ,pow_add,pow_add]
    ring
  have hb := CompactComplexScalarPathGuard.growth_power path p C (axes+gap)
  have hr := CompactComplexScalarPathGuard.stored_guard s p C (axes+gap)
    metadataP ha hp haxes hroom
  have hbits : 2≤CompactComplexScalarIntegerRows.guardBits := by
    unfold CompactComplexScalarIntegerRows.guardBits
    have hbase : 3≤CompactComplexScalarIntegerRows.growthConstant+1 := by
      unfold CompactComplexScalarIntegerRows.growthConstant
      omega
    have hpow := Nat.le_pow_clog (by decide : 1<2)
      (CompactComplexScalarIntegerRows.growthConstant+1)
    by_contra h
    have hh : Nat.clog 2 (CompactComplexScalarIntegerRows.growthConstant+1)≤1 := by omega
    have hm := Nat.pow_le_pow_right (by decide : 0<2) hh
    norm_num at hm
    omega
  have hhalf : ButterflyGuard.halfWidth metadataP s.bits =
      half s (metadataP-2*s.bits) := by
    unfold half ButterflyGuard.halfWidth
    omega
  have hpw : CompactComplexScalarPathGuard.power s p C (axes+gap)+2 ≤
      half s (metadataP-2*s.bits) := by omega
  calc
    _ ≤ 4*(CompactRecursiveGridBudget.bound p C levels
        (frames+2*returned+axes)*C*4^gap) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ hprefix)
    _ = 4*CompactComplexScalarPathGuard.budget p C levels frames returned (axes+gap) := by rw [he]
    _ < 4*2^(CompactComplexScalarPathGuard.power s p C (axes+gap)) :=
      Nat.mul_lt_mul_of_pos_left hb (by decide)
    _ = 2^(CompactComplexScalarPathGuard.power s p C (axes+gap)+2) := by
      rw [pow_add]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hpw

/-- A concrete stopped child and literal spectator numerator shifts preserve
the current named scalar prefix, advancing only the returned-child budget. -/
theorem stopped_prefix_grid {ι : Type*} [DecidableEq ι]
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit s.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before : ι → Array s rows ell) (g p C levels frames returned axes n : ℕ)
    (hw : ∀ role,Width s rows ell q (before role))
    (hg : ∀ role,Grid s rows ell q n
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (before role))
    (hguard : 4*(CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*
      4^(CompactComplexRecursiveGeometry.arity^k)) < 2^(half s q)) :
    (∀ role,Grid s rows ell q (n+CompactComplexRecursiveGeometry.arity^k)
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels
          (frames+2*(returned+CompactComplexRecursiveGeometry.arity^k)+axes)))
      (CompactComplexChildGridPromoted.aligned s rows ell q rho visit dir selected before role)) ∧
    (∀ role,role≠selected →
      decoded s rows ell q (n+CompactComplexRecursiveGeometry.arity^k)
        (CompactComplexChildGridPromoted.aligned s rows ell q rho visit dir selected before role) =
      decoded s rows ell q n (before role)) := by
  let M := CompactFramedScalarGrid.bound g
    (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))
  let gap := CompactComplexRecursiveGeometry.arity^k
  have hd : gap≤half s q+1 := by
    have hb := CompactSpectatorLeafSemantics.count_le_bits s rho visit
    unfold gap half ButterflyGuard.halfWidth
    omega
  have hpromotion : M*2^gap<2^(half s q) := by
    have hp : 2^gap≤4^gap := Nat.pow_le_pow_left (by decide) gap
    have hm := Nat.mul_le_mul_left M hp
    have hfour : M*4^gap≤4*(M*4^gap) := by omega
    exact (hm.trans hfour).trans_lt hguard
  have hshared := CompactComplexChildGridAlignment.stopped_shared_grid
    s rows ell q n M rho visit dir selected before
    (CompactComplexChildGridPromoted.aligned s rows ell q rho visit dir selected before)
    (hw selected) hg hguard
    (by simp only [CompactComplexChildGridPromoted.aligned,ite_true])
    (fun role hr i => by
      simp only [CompactComplexChildGridPromoted.aligned,ite_eq_right hr]
      exact CompactComplexChildGridPromoted.promotes s rows ell q n M gap
        (before role) (hw role) (hg role) hd hpromotion i)
  refine ⟨?_,hshared.2⟩
  intro role i
  exact Networks.GaussianPrecision.bound_mono
    (prefix_return_bound g p C levels frames returned axes gap) (hshared.1 role i)

theorem stopped_prefix_from_path {ι : Type*} [DecidableEq ι]
    {s : Shape} (rows ell metadataP : ℕ) (rho : Fin s.chunk)
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path s.active left k levels frames returned)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : ι)
    (before : ι → Array s rows ell) (g p C axes n : ℕ) (ha : 0<s.active)
    (hp : p+2*s.bits≤metadataP)
    (haxes : axes+CompactComplexRecursiveGeometry.arity^k≤s.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤s.chunk)
    (hw : ∀ role,Width s rows ell (metadataP-2*s.bits) (before role))
    (hg : ∀ role,Grid s rows ell (metadataP-2*s.bits) n
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (before role)) :
    (∀ role,Grid s rows ell (metadataP-2*s.bits) (n+CompactComplexRecursiveGeometry.arity^k)
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels
          (frames+2*(returned+CompactComplexRecursiveGeometry.arity^k)+axes)))
      (CompactComplexChildGridPromoted.aligned s rows ell (metadataP-2*s.bits)
        rho path.visit dir selected before role)) ∧
    (∀ role,role≠selected →
      decoded s rows ell (metadataP-2*s.bits) (n+CompactComplexRecursiveGeometry.arity^k)
        (CompactComplexChildGridPromoted.aligned s rows ell (metadataP-2*s.bits)
          rho path.visit dir selected before role) =
      decoded s rows ell (metadataP-2*s.bits) n (before role)) :=
  stopped_prefix_grid s rows ell (metadataP-2*s.bits) rho path.visit dir selected before
    g p C levels frames returned axes n hw hg
    (prefix_guard_from_path path g p C axes _ metadataP ha hp haxes hC hroom)

end
end IntegerMultBounds.Machine.CompactComplexStoppedEventProgress
