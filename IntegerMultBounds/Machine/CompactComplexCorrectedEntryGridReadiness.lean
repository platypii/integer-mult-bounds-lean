import IntegerMultBounds.Machine.CompactComplexCorrectedEntryGeometryReadiness

/-! The actual canonical corrected source role family inherits its original
parent grid. Signed guards are derived from the genuine dependency Path;
neither a prepared role grid nor record-capacity assumptions are supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedEntryGridReadiness
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Wire Address)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexCorrectedEntryGeometryReadiness (data array)
variable {sh : Shape} {left k levels frames returned : ℕ}
attribute [local irreducible] roleCount

/-- The unique original parent coefficient selected by physical cyclic
splitting at this named role and immutable inner coordinate. -/
def parentIndex (rows ell : ℕ) (hd : roleCount∣rows) (a : Wire)
    (i : Fin (rows/CompactComplexScalarCountLifecycle.roleDivisor*(2^sh.bits*2^ell))) :
    Fin (rows*(2^sh.bits*2^ell)) :=
  let ij := finProdFinEquiv.symm (Fin.cast (NativeEndpointCharacterEntryRoles.cardinality sh rows ell) i)
  Fin.cast (CompactNativeRoleReservedBridge.grouped_cardinality rows roleCount
    (CompactNativeRoleOriginal.inner sh ell) hd)
    (RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack ij.1 (roleEncoding a)) ij.2)

theorem input_decoded (rows ell q n : ℕ) (hd : roleCount∣rows) (f : Array sh rows ell)
    (a : Wire) (i : Fin (rows/CompactComplexScalarCountLifecycle.roleDivisor*(2^sh.bits*2^ell))) :
    decoded sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q n
      (NativeEndpointCharacterEntryRoles.data rows ell hd f a) i=
      decoded sh rows ell q n f (parentIndex rows ell hd a i) := rfl

/-- Literal cyclic selection only chooses a coefficient of the original
parent array, leaving its signed words and denominator unchanged. -/
theorem input_grid (rows ell q n M : ℕ) (hd : roleCount∣rows) (f : Array sh rows ell)
    (hg : Grid sh rows ell q n M f) :
    ∀ a,Grid sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q n M
      (NativeEndpointCharacterEntryRoles.data rows ell hd f a) := by
  intro a i
  exact hg _

theorem input_width (rows ell q : ℕ) (hd : roleCount∣rows) (f : Array sh rows ell)
    (hw : Width sh rows ell q f) :
    ∀ a,Width sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q
      (NativeEndpointCharacterEntryRoles.data rows ell hd f a) := by
  intro a i
  exact hw _

/-- The exact source character endpoint keeps the genuine parent Path grid. -/
theorem grid (v : Stage sh) (hslots : v.slots=arity) (rows ell metadataP q : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    ∀ a,Grid sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (data v hslots rows ell metadataP hd f a) := by
  intro a
  rcases a with a | a
  · exact NativeEndpointCharacterPath.grid_from_path false v hslots ell metadataP
      (NativeEndpointCharacterEntryRoles.data rows ell hd f) a path p C n hp hchunk
      (input_width rows ell q hd f hw _) (input_grid rows ell q n _ hd f hg _)
  · exact input_grid rows ell q n _ hd f hg _

/-- Cardinality reinterpretation exposes the same signed grid on actual
original-quotient arrays consumed by the next event. -/
theorem array_grid (v : Stage sh) (hslots : v.slots=arity) (rows ell metadataP q : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    ∀ j,Grid sh (rows/roleCount) ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (array v hslots rows ell metadataP hd f j) := by
  intro j i
  exact grid v hslots rows ell metadataP q hd f path p C n hp hchunk hw hg _ _

/-- Exact decoded source action, including unchanged Y and scratch roles. -/
def sourceAction (v : Stage sh) (hslots : v.slots=arity) (ell metadataP : ℕ)
    (before : Wire → Fin N → ℂ) : Wire → Fin N → ℂ :=
  fun a i => match a with
    | Sum.inl b => Networks.BinaryPhase.phase
        ((NativeEndpointCharacterPath.phase false v hslots ell metadataP b i.val).val : ZMod 4)*before a i
    | Sum.inr _ => before a i

theorem decoded_source (v : Stage sh) (hslots : v.slots=arity) (rows ell metadataP q : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    (fun a => decoded sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q n
      (data v hslots rows ell metadataP hd f a))=
    sourceAction v hslots ell metadataP
      (fun a => decoded sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q n
        (NativeEndpointCharacterEntryRoles.data rows ell hd f a)) := by
  funext a
  rcases a with a | a
  · exact NativeEndpointCharacterPath.decoded_from_path false v hslots ell metadataP
      (NativeEndpointCharacterEntryRoles.data rows ell hd f) a path p C n hp hchunk
      (input_width rows ell q hd f hw _) (input_grid rows ell q n _ hd f hg _)
  · rfl

/-- Address readout uses the honest private polynomial codec shape. Its
payload is never substituted into the retained original raw caller headers. -/
def codecIndex (rows ell metadataP : ℕ)
    (i : Fin (rows*(2^sh.bits*2^ell))) :
    Fin (rows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth) :=
  ⟨(i.val/2^ell)*NativePolynomialStageShape.payload sh ell metadataP,by
    have hR : 0<2^ell := pow_pos (by decide) _
    have hi : i.val/2^ell<rows*2^sh.bits :=
      (Nat.div_lt_iff_lt_mul hR).2 (by simpa only [Nat.mul_assoc] using i.isLt)
    have hP : 0<NativePolynomialStageShape.payload sh ell metadataP :=
      lt_of_lt_of_le (by omega : 0<sh.bits+1) (NativePolynomialStageShape.payload_fits sh ell metadataP)
    have h := Nat.mul_lt_mul_of_pos_right hi hP
    change (i.val/2^ell)*NativePolynomialStageShape.payload sh ell metadataP<
      rows*(2^sh.bits*NativePolynomialStageShape.payload sh ell metadataP)
    simpa only [Nat.mul_assoc] using h⟩

def coordinates (v : Stage sh) (hslots : v.slots=arity) (rows ell metadataP : ℕ)
    (i : Fin (rows*(2^sh.bits*2^ell))) : Networks.BinaryColumns.Address (25^3) v.f :=
  fun j => NativeEndpointCharacterReadout.coordinates (NativePolynomialStageShape.stage v ell metadataP)
    (codecIndex rows ell metadataP i) j ∘ finCongr hslots.symm

private theorem chi_cast {m n : ℕ} (h : m=n) (u : Networks.BinaryWalsh.Address n)
    (x : Networks.BinaryWalsh.Address m) :
    Networks.BinaryWalsh.chi (u ∘ finCongr h) x=
      Networks.BinaryWalsh.chi u (x ∘ finCongr h.symm) := by
  subst n
  rfl

/-- The physical runtime source phase is the actual exceptional-network
terminal character, at the unique original address read from its coefficient. -/
theorem phase_character (v : Stage sh) (hslots : v.slots=arity) (rows ell metadataP : ℕ)
    (b : Address) (i : Fin (rows*(2^sh.bits*2^ell))) :
    Networks.BinaryPhase.phase
      ((NativeEndpointCharacterPath.phase false v hslots ell metadataP b i.val).val : ZMod 4)=
    ∏ j : Fin v.f,Networks.BinaryWalsh.chi (Networks.ComplexEndpoints.terminalVector b)
      (coordinates v hslots rows ell metadataP i j) := by
  have hP : 0<NativePolynomialStageShape.payload sh ell metadataP :=
    lt_of_lt_of_le (by omega : 0<sh.bits+1) (NativePolynomialStageShape.payload_fits sh ell metadataP)
  have h := NativeEndpointCharacterReadout.character (NativePolynomialStageShape.stage v ell metadataP)
    (NativeEndpointCharacterTerminal.vector (NativePolynomialStageShape.stage v ell metadataP) hslots b)
    (codecIndex rows ell metadataP i)
  have hdiv : i.val/2^ell*NativePolynomialStageShape.payload sh ell metadataP/
      (NativePolynomialStageShape.shape sh ell metadataP).payload=i.val/2^ell :=
    Nat.mul_div_cancel _ hP
  have hweights : NativeEndpointCharacterReadout.weights (NativePolynomialStageShape.stage v ell metadataP)
      (NativeEndpointCharacterTerminal.vector (NativePolynomialStageShape.stage v ell metadataP) hslots b)=
      NativeEndpointCharacterTerminal.terminalWeights v hslots b := rfl
  have hm : (NativePolynomialStageShape.stage v ell metadataP).slots=arity := hslots
  simp only [codecIndex,hdiv,hweights] at h
  conv_lhs at h => rw [hm]
  change Networks.BinaryPhase.phase
      ((NativeEndpointCharacterPath.phase false v hslots ell metadataP b i.val).val : ZMod 4)=_ at h
  rw [h]
  apply Finset.prod_congr rfl
  intro j _
  exact chi_cast hslots _ _

/-- Given the actual parent decoder's network-input relation, the reached
signed family is exactly the original corrected-network input at every role. -/
theorem decoded_correctInput (v : Stage sh) (hslots : v.slots=arity) (rows ell metadataP q : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (stored : Wire → Networks.BinaryColumns.Arrays (25^3) v.f)
    (hin : ∀ a i,decoded sh rows ell q n f (parentIndex rows ell hd a i)=
      stored a (coordinates v hslots (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell metadataP i)) :
    ∀ a i,decoded sh (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell q n
      (data v hslots rows ell metadataP hd f a) i=
      Networks.ComplexEndpoints.correctInput v.f stored a
        (coordinates v hslots (rows/CompactComplexScalarCountLifecycle.roleDivisor) ell metadataP i) := by
  have h := decoded_source v hslots rows ell metadataP q hd f path p C n hp hchunk hw hg
  intro a i
  rw [congrFun (congrFun h a) i]
  rcases a with a | a | a
  · change Networks.BinaryPhase.phase
        ((NativeEndpointCharacterPath.phase false v hslots ell metadataP a i.val).val : ZMod 4)*_=_
    dsimp only
    rw [phase_character,input_decoded,hin]
    exact (Networks.ComplexEndpoints.signColumns_apply _ _ _ _).symm
  · exact (input_decoded rows ell q n hd f _ _).trans (hin _ _)
  · exact (input_decoded rows ell q n hd f _ _).trans (hin _ _)

end
end IntegerMultBounds.Machine.CompactComplexCorrectedEntryGridReadiness
