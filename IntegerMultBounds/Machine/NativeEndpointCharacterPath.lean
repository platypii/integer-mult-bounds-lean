import IntegerMultBounds.Machine.NativeEndpointCharacterNamedBank
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
import IntegerMultBounds.Networks.ComplexEndpointGrid

/-! Original Path guards justify every actual endpoint character coefficient;
the literal output preserves signed widths and the exact common dyadic grid. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexEndpointRoleExchange (Address Wire)
open NativeEndpointCharacterNamedRoles (role coefficients)
open NativeEndpointCharacterNamedBank (result)
open NativeEndpointCharacterRoles (arity)
open ButterflySigned (signedValue complexValue)
open Networks.GaussianPrecision
variable {sh : Shape} {rows ell q left k levels frames returned : ℕ}

def phase (_sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (b : Address) (i : ℕ) := AllAxisPolynomialLiteralEndpoint.phase
  (NativePolynomialStageShape.stage v ell p) arity
  (NativeEndpointCharacterTerminal.terminalWeights v hslots b) (i/2^ell)

theorem width (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (before : Wire → Array sh rows ell) (b : Address) (w : ℕ)
    (hw : ∀ i,(before (role sink b) i).1.length=w ∧ (before (role sink b) i).2.length=w)
    (i : Fin (rows*(2^sh.bits*2^ell))) :
    (result sink v hslots ell p before b i).1.length=w ∧
    (result sink v hslots ell p before b i).2.length=w := by
  exact AllAxisPolynomialLiteralEndpoint.result_width _ _ _ _ w
    (fun j => hw (Fin.cast (Nat.mul_assoc _ _ _) j)) _

theorem signed_decoded (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (before : Wire → Array sh rows ell) (a : Address) (b n : ℕ)
    (hw : ∀ i,(before (role sink a) i).1.length=b+1 ∧ (before (role sink a) i).2.length=b+1)
    (hg : ∀ i,|signedValue b (before (role sink a) i).1|<(2^b : ℕ) ∧
      |signedValue b (before (role sink a) i).2|<(2^b : ℕ)) (i : Fin (rows*(2^sh.bits*2^ell))) :
    complexValue (signedValue b (result sink v hslots ell p before a i).1)
      (signedValue b (result sink v hslots ell p before a i).2) n=
      Networks.BinaryPhase.phase ((phase sink v hslots ell p a i.val).val : ZMod 4)*
        complexValue (signedValue b (before (role sink a) i).1)
          (signedValue b (before (role sink a) i).2) n := by
  have h := UnitPhaseSigned.words_phase (phase sink v hslots ell p a i.val)
    (UnitPhasePolynomialArray.components (before (role sink a) i)) b n (by
      intro j
      unfold UnitPhasePolynomialArray.components
      split_ifs <;> first | exact (hw i).1 | exact (hw i).2) (by
      intro j
      fin_cases j <;> first | exact (hg i).1 | exact (hg i).2)
  simpa only [result,AllAxisPolynomialLiteralEndpoint.result,coefficients,Fin.cast_cast,
    Fin.cast_refl,Fin.val_cast,phase,UnitPhasePolynomialArray.components,id_eq,ite_true,
    show (1:ℕ)≠0 by decide,ite_false] using h

theorem decoded_from_path (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell metadataP : ℕ)
    (before : Wire → Array sh rows ell) (a : Address)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : Width sh rows ell q (before (role sink a)))
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before (role sink a))) :
    decoded sh rows ell q n (result sink v hslots ell metadataP before a)=
      fun i => Networks.BinaryPhase.phase ((phase sink v hslots ell metadataP a i.val).val : ZMod 4)*
        decoded sh rows ell q n (before (role sink a)) i := by
  funext i
  apply signed_decoded
  · intro j
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw j
  · exact fun j => CompactSpectatorInheritedGrid.signed_guards_from_path
      sh rows ell q path p C n hp hchunk (before (role sink a)) hg j

theorem grid_from_path (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell metadataP : ℕ)
    (before : Wire → Array sh rows ell) (a : Address)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : Width sh rows ell q (before (role sink a)))
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before (role sink a))) :
    Grid sh rows ell q n (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (result sink v hslots ell metadataP before a) := by
  intro i
  rw [decoded_from_path sink v hslots ell metadataP before a path p C n hp hchunk hw hg]
  exact bounded_I_pow_mul _ (hg i)

end
end IntegerMultBounds.Machine.NativeEndpointCharacterPath
