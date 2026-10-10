import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientation

/-! Both placements of the orientation selector retain the original saved
frame. Width, inherited dyadic grid and source readiness propagate through
its actual conditional array transform; the fixed decoder cost is paid by
the complete native volume. Post-orientation runs before any return-PC pop. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientationInvariants
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexSourceReadyWorkspace (tapes)
open CompactComplexSourceReadyOrientation (source output program)
open NativePolynomialConjugationData (array)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyDirection.width
  ComplexRank25.program ComplexRecursiveCallSchema.sites

def oriented {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (f : Fin N → ButterflyStreamData.Coefficient) := if call.inverse then array f else f

theorem output_eq {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (f : Fin N → ButterflyStreamData.Coefficient)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    output call v f=setTape v source (NativeZeroPadding.word (NativeZeroPaddingArray.word (oriented call f))) 0 := by
  unfold output oriented
  split_ifs
  · rfl
  · rw [←hs,←hh,SharedPlacementAlphabet.setTape_self]

theorem output_source {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (f : Fin N → ButterflyStreamData.Coefficient)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    (output call v f).tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word (oriented call f)) ∧
    (output call v f).head source=0 := by
  rw [output_eq call v f hs hh]
  simp [setTape]

theorem output_frame {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (f : Fin N → ButterflyStreamData.Coefficient)
    (i : Fin (tapes s c)) (hi : i≠source) :
    (output call v f).head i=v.head i ∧ (output call v f).tape i=v.tape i := by
  unfold output
  split_ifs <;> simp [setTape,hi]

/-- The genuine saved-PC frame used before the forward node survives the
orientation scan unchanged and can select the same direction afterwards. -/
theorem output_saved {N : ℕ} (stack : Fin (tapes s c)) (hstack : stack≠source)
    (call : ComplexRecursiveCallSchema.Call) (v : Tapes (tapes s c) 2)
    (f : Fin N → ButterflyStreamData.Coefficient) :
    Placement.active (FiniteReturnStackAt.placement stack) (output call v f)=
      Placement.active (FiniteReturnStackAt.placement stack) v := by
  rw [FiniteReturnStackAt.active_bank,FiniteReturnStackAt.active_bank]
  rw [(output_frame call v f stack hstack).1,(output_frame call v f stack hstack).2]

theorem oriented_involutive {N : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (f : Fin N → ButterflyStreamData.Coefficient) : oriented call (oriented call f)=f := by
  unfold oriented
  split_ifs <;> first | exact NativePolynomialConjugationRows.array_involutive f | rfl

theorem oriented_width (call : ComplexRecursiveCallSchema.Call) (sh : Shape) (rows ell q : ℕ)
    (f : Array sh rows ell) (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f) :
    CompactSpectatorInheritedGrid.Width sh rows ell q (oriented call f) := by
  unfold oriented
  split_ifs
  · exact NativePolynomialConjugationRows.inherited_width sh rows ell q f hw
  · exact hw

private theorem bounded_star {n M : ℕ} {z : ℂ} (hz : GaussianPrecision.BoundedGrid n M z) :
    GaussianPrecision.BoundedGrid n M (star z) := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  refine ⟨a,-b,?_,ha,by simpa only [abs_neg] using hb⟩
  have hc := congrArg star he
  simpa using hc

theorem oriented_decoded {sh : Shape} {rows ell q left k levels frames returned : ℕ}
    (call : ComplexRecursiveCallSchema.Call)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    CompactSpectatorInheritedGrid.decoded sh rows ell q n (oriented call f)=
      fun i => if call.inverse then star (CompactSpectatorInheritedGrid.decoded sh rows ell q n f i)
        else CompactSpectatorInheritedGrid.decoded sh rows ell q n f i := by
  unfold oriented
  split_ifs
  · exact NativePolynomialConjugationRows.decoded_from_path path p C n hp hchunk f hw hg
  · rfl

theorem oriented_grid {sh : Shape} {rows ell q left k levels frames returned : ℕ}
    (call : ComplexRecursiveCallSchema.Call)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (oriented call f) := by
  intro i
  have he := congrFun (oriented_decoded call path p C n hp hchunk f hw hg) i
  change GaussianPrecision.BoundedGrid _ _ _
  rw [he]
  split_ifs
  · exact bounded_star (hg i)
  · exact hg i

def constant := 2*CompactComplexSourceReadyDirection.width+11

theorem cost_linear (sh : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    2*CompactComplexSourceReadyDirection.width+6+5*CompactNativeRoleTransferBudget.volume rows sh ell p≤
      constant*CompactNativeRoleTransferBudget.volume rows sh ell p := by
  have hp := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  change 0<CompactNativeRoleTransferBudget.volume rows sh ell p at hp
  have hm := Nat.mul_le_mul_right (2*CompactComplexSourceReadyDirection.width+6) (Nat.succ_le_of_lt hp)
  unfold constant
  nlinarith

/-- The actual controller's saved call-PC slot in the shared source-ready bank. -/
def savedSlot (pcStack : Fin s) : Fin (tapes s c) :=
  Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
    (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 pcStack)))

theorem savedSlot_ne_source (pcStack : Fin s) : savedSlot (c:=c) pcStack≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [savedSlot,source,NativePolynomialConjugationWorkspace.source,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem retained_savedSlot {N : ℕ} (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (f : Fin N → ButterflyStreamData.Coefficient) :
    Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (output call v f)=
      Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) v :=
  output_saved _ (savedSlot_ne_source pcStack) call v f

/-- This same paid physical theorem applies before the full corrected forward
node and after it, while its original saved frame remains on the stack. -/
theorem runs_linear (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older p (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (p+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (sh : Shape) (rows ell precision : ℕ) (hr : 0<rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    HoareTime (program stack) (fun w => w=v) (fun w => w=output call v f)
      (constant*CompactNativeRoleTransferBudget.volume rows sh ell precision) :=
  (CompactComplexSourceReadyOrientation.runs_saved stack call v older p hstack sh rows ell precision hr f hw hs hh).consequence (fun _ h => h) (fun _ h => h) (cost_linear sh rows ell precision hr)

/-- Physical execution and exact semantic readiness on the actual controller
saved slot; all scalar safety is obtained from the original recursive Path. -/
theorem runs_from_path {sh : Shape} {rows ell q left k levels frames returned : ℕ}
    (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) v=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hr : 0<rows) (f : Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (hs : v.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (hh : v.head source=0) :
    HoareTime (program (savedSlot pcStack)) (fun w => w=v)
      (fun w => w=output call v f ∧
        w.tape source=NativeZeroPadding.word (NativeZeroPaddingArray.word (oriented call f)) ∧
        w.head source=0 ∧
        Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) w=
          Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) v ∧
        CompactSpectatorInheritedGrid.Width sh rows ell q (oriented call f) ∧
        CompactSpectatorInheritedGrid.Grid sh rows ell q n
          (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (oriented call f) ∧
        CompactSpectatorInheritedGrid.decoded sh rows ell q n (oriented call f)=
          fun i => if call.inverse then star (CompactSpectatorInheritedGrid.decoded sh rows ell q n f i)
            else CompactSpectatorInheritedGrid.decoded sh rows ell q n f i)
      (constant*CompactNativeRoleTransferBudget.volume rows sh ell
        (ButterflyIndependentGuardHeaders.reservation sh.bits q)) := by
  have h := runs_linear (savedSlot pcStack) call v older origin hstack sh rows ell
    (ButterflyIndependentGuardHeaders.reservation sh.bits q) hr f hw hs hh
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  obtain ⟨hs',hh'⟩ := output_source call v f hs hh
  exact ⟨rfl,hs',hh',retained_savedSlot pcStack call v f,oriented_width call sh rows ell q f hw,
    oriented_grid call path p C n hp hchunk f hw hg,oriented_decoded call path p C n hp hchunk f hw hg⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientationInvariants
