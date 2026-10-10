import IntegerMultBounds.Machine.CompactComplexSourceReadyLeafSemantics
import IntegerMultBounds.Machine.CompactComplexNonleafChildAddress
import IntegerMultBounds.Networks.ComplexEndpoints
import IntegerMultBounds.Networks.BinaryColumnConjugation
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedReturnPrefix

/-! Literal selected-axis leaf kernels restrict to genuine child tensor
coordinates. The surrounding binary address remains anchored to the actual
input, and no numerical transform equality is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexNonleafChildAddress (Address axis axisIndex insert flatten)
variable {sh : Shape} {left k : ℕ}
attribute [local irreducible] arity Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites

theorem axisIndex_injective : Function.Injective
    (fun p : Fin arity × Fin (arity^k) => axisIndex p.1 p.2) := by
  intro p q h
  have h' := congrArg
    (fun i => finProdFinEquiv.symm
      (Fin.cast (by rw [pow_succ,Nat.mul_comm] : arity^(k+1)=arity*arity^k) i)) h
  simpa only [axisIndex,Fin.cast_cast,Fin.cast_eq_self,RecursiveInterchangeRows.pack,
    Equiv.symm_apply_apply] using h'

theorem axisIndex_surjective : Function.Surjective
    (fun p : Fin arity × Fin (arity^k) => axisIndex p.1 p.2) := by
  intro i
  refine ⟨finProdFinEquiv.symm
    (Fin.cast (by rw [pow_succ,Nat.mul_comm] : arity^(k+1)=arity*arity^k) i),?_⟩
  simp only [axisIndex,RecursiveInterchangeRows.pack,Prod.mk.eta,Equiv.apply_symm_apply,
    Fin.cast_cast,Fin.cast_eq_self]

/-- A tensor coordinate shift changes exactly its selected global bit. -/
theorem insert_shift (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (anchor : BinaryWalsh.Address sh.bits) (a : Address k)
    (slot : Fin arity) (column : Fin (arity^k)) :
    insert rho visit anchor (BinaryColumns.shift column (Pi.single slot 1) a)=
      insert rho visit anchor a+Pi.single (axis rho visit (axisIndex slot column)) 1 := by
  funext t
  change insert rho visit anchor (BinaryColumns.shift column (Pi.single slot 1) a) t=
    insert rho visit anchor a t+(Pi.single (axis rho visit (axisIndex slot column)) 1 : BinaryWalsh.Address sh.bits) t
  by_cases ht : ∃ i,axis rho visit i=t
  · obtain ⟨i,rfl⟩ := ht
    obtain ⟨⟨s,c⟩,rfl⟩ := axisIndex_surjective (k:=k) i
    dsimp only
    rw [CompactComplexNonleafChildAddress.insert_axis,
      CompactComplexNonleafChildAddress.insert_axis]
    by_cases hc : c=column
    · subst c
      by_cases hs : s=slot
      · subst s
        simp [BinaryColumns.shift]
      · have hne : axis rho visit (axisIndex s column)≠axis rho visit (axisIndex slot column) := by
          intro h
          have hi := @CompactComplexNonleafChildAddress.axis_injective sh left k rho visit
            (axisIndex s column) (axisIndex slot column) h
          have he := @axisIndex_injective k (s,column) (slot,column) hi
          exact hs (congrArg Prod.fst he)
        simp [BinaryColumns.shift,Pi.single_eq_of_ne hs,Pi.single_eq_of_ne hne]
    · have hne : axis rho visit (axisIndex s c)≠axis rho visit (axisIndex slot column) := by
        intro h
        have hi := @CompactComplexNonleafChildAddress.axis_injective sh left k rho visit
          (axisIndex s c) (axisIndex slot column) h
        have he := @axisIndex_injective k (s,c) (slot,column) hi
        exact hc (congrArg Prod.snd he)
      simp [BinaryColumns.shift,Function.update_of_ne hc,Pi.single_eq_of_ne hne]
  · have hne : t≠axis rho visit (axisIndex slot column) := by
      intro he
      exact ht ⟨_,he.symm⟩
    rw [CompactComplexNonleafChildAddress.insert_frame rho visit anchor _ t ht,
      CompactComplexNonleafChildAddress.insert_frame rho visit anchor _ t ht]
    simp [Pi.single_eq_of_ne hne]

def slice (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (anchor : BinaryWalsh.Address sh.bits) (f : BinaryWalsh.Arrays sh.bits) :
    BinaryColumns.Arrays arity (arity^k) := fun a => f (insert rho visit anchor a)

/-- One actual leaf translation kernel is the matching named tensor kernel,
for either sign of its phase and every surrounding spectator address. -/
theorem slice_kernel (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (anchor : BinaryWalsh.Address sh.bits) (f : BinaryWalsh.Arrays sh.bits)
    (q : ZMod 4) (slot : Fin arity) (column : Fin (arity^k)) :
    slice rho visit anchor
      (BinaryWalsh.kernel q (Pi.single (axis rho visit (axisIndex slot column)) 1) f)=
      BinaryColumns.columnKernel column q (Pi.single slot 1) (slice rho visit anchor f) := by
  funext a
  simp only [slice,BinaryWalsh.kernel_apply,BinaryColumns.columnKernel_apply]
  rw [insert_shift]

abbrev Step (k : ℕ) := ZMod 4 × (Fin arity × Fin (arity^k))

def globalKernels (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (steps : List (Step k)) : List (ZMod 4 × BinaryWalsh.Address sh.bits) :=
  steps.map (fun st => (st.1,Pi.single (axis rho visit (axisIndex st.2.1 st.2.2)) 1))

def tensorProduct (steps : List (Step k)) : BinaryColumns.Operator arity (arity^k) :=
  (steps.map (fun st => BinaryColumns.columnKernel st.2.2 st.1 (Pi.single st.2.1 1))).prod

theorem slice_product (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (anchor : BinaryWalsh.Address sh.bits) (steps : List (Step k))
    (f : BinaryWalsh.Arrays sh.bits) :
    slice rho visit anchor
      (((globalKernels rho visit steps).map (fun g => BinaryWalsh.kernel g.1 g.2)).prod f)=
      tensorProduct steps (slice rho visit anchor f) := by
  induction steps with
  | nil => rfl
  | cons st steps ih =>
    change slice rho visit anchor
      (BinaryWalsh.kernel st.1 (Pi.single (axis rho visit (axisIndex st.2.1 st.2.2)) 1)
        (((globalKernels rho visit steps).map (fun g => BinaryWalsh.kernel g.1 g.2)).prod f))=_
    rw [slice_kernel,ih]
    rfl

/-- Exact finite composition transports every actual leaf kernel, without
replacing the physical addresses or assuming a tensor-transform identity. -/
theorem slice_kernelRun (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (anchor : BinaryWalsh.Address sh.bits) (steps : List (Step k))
    (f : BinaryWalsh.Arrays sh.bits) :
    slice rho visit anchor (BinaryWalsh.kernelRun (globalKernels rho visit steps) f)=
      tensorProduct steps (slice rho visit anchor f) := by
  rw [BinaryWalsh.kernelRun_eq_frame]
  have hp := slice_product rho visit anchor steps f
  rw [BinaryColumns.kernel_prod_eq_frame] at hp
  exact hp

def forwardSteps (k : ℕ) : List (Step k) :=
  (List.ofFn (fun slot : Fin arity =>
    List.ofFn (fun column : Fin (arity^k) => ((1 : ZMod 4),(slot,column))))).flatten

theorem forward_product : tensorProduct (forwardSteps k)=
    (ComplexEndpoints.fullFrame (h:=arity) (arity^k)).toLinearMap := by
  rw [ComplexEndpoints.fullFrame_coordinate_product]
  simp only [tensorProduct,forwardSteps,List.map_flatten,List.map_ofFn,List.prod_flatten,
    ComplexEndpoints.coordinateKernels,BinaryColumns.vectorFactor,Function.comp_def]

/-- The literal slot-major leaf order is the original tensor coordinate order. -/
theorem forward_directions (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1)) :
    CompactSpectatorLeafSemantics.directions sh rho visit (arity^(k+1)) le_rfl=
      globalKernels rho visit (forwardSteps k) := by
  unfold CompactSpectatorLeafSemantics.directions
  rw [List.ofFn_congr (by rw [pow_succ,Nat.mul_comm] : arity^(k+1)=arity*arity^k),List.ofFn_mul]
  simp only [globalKernels,forwardSteps,List.map_flatten,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext slot
  apply congrArg List.ofFn
  funext column
  congr 1
  apply congrArg (fun t => (Pi.single t 1 : BinaryWalsh.Address sh.bits))
  apply congrArg Fin.rev
  apply Fin.ext
  simp only [CompactSpectatorLeafSemantics.position,CompactSpectatorLeafHeaders.selected,
    CompactSpectatorVisitGeometry.selected,axisIndex,Fin.val_cast,RecursiveInterchangeRows.pack_val]
  congr 1

/-- The entire actual forward leaf kernel list is the full named child tensor. -/
theorem forward_kernel_tensor (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (anchor : BinaryWalsh.Address sh.bits) (f : BinaryWalsh.Arrays sh.bits) :
    slice rho visit anchor (BinaryWalsh.kernelRun
      (CompactSpectatorLeafSemantics.directions sh rho visit (arity^(k+1)) le_rfl) f)=
      ComplexEndpoints.fullFrame (arity^k) (slice rho visit anchor f) := by
  rw [forward_directions,slice_kernelRun,forward_product]
  rfl

def rowSlice (rows ell q n : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+1)) (row : Fin rows) (poly : Fin (2^ell))
    (anchor : BinaryWalsh.Address sh.bits) (f : CompactSpectatorVisitGeometry.Array sh rows ell) :=
  slice rho visit anchor (fun x => CompactSpectatorInheritedGrid.decoded sh rows ell q n f
    (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))

/-- The guarded actual forward leaf has the exact tensor action on every
anchored child slice, with the original row and polynomial spectators. -/
theorem forward_result_guarded (rows ell q n M : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+1))
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      M f)
    (hguard : 4*(M*4^(arity^(k+1)))<2^(CompactSpectatorInheritedGrid.half sh q))
    (row : Fin rows) (poly : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    let out := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit f
    CompactSpectatorInheritedGrid.Grid sh rows ell q (n+arity^(k+1))
      (M*4^(arity^(k+1))) out ∧
    rowSlice rows ell q (n+arity^(k+1)) rho visit row poly anchor out=
      ComplexEndpoints.fullFrame (arity^k) (rowSlice rows ell q n rho visit row poly anchor f) := by
  have h := CompactSpectatorInheritedGrid.directional_semantics sh rows ell q rho visit .forward n _
    f hw hg hguard row poly
  refine ⟨h.1,?_⟩
  have hs := congrArg (slice rho visit anchor) h.2
  change rowSlice rows ell q (n+arity^(k+1)) rho visit row poly anchor _=
    slice rho visit anchor (BinaryWalsh.kernelRun
      (CompactSpectatorLeafSemantics.directions sh rho visit (arity^(k+1)) le_rfl) _) at hs
  rw [forward_kernel_tensor] at hs
  exact hs


theorem forward_result_from_path (rows ell q n baseline C : ℕ) (rho : Fin sh.chunk)
    {levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (hb : baseline≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)) f)
    (row : Fin rows) (poly : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    let out := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho path.visit f
    CompactSpectatorInheritedGrid.Grid sh rows ell q (n+arity^(k+1))
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(arity^(k+1))) out ∧
    rowSlice rows ell q (n+arity^(k+1)) rho path.visit row poly anchor out=
      ComplexEndpoints.fullFrame (arity^k) (rowSlice rows ell q n rho path.visit row poly anchor f) := by
  have hguard := CompactSpectatorInheritedGrid.guard_from_path sh q path baseline C (arity^(k+1))
    hb hchunk (CompactSpectatorLeafSemantics.count_le_bits sh rho path.visit)
  have h := CompactSpectatorInheritedGrid.directional_semantics sh rows ell q rho path.visit .forward n _
    f hw hg hguard row poly
  refine ⟨h.1,?_⟩
  have hs := congrArg (slice rho path.visit anchor) h.2
  change rowSlice rows ell q (n+arity^(k+1)) rho path.visit row poly anchor _=
    slice rho path.visit anchor (BinaryWalsh.kernelRun
      (CompactSpectatorLeafSemantics.directions sh rho path.visit (arity^(k+1)) le_rfl) _) at hs
  rw [forward_kernel_tensor] at hs
  exact hs

/-- Orientation acts on the very same anchored child slice. -/
theorem rowSlice_oriented (call : ComplexRecursiveCallSchema.Call) (rows ell q n M : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n M f)
    (hguard : M<2^(CompactSpectatorInheritedGrid.half sh q))
    (row : Fin rows) (poly : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    rowSlice rows ell q n rho visit row poly anchor
      (CompactComplexSourceReadyOrientationInvariants.oriented call f)=
      if call.inverse then BinaryColumnConjugation.conjugate
        (rowSlice rows ell q n rho visit row poly anchor f)
      else rowSlice rows ell q n rho visit row poly anchor f := by
  have h := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh rows ell q n M f hw hg hguard
  funext a
  have he := congrFun h.2
    (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index (insert rho visit anchor a) poly))
  cases hd : call.inverse <;> simpa [rowSlice,slice,hd,BinaryColumnConjugation.conjugate] using he

private theorem oriented_tensor_action (reverse : Bool)
    (original input middle out : BinaryColumns.Arrays arity (arity^k))
    (hi : input=if reverse then BinaryColumnConjugation.conjugate original else original)
    (hm : middle=ComplexEndpoints.fullFrame (arity^k) input)
    (ho : out=if reverse then BinaryColumnConjugation.conjugate middle else middle) :
    out=if reverse then (ComplexEndpoints.fullFrame (arity^k)).symm original
      else ComplexEndpoints.fullFrame (arity^k) original := by
  cases reverse
  · exact ho.trans (hm.trans (congrArg (ComplexEndpoints.fullFrame (arity^k)) hi))
  · have he := BinaryColumnConjugation.frame_conjugate BinaryPhase.weightPhase
      (BinaryColumnConjugation.conjugate original)
    have hconj : BinaryColumnConjugation.conjugate
        (ComplexEndpoints.fullFrame (arity^k) (BinaryColumnConjugation.conjugate original))=
        (ComplexEndpoints.fullFrame (arity^k)).symm original := by
      simpa only [ComplexEndpoints.fullFrame,BinaryColumnConjugation.conjugate_twice] using he
    exact ho.trans ((congrArg BinaryColumnConjugation.conjugate
      (hm.trans (congrArg (ComplexEndpoints.fullFrame (arity^k)) hi))).trans hconj)

/-- The literal installed stopped result computes the forward or inverse
named tensor selected by the real saved call. No completed-network equality
or independent child execution certificate is assumed. -/
theorem stopped_leaf_tensor_guarded (call : ComplexRecursiveCallSchema.Call)
    (rows ell q n M : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+1))
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      M f)
    (hguard : 4*(M*4^(arity^(k+1)))<2^(CompactSpectatorInheritedGrid.half sh q))
    (row : Fin rows) (poly : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    let input := CompactComplexSourceReadyOrientationInvariants.oriented call f
    let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit input
    let out := CompactComplexSourceReadyOrientationInvariants.oriented call leaf
    CompactSpectatorInheritedGrid.Grid sh rows ell q (n+arity^(k+1))
      (M*4^(arity^(k+1))) out ∧
    rowSlice rows ell q (n+arity^(k+1)) rho visit row poly anchor out=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
        (rowSlice rows ell q n rho visit row poly anchor f)
      else ComplexEndpoints.fullFrame (arity^k)
        (rowSlice rows ell q n rho visit row poly anchor f) := by
  let input := CompactComplexSourceReadyOrientationInvariants.oriented call f
  let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit input
  have hM : M≤M*4^(arity^(k+1)) := Nat.le_mul_of_pos_right M (pow_pos (by decide) _)
  have hinput := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh rows ell q n M f hw hg (by omega)
  have hinputWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call sh rows ell q f hw
  have hforward := forward_result_guarded rows ell q n M rho visit input
    hinputWidth hinput.1 hguard row poly anchor
  have hleafWidth := CompactSpectatorLeafLoop.width_run sh rows ell
    (ButterflyIndependentGuardHeaders.reservation sh.bits q) rho visit (arity^(k+1)) input hinputWidth
  have houtput := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh rows ell q (n+arity^(k+1)) (M*4^(arity^(k+1))) leaf hleafWidth hforward.1 (by omega)
  refine ⟨houtput.1,?_⟩
  have hi := rowSlice_oriented call rows ell q n M rho visit f hw hg (by omega) row poly anchor
  have ho := rowSlice_oriented call rows ell q (n+arity^(k+1)) (M*4^(arity^(k+1)))
    rho visit leaf hleafWidth hforward.1 (by omega) row poly anchor
  exact oriented_tensor_action call.inverse
    (rowSlice rows ell q n rho visit row poly anchor f)
    (rowSlice rows ell q n rho visit row poly anchor input)
    (rowSlice rows ell q (n+arity^(k+1)) rho visit row poly anchor leaf)
    (rowSlice rows ell q (n+arity^(k+1)) rho visit row poly anchor
      (CompactComplexSourceReadyOrientationInvariants.oriented call leaf)) hi hforward.2 ho


theorem stopped_leaf_tensor_from_path (call : ComplexRecursiveCallSchema.Call)
    (rows ell q n baseline C : ℕ) (rho : Fin sh.chunk)
    {levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (hb : baseline≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)) f)
    (row : Fin rows) (poly : Fin (2^ell)) (anchor : BinaryWalsh.Address sh.bits) :
    let input := CompactComplexSourceReadyOrientationInvariants.oriented call f
    let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho path.visit input
    let out := CompactComplexSourceReadyOrientationInvariants.oriented call leaf
    CompactSpectatorInheritedGrid.Grid sh rows ell q (n+arity^(k+1))
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(arity^(k+1))) out ∧
    rowSlice rows ell q (n+arity^(k+1)) rho path.visit row poly anchor out=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm
        (rowSlice rows ell q n rho path.visit row poly anchor f)
      else ComplexEndpoints.fullFrame (arity^k)
        (rowSlice rows ell q n rho path.visit row poly anchor f) := by
  let M := CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)
  let input := CompactComplexSourceReadyOrientationInvariants.oriented call f
  let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho path.visit input
  have hguard := CompactSpectatorInheritedGrid.guard_from_path sh q path baseline C (arity^(k+1))
    hb hchunk (CompactSpectatorLeafSemantics.count_le_bits sh rho path.visit)
  change 4*(M*4^(arity^(k+1)))<2^(CompactSpectatorInheritedGrid.half sh q) at hguard
  have hM : M≤M*4^(arity^(k+1)) := Nat.le_mul_of_pos_right M (pow_pos (by decide) _)
  have hinput := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh rows ell q n M f hw hg (by omega)
  have hinputWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call sh rows ell q f hw
  have hforward := forward_result_from_path rows ell q n baseline C rho path hb hchunk input
    hinputWidth hinput.1 row poly anchor
  have hleafWidth := CompactSpectatorLeafLoop.width_run sh rows ell
    (ButterflyIndependentGuardHeaders.reservation sh.bits q) rho path.visit (arity^(k+1)) input hinputWidth
  have houtput := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid
    call sh rows ell q (n+arity^(k+1)) (M*4^(arity^(k+1))) leaf hleafWidth hforward.1 (by omega)
  refine ⟨houtput.1,?_⟩
  have hi := rowSlice_oriented call rows ell q n M rho path.visit f hw hg (by omega) row poly anchor
  have ho := rowSlice_oriented call rows ell q (n+arity^(k+1)) (M*4^(arity^(k+1)))
    rho path.visit leaf hleafWidth hforward.1 (by omega) row poly anchor
  exact oriented_tensor_action call.inverse
    (rowSlice rows ell q n rho path.visit row poly anchor f)
    (rowSlice rows ell q n rho path.visit row poly anchor input)
    (rowSlice rows ell q (n+arity^(k+1)) rho path.visit row poly anchor leaf)
    (rowSlice rows ell q (n+arity^(k+1)) rho path.visit row poly anchor
      (CompactComplexSourceReadyOrientationInvariants.oriented call leaf)) hi hforward.2 ho

/-- The anchored row slice is literally the child's input lookup at its own
output wire. The wire may be any data or dirty scratch role. -/
theorem rowSlice_inputIndex (rows ell q n : ℕ)
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (i : CompactComplexNonleafChildAddress.Index sh rows ell) :
    let v := (CompactComplexNonleafChildAddress.layout sh rows ell hd).symm i
    rowSlice rows ell q n rho visit
      (CompactComplexNonleafChildAddress.rowLayout rows hd v.1) v.2.2 v.2.1 f=
      fun a => CompactSpectatorInheritedGrid.decoded sh rows ell q n f
        (CompactComplexNonleafChildAddress.inputIndex sh rows ell hd rho visit i
          (CompactComplexNonleafChildAddress.outputWire sh rows ell hd i) a) := by
  rfl

/-- Every literal installed output coefficient has its genuine named tensor
address and output role; no wire is omitted or fixed to a chosen data bank. -/
theorem stopped_leaf_tensor_at_guarded (call : ComplexRecursiveCallSchema.Call)
    (rows ell q n M : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+1))
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      M f)
    (hguard : 4*(M*4^(arity^(k+1)))<2^(CompactSpectatorInheritedGrid.half sh q))
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows)
    (i : CompactComplexNonleafChildAddress.Index sh rows ell) :
    let input := CompactComplexSourceReadyOrientationInvariants.oriented call f
    let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit input
    let out := CompactComplexSourceReadyOrientationInvariants.oriented call leaf
    let stored := fun wire a => CompactSpectatorInheritedGrid.decoded sh rows ell q n f
      (CompactComplexNonleafChildAddress.inputIndex sh rows ell hd rho visit i wire a)
    let wire := CompactComplexNonleafChildAddress.outputWire sh rows ell hd i
    let address := CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho visit i
    CompactSpectatorInheritedGrid.decoded sh rows ell q (n+arity^(k+1)) out i=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm (stored wire) address
      else ComplexEndpoints.fullFrame (arity^k) (stored wire) address := by
  let v := (CompactComplexNonleafChildAddress.layout sh rows ell hd).symm i
  have h := stopped_leaf_tensor_guarded call rows ell q n M rho visit f hw hg hguard
    (CompactComplexNonleafChildAddress.rowLayout rows hd v.1) v.2.2 v.2.1
  have he := congrFun h.2 (CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho visit i)
  rw [rowSlice_inputIndex rows ell q n hd rho visit f i] at he
  dsimp only at he ⊢
  change CompactSpectatorInheritedGrid.decoded sh rows ell q (n+arity^(k+1))
    (CompactComplexSourceReadyOrientationInvariants.oriented call
      (CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho visit
        (CompactComplexSourceReadyOrientationInvariants.oriented call f)))
    (CompactComplexNonleafChildAddress.inputIndex sh rows ell hd rho visit i
      (CompactComplexNonleafChildAddress.outputWire sh rows ell hd i)
      (CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho visit i))=_ at he
  rw [CompactComplexNonleafChildAddress.input_output] at he
  simpa only [ite_apply] using he


theorem stopped_leaf_tensor_at (call : ComplexRecursiveCallSchema.Call)
    (rows ell q n baseline C : ℕ) (rho : Fin sh.chunk)
    {levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (hb : baseline≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)) f)
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows)
    (i : CompactComplexNonleafChildAddress.Index sh rows ell) :
    let input := CompactComplexSourceReadyOrientationInvariants.oriented call f
    let leaf := CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho path.visit input
    let out := CompactComplexSourceReadyOrientationInvariants.oriented call leaf
    let stored := fun wire a => CompactSpectatorInheritedGrid.decoded sh rows ell q n f
      (CompactComplexNonleafChildAddress.inputIndex sh rows ell hd rho path.visit i wire a)
    let wire := CompactComplexNonleafChildAddress.outputWire sh rows ell hd i
    let address := CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho path.visit i
    CompactSpectatorInheritedGrid.decoded sh rows ell q (n+arity^(k+1)) out i=
      if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm (stored wire) address
      else ComplexEndpoints.fullFrame (arity^k) (stored wire) address := by
  let v := (CompactComplexNonleafChildAddress.layout sh rows ell hd).symm i
  have h := stopped_leaf_tensor_from_path call rows ell q n baseline C rho path hb hchunk f hw hg
    (CompactComplexNonleafChildAddress.rowLayout rows hd v.1) v.2.2 v.2.1
  have he := congrFun h.2 (CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho path.visit i)
  rw [rowSlice_inputIndex rows ell q n hd rho path.visit f i] at he
  dsimp only at he ⊢
  change CompactSpectatorInheritedGrid.decoded sh rows ell q (n+arity^(k+1))
    (CompactComplexSourceReadyOrientationInvariants.oriented call
      (CompactSpectatorLeafGuardOriginal.result .forward sh rows ell q rho path.visit
        (CompactComplexSourceReadyOrientationInvariants.oriented call f)))
    (CompactComplexNonleafChildAddress.inputIndex sh rows ell hd rho path.visit i
      (CompactComplexNonleafChildAddress.outputWire sh rows ell hd i)
      (CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho path.visit i))=_ at he
  rw [CompactComplexNonleafChildAddress.input_output] at he
  simpa only [ite_apply] using he

end
end IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics
