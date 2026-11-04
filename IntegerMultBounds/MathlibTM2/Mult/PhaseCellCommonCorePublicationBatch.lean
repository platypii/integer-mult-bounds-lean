module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonCoreJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedOutputPublicationRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassPublicationSpec

/-! The common-format jobs supply the exact publication-batch metadata.
Core lengths and key order are derived from the actual fitting-halo group. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {A s t : ℕ} [NeZero s] [NeZero t]

noncomputable def ofCommonCoreClass (p u l target width H : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt)
    (V : Fin (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H)[j.val]
      PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).1)
        (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).2) (V := V j) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (hp : 4 ≤ p) (htarget : p+2 ≤ target)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1) :
    PackedExactBatch A s t Fs.length (H-2*(localityDepth p target*PhaseCellBand.width p u)) := by
  let radius := localityDepth p target*PhaseCellBand.width p u
  let indices := coreGatherIndices s width radius H
  let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A)
    p u l target t width indices[j.val] (V j) α gap C Fs (bounds j) hF
  refine {
    records := List.ofFn jobs
    W := packedHaloCommonWidth p l s u (target+1) 2
    hwidth := ?_, ht := ?_, hp := ?_, htarget := ?_, hlocal := ?_
    J := fun _ => J, hJ := ?_, hreplicas := ?_, hcore := ?_ }
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; rfl
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; rfl
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hp
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact htarget
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; rfl
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hJ
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; rfl
  · intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    change coreLength s width indices[j.val] = H-2*radius
    have hh := (coreGatherIndices_spec s width radius H indices[j.val] (List.getElem_mem j.isLt)).2.2
    omega

theorem ofCommonCoreClass_keys (p u l target width H : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt)
    (V : Fin (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H)[j.val]
      PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).1)
        (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).2) (V := V j) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (hp : 4 ≤ p) (htarget : p+2 ≤ target)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1) :
    ((ofCommonCoreClass (A := A) p u l target width H α gap C V bounds Fs hF hp htarget J hJ).records.map (fun r => r.k)) =
      (gatherPublicationClass s width (localityDepth p target*PhaseCellBand.width p u) H).indices := by
  simp only [ofCommonCoreClass,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun j : Fin (coreGatherIndices s width
    (localityDepth p target*PhaseCellBand.width p u) H).length =>
      (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H)[j.val]) = _
  exact List.ofFn_getElem


/-- Common jobs discharge every metadata premise of the publication theorem.
The input replica order is exactly the job list's order. -/
theorem ofCommonCoreClass_rows_spec (p u l target width H : ℕ) (α gap : ℝ)
    (C : ZMod s → GaussianInt)
    (V : Fin (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) H)[j.val]
      PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).1)
        (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).2) (V := V j) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (hp : 4 ≤ p) (htarget : p+2 ≤ target)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    (rows : (ofCommonCoreClass (A := A) p u l target width H α gap C V bounds Fs hF hp htarget J hJ).Rows) :
    let batch := ofCommonCoreClass (A := A) p u l target width H α gap C V bounds Fs hF hp htarget J hJ
    let g := gatherPublicationClass s width (localityDepth p target*PhaseCellBand.width p u) H
    let keys := ofCommonCoreClass_keys (A := A) p u l target width H α gap C V bounds Fs hF hp htarget J hJ
    ∀ (j : Fin Fs.length) k, k ∈ g.indices →
      let out := packedIntervalRead p batch.W (coreStart width k) (cstream A batch.W (rows.classRows g keys j k))
      (∀ z ∈ ownedCore s width k, ‖out z‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (Fs[j.val] z)))
        (3/(2 : ℝ)^p) := by
  apply rows.classRows_spec
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    rfl
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    rfl
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact List.ofFn_getElem.symm
  · intro r hr
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
