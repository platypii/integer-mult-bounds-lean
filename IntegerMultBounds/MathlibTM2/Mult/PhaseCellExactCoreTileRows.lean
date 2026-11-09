module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIndexedCoreTileRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProperPublicationBank
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams

/-! Rectangular and core-indexed views of actual exact-row archives. These are
proof-only views; no numerical job metadata or new machine pass is required. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

theorem exactCoreTileRows {p W width L : ℕ} (ks : List ℕ)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (h : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p W width k Fs J rows) ks batches)
    (hcore : ∀ k ∈ ks, coreLength s width k = L) :
    ∃ values : Fin ks.length → Fin Fs.length → List GaussianInt,
      (∀ i j, (values i j).length = L) ∧
      batches = List.ofFn (fun i => List.ofFn (values i)) ∧
      (batches.map (fun rows => cstream A W rows.flatten)).flatten =
        (List.ofFn fun i => (List.ofFn fun j => cstream A W (values i j)).flatten).flatten ∧
      ∀ i : Fin ks.length, ExactCoreRows (A := A) p W width ks[i] Fs J (List.ofFn (values i)) := by
  have hlength := h.length_eq
  have hjob (i : Fin ks.length) : ExactCoreRows (A := A) p W width ks[i] Fs J
      (batches[i.val]'(by rw [←hlength]; exact i.isLt)) :=
    h.get i.isLt (by rw [←hlength]; exact i.isLt)
  have hcount (i : Fin ks.length) :
      (batches[i.val]'(by rw [←hlength]; exact i.isLt)).length = Fs.length := (hjob i).1
  let values := fun (i : Fin ks.length) (j : Fin Fs.length) =>
    (batches[i.val]'(by rw [←hlength]; exact i.isLt))[j.val]'(by rw [hcount]; exact j.isLt)
  have hrow (i : Fin ks.length) : List.ofFn (values i) =
      batches[i.val]'(by rw [←hlength]; exact i.isLt) := by
    apply List.ext_getElem (by simp only [List.length_ofFn,hcount])
    intro j hj hj'
    simp only [List.getElem_ofFn,values]
  have hview : List.ofFn (fun i => List.ofFn (values i)) = batches := by
    apply List.ext_getElem (by simp only [List.length_ofFn]; exact hlength)
    intro i hi hi'
    simp only [List.getElem_ofFn,hrow]
  have hencode (rows : List (List GaussianInt)) :
      cstream A W rows.flatten = (rows.map (cstream A W)).flatten := by
    simpa only [List.flatMap_id,List.flatMap,List.map_id,id_eq] using
      cstream_flatMap_rows (A := A) (w := W) rows id
  refine ⟨values,?_,hview.symm,?_,?_⟩
  · intro i j
    exact ((hjob i).2.1 _ (List.getElem_mem (show j.val <
      (batches[i.val]'(by rw [←hlength]; exact i.isLt)).length by rw [hcount]; exact j.isLt))).trans
        (hcore _ (List.getElem_mem i.isLt))
  · rw [←hview]
    simp only [List.map_ofFn,Function.comp_def,hencode]
  · intro i
    rw [hrow]
    exact hjob i

theorem exactCoreClassRows_spec {p W width : ℕ}
    (g : CorePublicationClass s width) (Fs : List (ZMod s → GaussianInt))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (values : Fin g.indices.length → Fin Fs.length → List GaussianInt)
    (h : ∀ i : Fin g.indices.length,
      ExactCoreRows (A := A) p W width g.indices[i] Fs J (List.ofFn (values i))) :
    ∀ j k, k ∈ g.indices →
      let row := indexedCoreRows g.indices rfl values j k
      row.length = g.length ∧
      (∀ z ∈ ownedCore s width k, ‖packedIntervalRead p W (coreStart width k) (cstream A W row) z‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W row))
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (Fs[j] z)))
        (3/(2 : ℝ)^p) := by
  intro j
  apply indexedCoreRows_forall g.indices rfl g.indices_nodup values j
    (fun k row => row.length = g.length ∧
      (∀ z ∈ ownedCore s width k, ‖packedIntervalRead p W (coreStart width k) (cstream A W row) z‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W row))
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (Fs[j] z)))
        (3/(2 : ℝ)^p))
  intro i
  have hgood := (h i).2.2.get j.isLt (by simp)
  simp only [List.get_eq_getElem,List.getElem_ofFn] at hgood
  have hlen := (h i).2.1 _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hcore := (mem_corePublicationIndices s width g.length _).mp
    (g.sublist.subset (List.getElem_mem i.isLt))
  exact ⟨hlen.trans hcore.2,hgood⟩

/-- The grouped scatter's actual class outputs discharge the bulk accuracy
premise of boundary completion. -/
theorem exactCoreClass_output_bank {p W width : ℕ}
    (g : CorePublicationClass s width) (hw : 0 < width)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (values : Fin g.indices.length → Fin Fs.length → List GaussianInt)
    (h : ∀ i : Fin g.indices.length,
      ExactCoreRows (A := A) p W width g.indices[i] Fs J (List.ofFn (values i)))
    (ambient : Fin Fs.length → List (Fin (A+4)))
    (hambient : ∀ j, (ambient j).length = s*W) :
    g.BankAccurate p W (inversePublicationTargets p Fs.reverse J)
      (List.ofFn fun j => g.output W hw (indexedCoreRows g.indices rfl values j) (ambient j))
      (3/(2 : ℝ)^p) := by
  have hspec := exactCoreClassRows_spec g Fs J values h
  have htargets := inversePublicationTargets_eq_ofFn p Fs.reverse J
    (fun j : Fin Fs.length => Fs[j]) (by simp)
  unfold CorePublicationClass.BankAccurate
  rw [htargets]
  exact g.output_bank_good p W hw _ (3/(2 : ℝ)^p)
    (indexedCoreRows g.indices rfl values) ambient
    (fun j k hk => (hspec j k hk).1) hambient
    (fun j k hk => (hspec j k hk).2)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
