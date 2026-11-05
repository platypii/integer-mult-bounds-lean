module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationReplicas
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationAccuracy

/-! Accuracy of the actual concatenated destination returned by seam publication.
Replica order is inherited from the retained archive; the output suffix is arbitrary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  ScalarPlacement PhaseCellInterface

variable {A s : ℕ} [NeZero s]

theorem seamPublication_accurate (p width k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (hrows : SeamCropRows p width r J k rows)
    (windows : PublicationWindows s (coreLength s width k))
    (hwindow : windows.origins = [coreStart width k])
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (tail raw : List (Fin (A+4)))
    (hraw : raw = (singletonPublicationReplicas
      (rows.map (List.map (symZ (2*p+13)))) ambient).flatMap
        (PublicationReplica.output windows W)++tail)
    (j : ℕ) (hj : j < r.inputs.reverse.length) :
    let out := pairedCellRead p W (raw.drop (j*(s*W)))
    (∀ i ∈ ownedCore s width k, ‖out i‖ ≤ 1) ∧
    ErrorOn (ownedCore s width k) out
      ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
        ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  let wideRows := rows.map (List.map (symZ (2*p+13)))
  let replicas := singletonPublicationReplicas wideRows ambient
  obtain ⟨hn,_,_,hpairs,hvalid⟩ := seamPublicationReplicas_spec p width k W r J rows hrows
    windows (by simp [hwindow]) ambient hlen hambient
  change replicas.length = r.inputs.length at hn
  change List.Forall₂ (fun row replica => replica.rows = [row]) wideRows replicas at hpairs
  have hgood := (hrows.commonWidth p width W k hA hW r J rows).2
  have hjrow : j < wideRows.length := by rw [← hgood.length_eq]; exact hj
  have hjrep : j < replicas.length := by simpa only [hn,List.length_reverse] using hj
  have hrow := hpairs.get hjrow hjrep
  have hg := hgood.get hj hjrow
  simp only [List.get_eq_getElem] at hrow hg
  have transfer (x : ZMod s → ℂ) (error : ℝ)
      (h : ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W wideRows[j])) x error) :
      ErrorOn (ownedCore s width k) (pairedCellRead p W (raw.drop (j*(s*W)))) x error := by
    have he := replicaPublication_errorOn windows p W 0 replicas hvalid tail raw hraw
      j hjrep 0 (by simp [hwindow]) x error
    simp only [hwindow,List.getElem_cons_zero,hrow] at he
    exact he h
  constructor
  · have hb := transfer 0 1 (by simpa [ErrorOn,wideRows] using hg.1)
    simpa [ErrorOn] using hb
  · exact transfer _ _ hg.2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
