module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorAccuracy

/-! The actual generated packed groups cover the halo interior. Their uniform
accuracy contracts combine directly; no sum over cells or groups is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

/-- Publishing another length class preserves each complete word of this class. -/
theorem haloGroup_scatter_word_preserves {α : Type*} (s t band a b L M w : ℕ)
    (hLM : L ≠ M) (E X tail : List α) (hE : E.length = (b-a)*w)
    (hX : (haloPackedOffsets s t band a b L).length*(L*w) ≤ X.length)
    (j : ℕ) (hj : j ∈ haloPackedOffsets s t band a b M) (i : ℕ) (hi : i < M) :
    (((scatterRows (L*w) E X (packedCellGaps L w (haloPackedOffsets s t band a b L)))++tail).drop
      ((j+i)*w)).take w = ((E++tail).drop ((j+i)*w)).take w := by
  let ps := (haloPackedOffsets s t band a b L).map (·*w)
  have hd : ps.Pairwise (fun p q => p+L*w ≤ q) :=
    packedCell_offsets_disjoint L w _ (haloPackedOffsets_disjoint s t band a b L)
  have hf : ∀ p ∈ ps, p+L*w ≤ E.length := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    rw [hE,← Nat.add_mul]
    exact Nat.mul_le_mul_right w (haloPackedOffsets_fit s t band a b L r hr)
  have hx : ps.length*(L*w) ≤ X.length := by simpa [ps] using hX
  have hfits := windowGaps_fits (L*w) 0 ps E (fun _ _ => Nat.zero_le _) hd hf
  have hlen : (scatterRows (L*w) E X (windowGaps (L*w) 0 ps)).length = E.length :=
    length_scatterRows _ _ _ _ hfits (by simpa using hx)
  have hbound : (j+i)*w+w ≤ E.length := by
    have hh := haloPackedOffsets_fit s t band a b M j hj
    have hm := Nat.mul_le_mul_right w (show j+i+1 ≤ b-a by omega)
    simpa only [Nat.add_mul,Nat.one_mul,hE] using hm
  have he := scatterRows_slice_off (L*w) ps E X hd hf hx ((j+i)*w) w (by
    intro n hn
    have hn' : n < (haloPackedOffsets s t band a b L).length := by simpa [ps] using hn
    have hh := haloPackedOffsets_cross_disjoint s t band a b L M hLM _
      (List.getElem_mem hn') j hj
    simp only [ps,List.getElem_map]
    change (j+i)*w+w ≤ ((haloPackedOffsets s t band a b L)[n])*w ∨
      ((haloPackedOffsets s t band a b L)[n])*w+L*w ≤ (j+i)*w
    rcases hh with hh | hh
    · right
      simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (show _+L ≤ j+i by omega)
    · left
      simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w (show j+i+1 ≤ _ by omega))
  change (((scatterRows (L*w) E X (windowGaps (L*w) 0 ps))++tail).drop ((j+i)*w)).take w = _
  rw [List.drop_append_of_le_length (by omega),List.take_append_of_le_length (by simp only [List.length_drop,hlen]; omega),
    List.drop_append_of_le_length (by omega),List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
  exact he

/-- Accuracy already established for another class survives this publication. -/
theorem packedHaloGroupOutputSpec_scatter {A s t p u l target rhsExp a b L M : ℕ} [NeZero s]
    (C : ZMod s → GaussianInt) (hLM : L ≠ M) (E X tail : List (Fin (A+4)))
    (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hX : (haloPackedOffsets s t (PhaseCellBand.width p u) a b L).length*
      (L*executionWidth p l target rhsExp) ≤ X.length)
    (hspec : PackedCellOutputSpec t p u l target rhsExp M
      (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
      (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
      (fun _ => C) (E++tail)) :
    PackedCellOutputSpec t p u l target rhsExp M
      (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
      (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
      (fun _ => C) (scatterRows (L*executionWidth p l target rhsExp) E X
        (packedCellGaps L (executionWidth p l target rhsExp)
          (haloPackedOffsets s t (PhaseCellBand.width p u) a b L))++tail) := by
  intro n I x hx hfit hint hcell hmax i
  rw [haloGroup_scatter_word_preserves s t (PhaseCellBand.width p u) a b L M _ hLM E X tail hE hX
    _ (List.getElem_mem n.isLt) i.val i.isLt]
  exact hspec n I x hx hfit hint hcell hmax i

/-- The processed-key invariant extends by one publication on the shared buffer. -/
theorem packedHaloGroupOutputs_scatter {A s t p u l target rhsExp a b L : ℕ} [NeZero s]
    (C : ZMod s → GaussianInt) (done : List ℕ) (E X tail : List (Fin (A+4)))
    (hE : E.length = (b-a)*executionWidth p l target rhsExp)
    (hX : (haloPackedOffsets s t (PhaseCellBand.width p u) a b L).length*
      (L*executionWidth p l target rhsExp) ≤ X.length) :
    let Spec := fun M output => PackedCellOutputSpec t p u l target rhsExp M
      (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
      (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
      (fun _ => C) output
    let output := scatterRows (L*executionWidth p l target rhsExp) E X
      (packedCellGaps L (executionWidth p l target rhsExp)
        (haloPackedOffsets s t (PhaseCellBand.width p u) a b L))++tail
    (∀ M ∈ done, Spec M (E++tail)) → Spec L output → ∀ M ∈ L::done, Spec M output := by
  dsimp only
  intro hold hnew M hM
  by_cases heq : L = M
  · subst M; exact hnew
  · have hmem : M ∈ done := by
      simp only [List.mem_cons] at hM
      exact hM.resolve_left (Ne.symm heq)
    exact packedHaloGroupOutputSpec_scatter C heq E X tail hE hX (hold M hmem)

theorem haloInterior_error_of_packed_groups {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) (y x : ZMod s → ℝ) (ε : ℝ)
    (hgroup : ∀ L ∈ haloLengthKeys s t band a b,
      ∀ n : Fin (haloPackedOffsets s t band a b L).length, ∀ i : Fin L,
      |y (packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n+(i.val : ZMod s))-
        x (packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n+(i.val : ZMod s))| ≤ ε) :
    PhaseCellInterface.ErrorOn (haloInterior s t band a b) y x ε := by
  intro j hj
  obtain ⟨L,hL,n,i,hcoord⟩ := packedHaloGroups_cover hst band a b j hj
  simpa only [hcoord,Real.norm_eq_abs] using hgroup L hL n i

/-- Complete group contracts directly bound physical reads of the final local
buffer; no ambient-sized output representation is needed. -/
theorem haloInterior_error_of_packed_reads {A s t p u l target rhsExp a b : ℕ} [NeZero s]
    (hst : s < t) (hab : a ≤ b) (hb : b ≤ s)
    (C : ZMod s → GaussianInt) (output : List (Fin (A+4)))
    (haccuracy : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      PackedCellOutputSpec t p u l target rhsExp L (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)
        (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)) (fun _ => C) output)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun j => (packedIntervalRead (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) a output j).re) x (1/(2 : ℝ)^target) := by
  apply haloInterior_error_of_packed_groups hst _ a b _ x _
  intro L hL n i
  have hn : n.val < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length := by
    simpa only [haloPackedOffsets_length] using n.isLt
  have hlo := packedHaloGroupOrigin_eq (s := s) t (PhaseCellBand.width p u) a b L n hn
  obtain ⟨_,hcellfit,hint,hcell,hmax⟩ := haloGroup_solver_geometry hst (PhaseCellBand.width p u) a b L ⟨n,hn⟩
  have hacc := haccuracy L hL n _ x hx
    (by simpa only [hlo] using hcellfit) (by simpa only [hlo] using hint)
    (by simpa only [hlo] using hcell) (by simpa only [hlo] using hmax) i
  have hindex := packedCellOrigin_local_index (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)
    (show a+(b-a) ≤ s by omega) (haloPackedOffsets_fit s t (PhaseCellBand.width p u) a b L) n i
  simpa only [packedIntervalRead,hindex] using hacc

/-- The final packed output's per-group contracts imply complete interior accuracy. -/
theorem haloInterior_error_of_packed_outputs {A s t p u l target rhsExp a b : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (hab : a ≤ b) (hb : b ≤ s)
    (C D : ZMod s → GaussianInt) (hD : ∀ k, Fits (executionWidth p l target rhsExp) (D k))
    (output tail : List (Fin (A+4)))
    (hout : output = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) D)++tail)
    (haccuracy : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      PackedCellOutputSpec t p u l target rhsExp L (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)
        (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)) (fun _ => C) output)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
      (fun i => (value (executionPrecision p l target rhsExp) (D i)).re) x (1/(2 : ℝ)^target) := by
  apply haloInterior_error_of_packed_groups hst _ a b _ x _
  intro L hL n i
  have hn : n.val < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length := by
    simpa only [haloPackedOffsets_length] using n.isLt
  have hlo := packedHaloGroupOrigin_eq (s := s) t (PhaseCellBand.width p u) a b L n hn
  obtain ⟨_,hcellfit,hint,hcell,hmax⟩ := haloGroup_solver_geometry hst (PhaseCellBand.width p u) a b L ⟨n,hn⟩
  apply packedCellOutputSpec_field_at hA D hD _ (by omega)
    (haloPackedOffsets_fit s t (PhaseCellBand.width p u) a b L) (fun _ => C) output tail hout
    (haccuracy L hL) n (haloInterior s t (PhaseCellBand.width p u) a b) x hx
    (by simpa only [hlo] using hcellfit) (by simpa only [hlo] using hint)
    (by simpa only [hlo] using hcell) (by simpa only [hlo] using hmax) i

/-- A complete grouped packed publication supplies the precision-independent stable bound. -/
theorem haloInterior_stable_norm_of_packed_outputs {A s t p u l target rhsExp a b : ℕ} [NeZero s]
    (hp : 0 < p) (hst : s < t) (hA : 4 ≤ A) (hab : a ≤ b) (hb : b ≤ s)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value (executionPrecision p l target rhsExp) (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (hD : ∀ k, Fits (executionWidth p l target rhsExp) (D k))
    (output tail : List (Fin (A+4)))
    (hout : output = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) D)++tail)
    (haccuracy : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      PackedCellOutputSpec t p u l target rhsExp L (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)
        (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b L)) (fun _ => C) output)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re)) :
    ∀ i ∈ haloInterior s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l target rhsExp) (realPartWord (D i))‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  apply stableInterior_norm hp _ hdom C D hC x hx
  exact haloInterior_error_of_packed_outputs hst hA hab hb C D hD output tail hout haccuracy x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
