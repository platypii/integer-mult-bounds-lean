module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellRows

/-! The generated clipped length groups are packed disjoint cell windows.
All coordinates retain the ambient phase and use the halo origin only for storage. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloPackedOffsets (s t band a b L : ℕ) : List ℕ :=
  (haloOrigins s t band a b L).map (fun p => p-a)

@[simp] theorem haloPackedOffsets_length (s t band a b L : ℕ) :
    (haloPackedOffsets s t band a b L).length = (haloLengthGroup s t band a b L).length := by
  simp [haloPackedOffsets]

theorem haloOrigins_bounds (s t band a b L : ℕ) (p : ℕ) (hp : p ∈ haloOrigins s t band a b L) :
    a ≤ p ∧ p+L ≤ b := by
  obtain ⟨phase,hphase,rfl⟩ := List.mem_map.mp hp
  obtain ⟨_,hL,hlen⟩ := (mem_haloLengthGroup s t band a b L phase).mp hphase
  have hstart : a ≤ haloStart s t band a phase := by unfold haloStart; omega
  have hstop : haloStop s t band b phase ≤ b := by unfold haloStop; omega
  unfold haloLength at hlen
  omega

theorem haloPackedOffsets_fit (s t band a b L : ℕ) :
    ∀ j ∈ haloPackedOffsets s t band a b L, j+L ≤ b-a := by
  intro j hj
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
  have hh := haloOrigins_bounds s t band a b L p hp
  omega

theorem haloPackedOffsets_disjoint (s t band a b L : ℕ) :
    (haloPackedOffsets s t band a b L).Pairwise (fun i j => i+L ≤ j) := by
  apply List.pairwise_map.mpr
  apply (haloOrigins_disjoint s t band a b L).imp_of_mem
  intro p q hp hq hpq
  have hp' := haloOrigins_bounds s t band a b L p hp
  have hq' := haloOrigins_bounds s t band a b L q hq
  omega

theorem haloPackedOffsets_get (s t band a b L n : ℕ)
    (hn : n < (haloLengthGroup s t band a b L).length) :
    (haloPackedOffsets s t band a b L)[n]?.getD 0 =
      haloStart s t band a (haloGroupPhase s t band a b L n)-a := by
  simp [haloPackedOffsets,haloOrigins,haloGroupPhase,List.getElem?_eq_getElem hn]

theorem packedHaloGroupOrigin_eq {s : ℕ} (t band a b L n : ℕ)
    (hn : n < (haloLengthGroup s t band a b L).length) :
    packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n = haloGroupOrigin s t band a b L n := by
  have hm := haloGroupPhase_mem s t band a b L ⟨n,hn⟩
  have hb := haloOrigins_bounds s t band a b L
    (haloStart s t band a (haloGroupPhase s t band a b L n)) (by exact List.mem_map.mpr ⟨_,hm,rfl⟩)
  unfold packedCellOrigin
  rw [haloPackedOffsets_get _ _ _ _ _ _ _ hn,Nat.add_sub_of_le hb.1]
  rfl

/-- Exact coverage by the offsets supplied to the packed cell batch. -/
theorem packedHaloGroups_cover {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ)
    (j : ZMod s) (hj : j ∈ haloInterior s t band a b) :
    ∃ L ∈ haloLengthKeys s t band a b, ∃ n : Fin (haloPackedOffsets s t band a b L).length,
      ∃ i : Fin L, packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n+(i.val : ZMod s) = j := by
  obtain ⟨L,hL,phase,hphase,hstart,hstop⟩ := haloGroups_cover hst band a b j hj
  obtain ⟨n,hn,he⟩ := List.getElem_of_mem hphase
  have hn' : n < (haloPackedOffsets s t band a b L).length := by simpa using hn
  have hphase' : haloGroupPhase s t band a b L n = phase := by
    simpa only [haloGroupPhase,List.getD_eq_getElem _ _ hn] using he
  have hlen := ((mem_haloLengthGroup s t band a b L phase).mp hphase).2.2
  have hi : j.val-haloStart s t band a phase < L := by unfold haloLength at hlen; omega
  refine ⟨L,hL,⟨n,hn'⟩,⟨j.val-haloStart s t band a phase,hi⟩,?_⟩
  rw [packedHaloGroupOrigin_eq t band a b L n hn]
  simp only [haloGroupOrigin,hphase']
  rw [← Nat.cast_add,Nat.add_sub_of_le hstart,ZMod.natCast_zmod_val]

/-- Distinct generated length groups publish into disjoint coordinate windows. -/
theorem haloPackedOffsets_cross_disjoint (s t band a b L M : ℕ) (hLM : L ≠ M)
    (i : ℕ) (hi : i ∈ haloPackedOffsets s t band a b L)
    (j : ℕ) (hj : j ∈ haloPackedOffsets s t band a b M) :
    i+L ≤ j ∨ j+M ≤ i := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj
  have hpB := haloOrigins_bounds s t band a b L p hp
  have hqB := haloOrigins_bounds s t band a b M q hq
  obtain ⟨phase,hphase,rfl⟩ := List.mem_map.mp hp
  obtain ⟨phase',hphase',rfl⟩ := List.mem_map.mp hq
  obtain ⟨_,hLpos,hlen⟩ := (mem_haloLengthGroup s t band a b L phase).mp hphase
  obtain ⟨_,hMpos,hlen'⟩ := (mem_haloLengthGroup s t band a b M phase').mp hphase'
  have hne : phase ≠ phase' := by intro he; subst phase'; exact hLM (hlen.symm.trans hlen')
  by_cases hpq : phase < phase'
  · have hh := haloCells_ordered s t band a b phase phase' hpq
    unfold haloLength at hlen
    omega
  · have hh := haloCells_ordered s t band a b phase' phase (by omega)
    unfold haloLength at hlen'
    omega

/-- A later length-group scatter leaves every earlier group's coordinate intact. -/
theorem haloGroup_scatter_preserves {α : Type*} (s t band a b L M : ℕ) (hLM : L ≠ M)
    (E X : List α) (hE : E.length = b-a)
    (hX : (haloPackedOffsets s t band a b L).length*L ≤ X.length)
    (j : ℕ) (hj : j ∈ haloPackedOffsets s t band a b M) (i : ℕ) (hi : i < M) :
    (scatterRows L E X (windowGaps L 0 (haloPackedOffsets s t band a b L)))[j+i]? = E[j+i]? := by
  apply scatterRows_absolute_off L _ E X (haloPackedOffsets_disjoint s t band a b L)
    (by intro p hp; rw [hE]; exact haloPackedOffsets_fit s t band a b L p hp) hX
  intro n hn
  have hh := haloPackedOffsets_cross_disjoint s t band a b L M hLM _ (List.getElem_mem hn) j hj
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
