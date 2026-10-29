module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSparseScatter
public import IntegerMultBounds.NLogN.PhaseCellRoundedSchur
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Boundary values retain their ambient indices and order. Only their tape
offsets are translated, so sparse recovery occupies the halo length. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {s : ℕ} [NeZero s]

/-- The actual solver boundary fits the packed interval, including artificial
endpoint guards. No separate boundary-containment certificate is needed. -/
theorem haloBoundary_packed_bounds (t band a b : ℕ) (hab : a ≤ b) :
    ∀ i ∈ IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloBoundary s t band a b,
      a ≤ i.val ∧ i.val < a+(b-a) := by
  intro i hi
  have hh := (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.mem_haloVertices a b i).mp
    (Finset.mem_sdiff.mp hi).1
  omega

noncomputable def packedBoundaryOrigins (B : Finset (ZMod s)) (a : ℕ) : List ℕ :=
  (bOrder s B).map (fun i => i.val-a)

noncomputable def packedBoundaryGaps (B : Finset (ZMod s)) (a w : ℕ) : List ℕ :=
  windowGaps w 0 ((packedBoundaryOrigins B a).map (fun i => i*w))

theorem packedBoundaryOrigins_disjoint (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) :
    (packedBoundaryOrigins B a).Pairwise (fun p q => p+1 ≤ q) := by
  rw [packedBoundaryOrigins,List.pairwise_map]
  apply List.pairwise_iff_getElem.mpr
  intro n m hn hm hnm
  have hlt := List.pairwise_iff_getElem.mp (bOrder_val_sorted s B) n m hn hm hnm
  have hmem : (bOrder s B)[n] ∈ B := by
    simpa only [← List.mem_toFinset,bOrder_toFinset] using List.getElem_mem hn
  have hlo := (hB _ hmem).1
  omega

theorem packedBoundaryOrigins_fit (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) :
    ∀ p ∈ packedBoundaryOrigins B a, p+1 ≤ L := by
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have hiB : i ∈ B := by simpa only [← List.mem_toFinset,bOrder_toFinset] using hi
  have hh := hB i hiB
  omega

@[simp] theorem packedBoundaryGaps_length (B : Finset (ZMod s)) (a w : ℕ) :
    (packedBoundaryGaps B a w).length = B.card := by
  simp [packedBoundaryGaps,packedBoundaryOrigins,bOrder_length]

theorem packedBoundaryGaps_fits {α : Type*} (B : Finset (ZMod s)) (a L w : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) (E : List α) (hlen : L*w ≤ E.length) :
    ScatterFits w E (packedBoundaryGaps B a w) := by
  have hd : ((packedBoundaryOrigins B a).map (fun i => i*w)).Pairwise (fun p q => p+w ≤ q) := by
    rw [List.pairwise_map]
    exact (packedBoundaryOrigins_disjoint B a L hB).imp (fun h => by
      simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w h)
  have hf : ∀ p ∈ (packedBoundaryOrigins B a).map (fun i => i*w), p+w ≤ E.length := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh := Nat.mul_le_mul_right w (packedBoundaryOrigins_fit B a L hB i hi)
    exact (by simpa only [Nat.add_mul,Nat.one_mul] using hh : i*w+w ≤ L*w).trans hlen
  simpa only [packedBoundaryGaps,List.drop_zero] using
    windowGaps_fits w 0 _ E (fun _ _ => Nat.zero_le _) hd hf

theorem packedBoundaryScatterCost_le (B : Finset (ZMod s)) (a L w : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) (hw : 1 ≤ w) :
    B.card*(12*w+23)+12*(packedBoundaryGaps B a w).sum+6 ≤ 35*L*w+6 := by
  have hv := scatterVolume_le w (List.replicate (L*w) ()) (packedBoundaryGaps B a w)
    (packedBoundaryGaps_fits B a L w hB _ (by simp))
  simp only [scatterVolume,packedBoundaryGaps_length,List.length_replicate] at hv
  have hn : B.card ≤ B.card*w := by simpa using Nat.mul_le_mul_left B.card hw
  have hnw : B.card*w ≤ L*w := by omega
  nlinarith only [hv,hn,hnw]

/-- Recovery for the actual halo boundary is charged to halo length. -/
theorem haloBoundaryPackedScatterCost_le (t band a b w : ℕ) (hab : a ≤ b) (hw : 1 ≤ w) :
    let B := IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloBoundary s t band a b
    B.card*(12*w+23)+12*(packedBoundaryGaps B a w).sum+6 ≤ 35*(b-a)*w+6 := by
  exact packedBoundaryScatterCost_le _ a (b-a) w
    (haloBoundary_packed_bounds t band a b hab) hw

theorem packedBoundary_scatter_field (B : Finset (ZMod s)) (a L : ℕ)
    (hfit : a+L ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0) :
    scatterRows 1 (List.replicate L 0) ((bOrder s B).map G)
      (windowGaps 1 0 (packedBoundaryOrigins B a)) = packedInterval a L G := by
  have hlen := packedInterval_length G hfit
  nth_rw 1 [← hlen]
  refine scatterRows_sparse 0 (packedInterval a L G) ((bOrder s B).map G)
    (packedBoundaryOrigins B a) (packedBoundaryOrigins_disjoint B a L hB) ?_ ?_ ?_ ?_
  · intro p hp
    rw [hlen]
    have hh := packedBoundaryOrigins_fit B a L hB p hp
    omega
  · simp [packedBoundaryOrigins]
  · intro n hn
    have hn' : n < (bOrder s B).length := by simpa [packedBoundaryOrigins] using hn
    have hm : (bOrder s B)[n] ∈ B := by
      simpa only [← List.mem_toFinset,bOrder_toFinset] using List.getElem_mem hn'
    have hb := hB _ hm
    simp only [packedBoundaryOrigins,List.getElem_map]
    rw [packedInterval_get G hfit (by omega),Nat.add_sub_of_le hb.1,ZMod.natCast_zmod_val]
  · intro i hi hnot
    have hiL : i < L := by simpa only [hlen] using hi
    rw [packedInterval_get G hfit hiL]
    apply hoff
    intro hm
    apply hnot
    have hv : ((a+i : ℕ) : ZMod s).val = a+i := by
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]
    apply List.mem_map.mpr
    refine ⟨((a+i : ℕ) : ZMod s),?_,?_⟩
    · simpa only [← List.mem_toFinset,bOrder_toFinset] using hm
    · rw [hv]; omega

theorem packedBoundary_scatter_cstream (B : Finset (ZMod s)) (A a L w : ℕ)
    (hfit : a+L ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0) :
    scatterRows w (cstream A w (List.replicate L 0)) (cstream A w ((bOrder s B).map G))
      (packedBoundaryGaps B a w) = cstream A w (packedInterval a L G) := by
  have hg : packedBoundaryGaps B a w =
      (windowGaps 1 0 (packedBoundaryOrigins B a)).map (fun d => d*w) := by
    simpa only [packedBoundaryGaps,Nat.one_mul,Nat.zero_mul] using
      windowGaps_scale 1 0 w (packedBoundaryOrigins B a)
  rw [hg]
  have hh := scatterRows_cstream A w 1 (List.replicate L 0) ((bOrder s B).map G)
    (windowGaps 1 0 (packedBoundaryOrigins B a))
  simpa only [Nat.one_mul,packedBoundary_scatter_field B a L hfit hB G hoff] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
