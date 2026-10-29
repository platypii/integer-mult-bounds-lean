module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryScatterData

/-! Sparse publication of ascending boundary words into a zero ambient line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

noncomputable def boundaryScatterOrigins (s : ℕ) [NeZero s] (B : Finset (ZMod s)) : List ℕ :=
  (bOrder s B).map ZMod.val

noncomputable def boundaryScatterGaps (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) : List ℕ :=
  windowGaps w 0 ((boundaryScatterOrigins s B).map (fun i => i*w))

theorem boundaryScatterOrigins_disjoint (s : ℕ) [NeZero s] (B : Finset (ZMod s)) :
    (boundaryScatterOrigins s B).Pairwise (fun p q => p+1 ≤ q) := by
  rw [boundaryScatterOrigins,List.pairwise_map]
  exact (bOrder_val_sorted s B).imp (fun h => by omega)

theorem boundaryScatterOrigins_fit (s : ℕ) [NeZero s] (B : Finset (ZMod s)) :
    ∀ i ∈ boundaryScatterOrigins s B, i+1 ≤ s := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact Nat.succ_le_of_lt j.val_lt

/-- Sparse unit-window publication exactly realizes a zero-extended field. -/
theorem boundary_scatter_field (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0) :
    scatterRows 1 (List.replicate s 0) ((bOrder s B).map G)
      (boundaryScatterGaps s B 1) = chirpLine s G := by
  have hh := packedBoundary_scatter_field B 0 s (by omega)
    (fun i _ => ⟨Nat.zero_le _,by simpa using i.val_lt⟩) G hoff
  simpa [boundaryScatterGaps,boundaryScatterOrigins,packedBoundaryOrigins,Function.comp_def,
    packedInterval,List.take_of_length_le (show (chirpLine s G).length ≤ s by simp)] using hh

theorem boundaryScatterGaps_scale (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) :
    boundaryScatterGaps s B w = (windowGaps 1 0 (boundaryScatterOrigins s B)).map (fun d => d*w) := by
  simpa only [boundaryScatterGaps,Nat.one_mul,Nat.zero_mul] using windowGaps_scale 1 0 w (boundaryScatterOrigins s B)

@[simp] theorem boundaryScatterGaps_length (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) :
    (boundaryScatterGaps s B w).length = B.card := by
  simp [boundaryScatterGaps,boundaryScatterOrigins,bOrder_length]

theorem boundaryScatterGaps_fits {α : Type*} (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (w : ℕ) (E : List α) (hlen : s*w ≤ E.length) : ScatterFits w E (boundaryScatterGaps s B w) := by
  have hdis : ((boundaryScatterOrigins s B).map (fun i => i*w)).Pairwise (fun p q => p+w ≤ q) := by
    rw [List.pairwise_map]
    exact (boundaryScatterOrigins_disjoint s B).imp (fun h => by
      simpa [Nat.add_mul] using Nat.mul_le_mul_right w h)
  have hf : ∀ p ∈ (boundaryScatterOrigins s B).map (fun i => i*w), p+w ≤ E.length := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have h := Nat.mul_le_mul_right w (boundaryScatterOrigins_fit s B i hi)
    have h' : i*w+w ≤ s*w := by simpa [Nat.add_mul] using h
    exact h'.trans hlen
  simpa only [boundaryScatterGaps,List.drop_zero] using windowGaps_fits w 0 _ E (fun _ _ => Nat.zero_le _) hdis hf

theorem boundaryScatterGaps_volume (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) :
    (boundaryScatterGaps s B w).sum + B.card*w ≤ s*w := by
  have h := scatterVolume_le w (List.replicate (s*w) ()) (boundaryScatterGaps s B w)
    (boundaryScatterGaps_fits s B w _ (by simp))
  simpa [scatterVolume] using h

theorem boundaryScatterCost_le (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) (hw : 1 ≤ w) :
    B.card*(12*w+23)+12*(boundaryScatterGaps s B w).sum+6 ≤ 35*s*w+6 := by
  have hv := boundaryScatterGaps_volume s B w
  have hn : B.card ≤ B.card*w := by simpa using Nat.mul_le_mul_left B.card hw
  have hnw : B.card*w ≤ s*w := by omega
  nlinarith only [hv,hn,hnw]

/-- Sparse encoded publication is exactly the ambient recovery field stream. -/
theorem boundary_scatter_cstream (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (A w : ℕ)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0) :
    scatterRows w (cstream A w (List.replicate s 0)) (cstream A w ((bOrder s B).map G))
      (boundaryScatterGaps s B w) = cstream A w (chirpLine s G) := by
  rw [boundaryScatterGaps_scale]
  have h := scatterRows_cstream A w 1 (List.replicate s 0) ((bOrder s B).map G)
    (windowGaps 1 0 (boundaryScatterOrigins s B))
  have hd := boundary_scatter_field s B G hoff
  simp only [boundaryScatterGaps,Nat.mul_one] at hd
  rw [show (fun i : ℕ => i) = id from rfl,List.map_id] at hd
  simpa only [Nat.one_mul,hd] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
