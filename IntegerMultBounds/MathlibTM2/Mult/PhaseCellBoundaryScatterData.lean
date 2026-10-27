module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule

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
  let ps := boundaryScatterOrigins s B
  let E : List GaussianInt := List.replicate s 0
  let X := (bOrder s B).map G
  have hdis := boundaryScatterOrigins_disjoint s B
  have hfit : ∀ p ∈ ps, p+1 ≤ E.length := by simpa [E] using boundaryScatterOrigins_fit s B
  have hx : ps.length*1 ≤ X.length := by simp [ps,boundaryScatterOrigins,X]
  have hf := windowGaps_fits 1 0 ps E (fun _ _ => Nat.zero_le _) hdis hfit
  have hlen := length_scatterRows 1 E X (windowGaps 1 0 ps) (by simpa using hf) (by simpa using hx)
  simp only [boundaryScatterGaps,Nat.mul_one]
  rw [show (fun i : ℕ => i) = id from rfl,List.map_id]
  change scatterRows 1 E X (windowGaps 1 0 ps) = chirpLine s G
  apply List.ext_getElem (by simpa [E] using hlen)
  intro i hi hj
  have hiS : i < s := by simpa [E,hlen] using hi
  have hival : (i : ZMod s).val = i := by simp [ZMod.val_natCast,Nat.mod_eq_of_lt hiS]
  have htarget : (chirpLine s G)[i] = G (i : ZMod s) := by simp [chirpLine]
  rw [htarget]
  by_cases hiB : (i : ZMod s) ∈ B
  · have hm : (i : ZMod s) ∈ bOrder s B := by
      simpa only [← List.mem_toFinset,bOrder_toFinset] using hiB
    obtain ⟨n,hn,hcoord⟩ := List.getElem_of_mem hm
    have hnps : n < ps.length := by simpa [ps,boundaryScatterOrigins] using hn
    have hnX : n < X.length := by simpa [X] using hn
    have hp : ps[n] = i := by simp [ps,boundaryScatterOrigins,hcoord,hival]
    have hw := scatterRows_absolute 1 ps E X hdis hfit hx n hnps
    rw [hp,Nat.mul_one,List.take_one_drop_eq_of_lt_length hi,
      List.take_one_drop_eq_of_lt_length hnX] at hw
    have he := congrArg (fun l : List GaussianInt => l.headD 0) hw
    simpa [X,hcoord] using he
  · have ho : ∀ n (hn : n < ps.length), i < ps[n] ∨ ps[n]+1 ≤ i := by
      intro n hn
      have hnB : n < (bOrder s B).length := by simpa [ps,boundaryScatterOrigins] using hn
      have hm : (bOrder s B)[n] ∈ B := by
        have h := List.mem_toFinset.mpr (List.getElem_mem hnB)
        simpa only [bOrder_toFinset] using h
      have hne : ps[n] ≠ i := by
        intro he
        have hval : (bOrder s B)[n].val = (i : ZMod s).val := by
          simpa [ps,boundaryScatterOrigins,hival] using he
        exact hiB ((ZMod.val_injective s hval) ▸ hm)
      omega
    have he := scatterRows_absolute_off 1 ps E X hdis hfit hx i ho
    rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem (by simpa [E] using hiS)] at he
    have he' := Option.some.inj he
    simpa [E,hoff _ hiB] using he'

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
