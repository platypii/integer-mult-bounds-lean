module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedScatter

/-! Publish disjoint cell windows into a packed halo. The cost is bounded by
local volume; neither fitting nor addressing uses the ambient period. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def packedCellGaps (L w : ℕ) (offsets : List ℕ) : List ℕ :=
  windowGaps (L*w) 0 (offsets.map (·*w))

theorem packedCellGaps_scale (L w : ℕ) (offsets : List ℕ) :
    packedCellGaps L w offsets = (windowGaps L 0 offsets).map (·*w) := by
  simpa only [packedCellGaps,Nat.zero_mul] using windowGaps_scale L 0 w offsets

/-- Local publication is an encoding of the same scatter on Gaussian words. -/
theorem packedCellScatter_cstream (A L w : ℕ) (offsets : List ℕ)
    (E X : List GaussianInt) :
    scatterRows (L*w) (cstream A w E) (cstream A w X) (packedCellGaps L w offsets) =
      cstream A w (scatterRows L E X (windowGaps L 0 offsets)) := by
  rw [packedCellGaps_scale,scatterRows_cstream]

/-- Packed aligned publication preserves a common encoded magnitude bound. -/
theorem packedCellScatter_range {A w q e : ℕ} (L : ℕ) (offsets : List ℕ)
    (E X : List (Fin (A+4))) (hE : EncodedRange A w q e E) (hX : EncodedRange A w q e X) :
    EncodedRange A w q e (scatterRows (L*w) E X (packedCellGaps L w offsets)) := by
  obtain ⟨es,rfl,hes⟩ := hE
  obtain ⟨xs,rfl,hxs⟩ := hX
  rw [packedCellScatter_cstream]
  refine ⟨_,rfl,?_⟩
  intro z hz
  rcases scatterRows_mem L es xs _ z hz with hz | hz
  · exact hes z hz
  · exact hxs z hz

theorem packedCell_offsets_disjoint (L w : ℕ) (offsets : List ℕ)
    (hdis : offsets.Pairwise (fun i j => i+L ≤ j)) :
    (offsets.map (·*w)).Pairwise (fun i j => i+L*w ≤ j) := by
  rw [List.pairwise_map]
  exact hdis.imp (fun h => by simpa only [Nat.add_mul] using Nat.mul_le_mul_right w h)

theorem packedCell_offsets_fit (N L w : ℕ) (offsets : List ℕ)
    (E : List (Fin (A+4))) (hE : E.length = N*w) (hfit : ∀ j ∈ offsets, j+L ≤ N) :
    ∀ j ∈ offsets.map (·*w), j+L*w ≤ E.length := by
  intro j hj
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj
  simpa only [hE,← Nat.add_mul] using Nat.mul_le_mul_right w (hfit k hk)

theorem packedCellScatter_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (N L w : ℕ) (hL : 1 ≤ L) (hw : 1 ≤ w) (offsets : List ℕ)
    (hdis : offsets.Pairwise (fun i j => i+L ≤ j)) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = N*w) (hys : ys.length = offsets.length*(L*w))
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (packedCellGaps L w offsets))
    (hdst : S.R dst = E++outputTail) (hsrc : S.R src = ys++sourceTail)
    (hwidth : (S.R window).length = L*w)
    (hclean : ∀ k ∈ [savedControl,gap,acc,trash,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 35*N*w+6 ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          (scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail))}) := by
  have hd := packedCell_offsets_disjoint L w offsets hdis
  have hf := packedCell_offsets_fit N L w offsets E hE hfit
  have hfits : ScatterFits (L*w) E (packedCellGaps L w offsets) := by
    simpa [packedCellGaps] using windowGaps_fits (L*w) 0 (offsets.map (·*w)) E
      (fun _ _ => Nat.zero_le _) hd hf
  have hfits' : ScatterFits (L*w) (E++outputTail) (packedCellGaps L w offsets) := by
    simpa [packedCellGaps] using windowGaps_fits (L*w) 0 (offsets.map (·*w)) (E++outputTail)
      (fun _ _ => Nat.zero_le _) hd (fun j hj => (hf j hj).trans (by simp))
  have hlength : (packedCellGaps L w offsets).length = offsets.length := by simp [packedCellGaps]
  have hvolume := scatterVolume_le (L*w) E (packedCellGaps L w offsets) hfits
  rw [scatterVolume,hlength,hE] at hvolume
  have hLw : 1 ≤ L*w := by simpa using Nat.mul_le_mul hL hw
  have hcount : offsets.length ≤ N*w := by
    have hc : offsets.length ≤ offsets.length*(L*w) := by
      simpa using Nat.mul_le_mul_left offsets.length hLw
    omega
  obtain ⟨v',hu,he⟩ := scatterBatch_exec (body := body) hreg (L*w) (packedCellGaps L w offsets)
    (E++outputTail) (ys++sourceTail) hfits' (by simp [hlength,← hys]) v S hc hdst hsrc hwidth hclean
  refine ⟨v',_,hu,by rw [hlength]; nlinarith only [hvolume,hcount],he.cast rfl ?_⟩
  have hdrop : (ys++sourceTail).drop ((packedCellGaps L w offsets).length*(L*w)) = sourceTail := by
    rw [hlength,← hys,List.drop_append_length]
  have hdest : scatterRows (L*w) (E++outputTail) (ys++sourceTail) (packedCellGaps L w offsets) =
      scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail := by
    rw [scatterRows_append _ _ _ _ _ hfits,
      scatterRows_source_suffix _ _ _ _ _ (by rw [hlength,hys])]
  rw [hdrop,hdest]

/-- Every published word is the same word returned by compact cell arithmetic. -/
theorem packedCellScatter_word (N L w : ℕ) (offsets : List ℕ)
    (E X : List (Fin (A+4))) (hE : E.length = N*w)
    (hdis : offsets.Pairwise (fun i j => i+L ≤ j)) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hX : offsets.length*(L*w) ≤ X.length)
    (r i : ℕ) (hr : r < offsets.length) (hi : i < L) :
    ((scatterRows (L*w) E X (packedCellGaps L w offsets)).drop ((offsets[r]+i)*w)).take w =
      (X.drop ((r*L+i)*w)).take w := by
  have hh := scatterRows_absolute (L*w) (offsets.map (·*w)) E X
    (packedCell_offsets_disjoint L w offsets hdis) (packedCell_offsets_fit N L w offsets E hE hfit)
    (by simpa using hX) r (by simpa using hr)
  simp only [List.getElem_map] at hh
  have hword : w ≤ L*w-i*w := by
    have hm := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hi)
    change (i+1)*w ≤ L*w at hm
    rw [Nat.add_mul,Nat.one_mul] at hm
    omega
  have hs := congrArg (fun zs : List (Fin (A+4)) => (zs.drop (i*w)).take w) hh
  simpa only [List.drop_take,List.take_take,List.drop_drop,Nat.min_eq_left hword,
    packedCellGaps,Nat.add_mul,Nat.mul_assoc] using hs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
