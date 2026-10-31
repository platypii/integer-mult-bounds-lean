module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGatherData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Consecutive packed halos retain their original ambient coordinates. A
replica-major sweep gathers all ordered cell windows without ambient scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedReplicaWords {s : ℕ} (origin span N : ℕ) (C : ℕ → ZMod s → GaussianInt) : List GaussianInt :=
  (List.range N).flatMap (fun r => packedInterval origin span (C r))

@[simp] theorem packedReplicaWords_length {s : ℕ} (origin span N : ℕ)
    (C : ℕ → ZMod s → GaussianInt) (hspan : origin+span ≤ s) :
    (packedReplicaWords origin span N C).length = N*span := by
  simp [packedReplicaWords,List.length_flatMap,packedInterval_length _ hspan]

private theorem packedInterval_window {s : ℕ} (origin span off L : ℕ)
    (C : ZMod s → GaussianInt) (hspan : origin+span ≤ s) (hfit : off+L ≤ span) :
    ((packedInterval origin span C).drop off).take L =
      cellSourceRows L (fun _ => ((origin+off : ℕ) : ZMod s)) (fun _ => C) 0 := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,packedInterval_length C hspan,cellSourceRows_length]
    omega
  · intro k hk _
    have hkL : k < L := by simpa only [List.length_take,List.length_drop,
      packedInterval_length C hspan,Nat.min_eq_left (by omega : L ≤ span-off)] using hk
    simp only [List.getElem_take,List.getElem_drop]
    rw [packedInterval_get C hspan (by omega)]
    simp [cellSourceRows,Nat.cast_add,add_assoc]

theorem packedReplicaStream_window {A s : ℕ} (w origin span N : ℕ)
    (C : ℕ → ZMod s → GaussianInt) (off L r : ℕ)
    (hspan : origin+span ≤ s) (hr : r < N) (hfit : off+L ≤ span) :
    ((cstream A w (packedReplicaWords origin span N C)).drop ((r*span+off)*w)).take (L*w) =
      cstream A w (cellSourceRows L (fun _ => ((origin+off : ℕ) : ZMod s)) C r) := by
  rw [rsa_cstream_drop,rsa_cstream_take]
  have hh := flatten_uniform_window ((List.range N).map (fun r => packedInterval origin span (C r)))
    span off L r (by
      intro row hrow
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hrow
      exact packedInterval_length _ hspan) (by simpa using hr) hfit
  have hrow : ((List.range N).map (fun j => packedInterval origin span (C j))).getD r [] =
      packedInterval origin span (C r) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hr)]
    simp
  rw [hrow,packedInterval_window origin span off L (C r) hspan hfit] at hh
  simpa only [packedReplicaWords,List.flatMap_def,cellSourceRows] using congrArg (cstream A w) hh

def packedReplicaSymbolOrigins (N span w : ℕ) (offsets : List ℕ) : List ℕ :=
  (List.range N).flatMap (fun r => offsets.map (fun j => (r*span+j)*w))

@[simp] theorem packedReplicaSymbolOrigins_length (N span w : ℕ) (offsets : List ℕ) :
    (packedReplicaSymbolOrigins N span w offsets).length = N*offsets.length := by
  simp [packedReplicaSymbolOrigins,List.length_flatMap]

theorem packedReplicaSymbolOrigins_ordered (N span L w : ℕ) (offsets : List ℕ)
    (hordered : offsets.Pairwise (· ≤ ·)) (hfit : ∀ j ∈ offsets, j+L ≤ span) :
    (packedReplicaSymbolOrigins N span w offsets).Pairwise (· ≤ ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro r _
    apply List.pairwise_map.mpr
    exact hordered.imp (fun h => Nat.mul_le_mul_right w (Nat.add_le_add_left h _))
  · apply List.pairwise_lt_range.imp
    intro r r' hrr a ha b hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
    apply Nat.mul_le_mul_right w
    have hi' := hfit i hi
    have hs := Nat.mul_le_mul_right span (show r+1 ≤ r' by omega)
    nlinarith only [hi',hs,Nat.zero_le j]

theorem packedReplicaSymbolOrigins_fit (N span L w : ℕ) (offsets : List ℕ)
    (hfit : ∀ j ∈ offsets, j+L ≤ span) :
    ∀ p ∈ packedReplicaSymbolOrigins N span w offsets, p+L*w ≤ N*span*w := by
  intro p hp
  obtain ⟨r,hr,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  have hrN : r+1 ≤ N := List.mem_range.mp hr
  have hj' := hfit j hj
  have hs := Nat.mul_le_mul_right span hrN
  have hf : r*span+j+L ≤ N*span := by nlinarith only [hj',hs]
  simpa only [Nat.add_mul,Nat.mul_assoc] using Nat.mul_le_mul_right w hf

theorem packedReplicaGatherRows_eq {A s : ℕ} (w origin span N L : ℕ) (offsets : List ℕ)
    (C : ℕ → ZMod s → GaussianInt) (hspan : origin+span ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ span) :
    (packedReplicaSymbolOrigins N span w offsets).flatMap
      (fun p => ((cstream A w (packedReplicaWords origin span N C)).drop p).take (L*w)) =
    cstream A w ((List.range N).flatMap (fun r => offsets.flatMap
      (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) C r))) := by
  simp only [packedReplicaSymbolOrigins,List.flatMap_assoc,List.flatMap_map,cstream]
  apply List.flatMap_congr
  intro r hr
  apply List.flatMap_congr
  intro j hj
  exact packedReplicaStream_window w origin span N C j L r hspan (List.mem_range.mp hr) (hfit j hj)

theorem range_getD_flatMap {α β : Type} (xs : List α) (d : α) (f : α → List β) :
    (List.range xs.length).flatMap (fun j => f (xs.getD j d)) = xs.flatMap f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [List.range_succ_eq_map,List.flatMap_map] using congrArg (f x ++ ·) ih

/-- The gathered rows are exactly the combined numerical batch's indexed ABI. -/
theorem packedReplicaRows_eq_batch {s : ℕ} (N origin L : ℕ) (offsets : List ℕ)
    (C : ℕ → ZMod s → GaussianInt) :
    (List.range N).flatMap (fun r => offsets.flatMap
      (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) C r)) =
    (List.range N).flatMap (fun r => (List.range offsets.length).flatMap
      (cellSourceRows L (fun j => ((origin+offsets.getD j 0 : ℕ) : ZMod s)) (fun _ => C r))) := by
  apply List.flatMap_congr
  intro r _
  symm
  change (List.range offsets.length).flatMap (fun j =>
    cellSourceRows L (fun j => ((origin+offsets.getD j 0 : ℕ) : ZMod s)) (fun _ => C r) j) = _
  simpa only [cellSourceRows] using range_getD_flatMap offsets 0
    (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) C r)

/-- A list of gathered RHS rows has the exact indexed numerical layout. The
default is used only outside the declared replica range. -/
theorem packedReplicaRows_list_eq_batch {s : ℕ} (origin L : ℕ) (offsets : List ℕ)
    (Fs : List (ZMod s → GaussianInt)) (d : ZMod s → GaussianInt) :
    Fs.flatMap (fun F => offsets.flatMap (fun j =>
      cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)) =
    (List.range Fs.length).flatMap (fun r => (List.range offsets.length).flatMap
      (cellSourceRows L (fun j => ((origin+offsets.getD j 0 : ℕ) : ZMod s)) (fun _ => Fs.getD r d))) := by
  calc
    _ = (List.range Fs.length).flatMap (fun r => offsets.flatMap (fun j =>
        cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => Fs.getD r d) 0)) :=
      (range_getD_flatMap Fs d _).symm
    _ = (List.range Fs.length).flatMap (fun r => offsets.flatMap (fun j =>
        cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun r => Fs.getD r d) r)) := by
      simp only [cellSourceRows]
    _ = _ := packedReplicaRows_eq_batch Fs.length origin L offsets (fun r => Fs.getD r d)

/-- Byte-level bridge, also applicable to the gather loop's reversed RHS list. -/
theorem packedReplicaStream_list_eq_batch {A s : ℕ} (w origin L : ℕ) (offsets : List ℕ)
    (Fs : List (ZMod s → GaussianInt)) (d : ZMod s → GaussianInt) :
    Fs.flatMap (fun F => cstream A w (offsets.flatMap (fun j =>
      cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0))) =
    cstream A w ((List.range Fs.length).flatMap (fun r => (List.range offsets.length).flatMap
      (cellSourceRows L (fun j => ((origin+offsets.getD j 0 : ℕ) : ZMod s)) (fun _ => Fs.getD r d)))) := by
  rw [←packedReplicaRows_list_eq_batch origin L offsets Fs d]
  simp only [cstream,List.flatMap_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
