module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaChunkInverse

/-! Factor a rectangular transpose into adjacent field swaps. Factor sizes are
independent; balance is a separate condition for the machine implementation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host

structure RectangularChunkSwap where
  outerCount : ℕ
  leftWidth : ℕ
  rightWidth : ℕ
  blockWidth : ℕ

def RectangularChunkSwap.volume (r : RectangularChunkSwap) : ℕ :=
  r.outerCount*r.leftWidth*r.rightWidth*r.blockWidth

def RectangularChunkSwap.inverse (r : RectangularChunkSwap) : RectangularChunkSwap :=
  ⟨r.outerCount,r.rightWidth,r.leftWidth,r.blockWidth⟩

def runRectangularChunkSwaps {α : Type*} (fill : α) :
    List RectangularChunkSwap → List α → List α
  | [],xs => xs
  | r::rs,xs => runRectangularChunkSwaps fill rs
      (swapList r.outerCount r.leftWidth 1 r.rightWidth r.blockWidth fill xs)

/-- Move the key field left past one factor at a time, starting at the
least significant factor. Every stage retains the complete tile volume. -/
def rectangularChunkSwaps (K W : ℕ) : List ℕ → List RectangularChunkSwap
  | [] => []
  | n::ns => ⟨ns.prod,n,K,W⟩::rectangularChunkSwaps K (n*W) ns

theorem rectangularChunkSwaps_length (K W : ℕ) (ns : List ℕ) :
    (rectangularChunkSwaps K W ns).length = ns.length := by
  induction ns generalizing W with
  | nil => rfl
  | cons n ns ih => simp only [rectangularChunkSwaps,List.length_cons,ih]

theorem rectangularChunkSwaps_stage_volume (K W : ℕ) (ns : List ℕ) :
    ∀ r ∈ rectangularChunkSwaps K W ns, r.volume = ns.prod*K*W := by
  induction ns generalizing W with
  | nil => simp [rectangularChunkSwaps]
  | cons n ns ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r; simp only [RectangularChunkSwap.volume,List.prod_cons]; ring
    · rw [ih (n*W) r hr,List.prod_cons]; ring

theorem rectangularChunkSwaps_volume (K W : ℕ) (ns : List ℕ) :
    ((rectangularChunkSwaps K W ns).map RectangularChunkSwap.volume).sum =
      ns.length*(ns.prod*K*W) := by
  rw [List.map_congr_left (fun r hr => rectangularChunkSwaps_stage_volume K W ns r hr)]
  simp [rectangularChunkSwaps_length]

theorem runRectangularChunkSwaps_eq {α : Type*} (K W : ℕ) (ns : List ℕ)
    (fill : α) (xs : List α) (hlen : xs.length = ns.prod*K*W) :
    runRectangularChunkSwaps fill (rectangularChunkSwaps K W ns) xs =
      swapList 1 ns.prod 1 K W fill xs := by
  induction ns generalizing W xs with
  | nil =>
    simpa only [rectangularChunkSwaps,runRectangularChunkSwaps,List.prod_nil,pow_zero,replicaChunkSwaps,runReplicaChunkSwaps] using
      (runReplicaChunkSwaps_eq K W 0 fill xs (by simpa using hlen))
  | cons n ns ih =>
    simp only [rectangularChunkSwaps,runRectangularChunkSwaps]
    rw [ih (n*W) _ (by simp only [swapList,List.length_map,List.length_range]; ring)]
    have hh := replicaKey_swap_factor (H := ns.prod) (N := n) (K := K) (W := W)
      fill xs (by rw [List.prod_cons] at hlen; nlinarith only [hlen])
    simpa only [List.prod_cons,Nat.mul_comm] using hh

theorem runRectangularChunkSwaps_append {α : Type*} (fill : α)
    (rs ss : List RectangularChunkSwap) (xs : List α) :
    runRectangularChunkSwaps fill (rs++ss) xs =
      runRectangularChunkSwaps fill ss (runRectangularChunkSwaps fill rs xs) := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem runRectangularChunkSwaps_length {α : Type*} (fill : α)
    (rs : List RectangularChunkSwap) (V : ℕ)
    (hvolume : ∀ r ∈ rs, r.volume = V) (xs : List α) (hlen : xs.length = V) :
    (runRectangularChunkSwaps fill rs xs).length = V := by
  induction rs generalizing xs with
  | nil => exact hlen
  | cons r rs ih =>
    apply ih (by intro s hs; exact hvolume s (by simp [hs]))
    simpa only [swapList,List.length_map,List.length_range,Nat.mul_one,
      RectangularChunkSwap.volume,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hvolume r (by simp)

/-- A rectangular stage is inverted by exchanging its widths. Reverse the
schedule as well; no symmetry assumption on the factors is needed. -/
theorem runRectangularChunkSwaps_reverse_cancel {α : Type*} (fill : α)
    (rs : List RectangularChunkSwap) (V : ℕ)
    (hvolume : ∀ r ∈ rs, r.volume = V) (xs : List α) (hlen : xs.length = V) :
    runRectangularChunkSwaps fill (rs.reverse.map RectangularChunkSwap.inverse)
      (runRectangularChunkSwaps fill rs xs) = xs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih =>
    have ht : ∀ s ∈ rs, s.volume = V := by
      intro s hs; exact hvolume s (by simp [hs])
    have hl : (swapList r.outerCount r.leftWidth 1 r.rightWidth r.blockWidth fill xs).length = V := by
      simpa only [swapList,List.length_map,List.length_range,Nat.mul_one,
        RectangularChunkSwap.volume,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hvolume r (by simp)
    rw [List.reverse_cons,List.map_append,runRectangularChunkSwaps_append]
    change swapList r.outerCount r.rightWidth 1 r.leftWidth r.blockWidth fill
      (runRectangularChunkSwaps fill (rs.reverse.map RectangularChunkSwap.inverse)
        (runRectangularChunkSwaps fill rs
          (swapList r.outerCount r.leftWidth 1 r.rightWidth r.blockWidth fill xs))) = xs
    rw [ih ht _ hl]
    apply swapList_involution
    simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one,
      RectangularChunkSwap.volume] using hlen.trans (hvolume r (by simp)).symm


theorem rectangularChunkSwaps_positive {K W : ℕ} (hK : 0 < K) (hW : 0 < W)
    (ns : List ℕ) (hns : ∀ n ∈ ns, 0 < n) :
    ∀ r ∈ rectangularChunkSwaps K W ns,
      0 < r.outerCount ∧ 0 < r.leftWidth ∧ 0 < r.rightWidth ∧ 0 < r.blockWidth := by
  induction ns generalizing W with
  | nil => simp [rectangularChunkSwaps]
  | cons n ns ih =>
    have hn := hns n (by simp)
    have ht : ∀ m ∈ ns, 0 < m := by intro m hm; exact hns m (by simp [hm])
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      exact ⟨List.prod_pos ht,hn,hK,hW⟩
    · exact ih (Nat.mul_pos hn hW) ht r hr

/-- Actual packed input words have the complete-key output ordering, with no
padding or change to symbol offsets inside each payload block. -/
theorem runRectangularChunkSwaps_words {α : Type*} (K W : ℕ) (ns : List ℕ)
    (fill : α) (f : Fin ns.prod → Fin K → Fin W → α) :
    runRectangularChunkSwaps fill (rectangularChunkSwaps K W ns) (replicaKeyWords f) =
      keyReplicaWords f := by
  rw [runRectangularChunkSwaps_eq K W ns fill _ (by simp [replicaKeyWords,Nat.mul_assoc])]
  exact replicaKeyWords_swap fill f

/-- Numerical outputs can return through the inverse route regardless of
which new values replaced the input words. -/
theorem runRectangularChunkSwaps_inverse_words {α : Type*} (K W : ℕ) (ns : List ℕ)
    (fill : α) (f : Fin ns.prod → Fin K → Fin W → α) :
    runRectangularChunkSwaps fill
      ((rectangularChunkSwaps K W ns).reverse.map RectangularChunkSwap.inverse)
      (keyReplicaWords f) = replicaKeyWords f := by
  have hh := runRectangularChunkSwaps_reverse_cancel fill (rectangularChunkSwaps K W ns)
    (ns.prod*K*W) (rectangularChunkSwaps_stage_volume K W ns) (replicaKeyWords f)
    (by simp [replicaKeyWords,Nat.mul_assoc])
  rwa [runRectangularChunkSwaps_words] at hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
