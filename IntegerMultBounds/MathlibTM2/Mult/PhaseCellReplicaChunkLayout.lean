module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout
public import Mathlib.Tactic.Ring

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host

private theorem swapList_blocks_getElem? {α : Type*} {P H D B : ℕ}
    (dflt : α) (xs : List α) (hlen : xs.length = P*H*D*B)
    {p h d b : ℕ} (hp : p < P) (hh : h < H) (hd : d < D) (hb : b < B) :
    (swapList P H 1 D B dflt xs)[((p*D+d)*H+h)*B+b]? =
      xs[((p*H+h)*D+d)*B+b]? := by
  simpa only [Nat.mul_one,Nat.add_zero] using swapList_getElem? dflt xs
    (by simpa only [Nat.mul_one] using hlen) hp hh (by decide : 0 < 1) hd hb

/-- Move a key field past the last replica chunk, then past the remaining
replica prefix. This factors the full rectangle without changing its volume. -/
theorem replicaKey_swap_factor {α : Type*} {H N K W : ℕ} (dflt : α) (xs : List α)
    (hlen : xs.length = H*N*K*W) :
    swapList 1 H 1 K (N*W) dflt (swapList H N 1 K W dflt xs) =
      swapList 1 (H*N) 1 K W dflt xs := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < K*(H*(N*W))
  · let z : Fin (K*(H*(N*W))) := ⟨i,hi⟩
    let p := finProdFinEquiv.symm z
    let q := finProdFinEquiv.symm p.2
    let r := finProdFinEquiv.symm q.2
    have hz : finProdFinEquiv (p.1,finProdFinEquiv (q.1,finProdFinEquiv (r.1,r.2))) = z := by
      simp only [r,q,p,Equiv.apply_symm_apply,Prod.mk.eta]
    have hidx : ((p.1.val*H+q.1.val)*N+r.1.val)*W+r.2.val = i := by
      have he := congrArg Fin.val hz
      change ((r.2.val+W*r.1.val)+(N*W)*q.1.val)+(H*(N*W))*p.1.val = i at he
      calc
        _ = ((r.2.val+W*r.1.val)+(N*W)*q.1.val)+(H*(N*W))*p.1.val := by ring
        _ = i := he
    have ho := swapList_blocks_getElem? dflt (swapList H N 1 K W dflt xs)
      (by simp only [swapList,List.length_map,List.length_range]; ring)
      (p := 0) (h := q.1.val) (d := p.1.val) (b := r.1.val*W+r.2.val)
      (by decide : 0 < 1) q.1.isLt p.1.isLt (mix_lt r.1.isLt r.2.isLt)
    have hm := swapList_blocks_getElem? dflt xs hlen q.1.isLt r.1.isLt p.1.isLt r.2.isLt
    have hf := swapList_blocks_getElem? dflt xs
      (by simpa only [Nat.one_mul,Nat.mul_assoc] using hlen)
      (p := 0) (h := q.1.val*N+r.1.val) (d := p.1.val) (b := r.2.val)
      (by decide : 0 < 1) (mix_lt q.1.isLt r.1.isLt) p.1.isLt r.2.isLt
    simp only [Nat.zero_mul,Nat.zero_add] at ho hf
    have hoidx : (p.1.val*H+q.1.val)*(N*W)+(r.1.val*W+r.2.val) = i := by
      rw [←hidx]; ring
    have hmidx : ((q.1.val*K+p.1.val)*N+r.1.val)*W+r.2.val =
        (q.1.val*K+p.1.val)*(N*W)+(r.1.val*W+r.2.val) := by ring
    have hfidx : (p.1.val*(H*N)+(q.1.val*N+r.1.val))*W+r.2.val = i := by
      rw [←hidx]; ring
    rw [hoidx] at ho
    rw [hmidx] at hm
    rw [hfidx] at hf
    exact ho.trans (hm.trans hf.symm)
  · have hl : (swapList 1 H 1 K (N*W) dflt (swapList H N 1 K W dflt xs)).length = K*(H*(N*W)) := by
      simp [swapList,Nat.mul_assoc]
    have hr : (swapList 1 (H*N) 1 K W dflt xs).length = K*(H*(N*W)) := by
      simp [swapList,Nat.mul_assoc]
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

private theorem swapList_one_left {α : Type*} {K W : ℕ} (dflt : α) (xs : List α)
    (hlen : xs.length = K*W) : swapList 1 1 1 K W dflt xs = xs := by
  have hsrc (i : ℕ) : swapSrc 1 1 K W i = i := by
    simp only [swapSrc,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.add_zero]
    rw [show i/W/K*K+i/W%K = i/W by simpa only [Nat.mul_comm] using Nat.div_add_mod (i/W) K]
    simpa only [Nat.mul_comm] using Nat.div_add_mod i W
  apply List.ext_getElem?
  intro i
  simp only [swapList,Nat.mul_one,Nat.one_mul]
  by_cases hi : i < xs.length
  · have hi' : i < K*W := hlen ▸ hi
    rw [List.getElem?_map,List.getElem?_range hi',Option.map_some,hsrc,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getElem?_eq_none (by simp only [List.length_map,List.length_range]; omega),
      List.getElem?_eq_none (by omega)]

/-- Each pair records the prefix multiplicity and suffix block width for one
interchange of two equal `K`-sized address chunks. -/
def replicaChunkSwaps (K W : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | c+1 => (K^c,W)::replicaChunkSwaps K (K*W) c

def runReplicaChunkSwaps {α : Type*} (K : ℕ) (dflt : α) :
    List (ℕ × ℕ) → List α → List α
  | [],xs => xs
  | (P,B)::rs,xs => runReplicaChunkSwaps K dflt rs (swapList P K 1 K B dflt xs)

theorem replicaChunkSwaps_length (K W c : ℕ) : (replicaChunkSwaps K W c).length = c := by
  induction c generalizing W with
  | zero => rfl
  | succ c ih => simp only [replicaChunkSwaps,List.length_cons,ih]

/-- Every stage touches the original tile volume, including spectator fields. -/
theorem replicaChunkSwaps_volume (K W c : ℕ) :
    ((replicaChunkSwaps K W c).map (fun r => r.1*K*K*r.2)).sum = c*(K^c*K*W) := by
  induction c generalizing W with
  | zero => simp [replicaChunkSwaps]
  | succ c ih =>
    simp only [replicaChunkSwaps,List.map_cons,List.sum_cons,ih,pow_succ]
    ring

theorem replicaChunkSwaps_positive {K W : ℕ} (hK : 0 < K) (hW : 0 < W) (c : ℕ) :
    ∀ r ∈ replicaChunkSwaps K W c, 0 < r.1 ∧ 0 < r.2 := by
  induction c generalizing W with
  | zero => simp [replicaChunkSwaps]
  | succ c ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r; exact ⟨pow_pos hK _,hW⟩
    · exact ih (Nat.mul_pos hK hW) r hr

/-- A tile with `K^c` replicas is grouped by key using exactly `c` balanced
chunk interchanges. The induction changes spectators, never the chunk width. -/
theorem runReplicaChunkSwaps_eq {α : Type*} (K W c : ℕ) (dflt : α) (xs : List α)
    (hlen : xs.length = K^c*K*W) :
    runReplicaChunkSwaps K dflt (replicaChunkSwaps K W c) xs =
      swapList 1 (K^c) 1 K W dflt xs := by
  induction c generalizing W xs with
  | zero =>
    simpa only [replicaChunkSwaps,runReplicaChunkSwaps,pow_zero,Nat.one_mul] using
      (swapList_one_left dflt xs (by simpa using hlen)).symm
  | succ c ih =>
    simp only [replicaChunkSwaps,runReplicaChunkSwaps]
    rw [ih (K*W) _ (by simp only [swapList,List.length_map,List.length_range,Nat.mul_one]; ring)]
    simpa only [pow_succ] using replicaKey_swap_factor (H := K^c) (N := K) dflt xs
      (by simpa only [pow_succ] using hlen)

/-- The chunk schedule has exactly the complete-key output layout used by the
prepared numerical batches. -/
theorem runReplicaChunkSwaps_words {α : Type*} (K W c : ℕ) (dflt : α)
    (f : Fin (K^c) → Fin K → Fin W → α) :
    runReplicaChunkSwaps K dflt (replicaChunkSwaps K W c) (replicaKeyWords f) = keyReplicaWords f := by
  rw [runReplicaChunkSwaps_eq K W c dflt _ (by simp [replicaKeyWords,Nat.mul_assoc])]
  exact replicaKeyWords_swap dflt f

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
