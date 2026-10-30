module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Dummy data precede the real payload; removing that prefix restores the
real replica order without a reversal or permutation. -/
def tilePrefixPad {α : Type*} (capacity : ℕ) (fill : α) (xs : List α) : List α :=
  List.replicate (capacity-xs.length) fill++xs

theorem tilePrefixPad_length {α : Type*} (capacity : ℕ) (fill : α) (xs : List α)
    (hfit : xs.length ≤ capacity) : (tilePrefixPad capacity fill xs).length = capacity := by
  simp only [tilePrefixPad,List.length_append,List.length_replicate]
  omega

theorem tilePrefixPad_drop {α : Type*} (capacity : ℕ) (fill : α) (xs : List α) :
    (tilePrefixPad capacity fill xs).drop (capacity-xs.length) = xs := by
  simp [tilePrefixPad,List.drop_append]

theorem tilePrefixPad_getElem? {α : Type*} (capacity : ℕ) (fill : α) (xs : List α) (i : ℕ) :
    (tilePrefixPad capacity fill xs)[capacity-xs.length+i]? = xs[i]? := by
  rw [tilePrefixPad,List.getElem?_append_right (by simp)]
  simp

theorem tilePrefixPad_zipWith {α β γ : Type*} (op : α → β → γ)
    (capacity : ℕ) (a : α) (b : β) (xs : List α) (ys : List β) (hlen : xs.length = ys.length) :
    List.zipWith op (tilePrefixPad capacity a xs) (tilePrefixPad capacity b ys) =
      tilePrefixPad capacity (op a b) (List.zipWith op xs ys) := by
  have hzip : (List.zipWith op xs ys).length = xs.length := by simp [hlen]
  simp only [tilePrefixPad,hzip,←hlen]
  induction capacity-xs.length with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ,List.cons_append,List.zipWith_cons_cons] using congrArg (List.cons (op a b)) ih

/-- Padding a rectangular replica stream adds whole dummy replicas. -/
theorem tilePrefixPad_replica_rows {α : Type*} {N K W : ℕ} (capacity : ℕ) (fill : α)
    (f : Fin N → Fin K → Fin W → α) :
    tilePrefixPad (capacity*(K*W)) fill (replicaKeyWords f) =
      List.replicate ((capacity-N)*(K*W)) fill++replicaKeyWords f := by
  simp only [tilePrefixPad,replicaKeyWords,List.length_ofFn,←Nat.sub_mul]

/-- A padded owned word supplies the router's array view directly from its
proved length. The witness is determined by that word, not by an execution oracle. -/
theorem tilePrefixPad_replica_view {α : Type*} {N K W : ℕ} (capacity : ℕ) (fill : α)
    (f : Fin N → Fin K → Fin W → α) (hN : N ≤ capacity) :
    ∃ g : Fin capacity → Fin K → Fin W → α,
      replicaKeyWords g = tilePrefixPad (capacity*(K*W)) fill (replicaKeyWords f) := by
  apply replicaKeyWords_of_length
  apply tilePrefixPad_length
  simpa only [replicaKeyWords,List.length_ofFn] using Nat.mul_le_mul_right (K*W) hN

/-- Padding paired payloads produces genuine padded bit-plane arrays. No
externally supplied encoding relation is needed by the packed router. -/
theorem tilePrefixPad_pair_view {α : Type*} {N K W : ℕ} (capacity : ℕ)
    (op : Bool → Bool → α) (realBits imagBits : Fin N → Fin K → Fin W → Bool)
    (hN : N ≤ capacity) :
    ∃ r i : Fin capacity → Fin K → Fin W → Bool,
      tilePrefixPad (capacity*(K*W)) (op false false)
        (replicaKeyWords (fun n k b => op (realBits n k b) (imagBits n k b))) =
        replicaKeyWords (fun n k b => op (r n k b) (i n k b)) := by
  obtain ⟨r,hr⟩ := tilePrefixPad_replica_view capacity false realBits hN
  obtain ⟨i,hi⟩ := tilePrefixPad_replica_view capacity false imagBits hN
  refine ⟨r,i,?_⟩
  rw [←replicaKeyWords_zipWith op realBits imagBits,
    ←tilePrefixPad_zipWith op (capacity*(K*W)) false false _ _ (by simp [replicaKeyWords]),
    ←hr,←hi,replicaKeyWords_zipWith]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
