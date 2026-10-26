module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderCode
public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold

/-! The generated boundary coordinate stream has the exact advertised order and set. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def boundaryIndices (s t band a b : ℕ) : List ℕ :=
  (List.range s).filter (haloMaskAt true s t band a b)

theorem boundaryOrderSymbols_eq (A w s t band a b : ℕ) :
    boundaryOrderSymbols A w s t band a b =
      (boundaryIndices s t band a b).flatMap (fun k => tblPairs A w k 0) := by
  have h : ∀ ks : List ℕ, ks.flatMap (fun k =>
      if haloMaskAt true s t band a b k then tblPairs A w k 0 else []) =
      (ks.filter (haloMaskAt true s t band a b)).flatMap (fun k => tblPairs A w k 0) := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih =>
      by_cases hk : haloMaskAt true s t band a b k = true <;> simp [hk,ih]
  exact h (List.range s)

theorem boundaryIndices_order {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) (hb : b ≤ s) :
    (boundaryIndices s t band a b).map (fun k : ℕ => (k : ZMod s)) =
      bOrder s (haloBoundary s t band a b) := by
  have h : ∀ ks : List ℕ, (∀ k ∈ ks, k < s) →
      (ks.filter (haloMaskAt true s t band a b)).map (fun k : ℕ => (k : ZMod s)) =
      (ks.map (fun k : ℕ => (k : ZMod s))).filter (fun j => j ∈ haloBoundary s t band a b) := by
    intro ks
    induction ks with
    | nil => intro _; simp
    | cons k ks ih =>
      intro hks
      have ht := ih (fun j hj => hks j (by simp [hj]))
      have hm := haloMaskAt_spec true hst band a b k hb (hks k (by simp))
      by_cases hk : (k : ZMod s) ∈ haloBoundary s t band a b
      · have hmask : haloMaskAt true s t band a b k = true := hm.mpr hk
        simp [hmask,hk,ht]
      · have hmask : ¬haloMaskAt true s t band a b k = true := fun hh => hk (hm.mp hh)
        simp [hmask,hk,ht]
  simpa only [boundaryIndices,bOrder,physOrder] using h (List.range s) (fun _ hk => List.mem_range.mp hk)

theorem boundaryIndices_exact {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) (hb : b ≤ s) :
    ((boundaryIndices s t band a b).map (fun k : ℕ => (k : ZMod s))).Nodup ∧
      ((boundaryIndices s t band a b).map (fun k : ℕ => (k : ZMod s))).toFinset = haloBoundary s t band a b := by
  rw [boundaryIndices_order hst band a b hb]
  exact ⟨bOrder_nodup s _,bOrder_toFinset s _⟩

theorem boundaryIndices_length {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) (hb : b ≤ s) :
    (boundaryIndices s t band a b).length = (haloBoundary s t band a b).card := by
  obtain ⟨hnd,hset⟩ := boundaryIndices_exact hst band a b hb
  have hh := List.toFinset_card_of_nodup hnd
  simpa only [hset,List.length_map] using hh.symm

theorem boundaryOrderSymbols_length {s t : ℕ} [NeZero s] (hst : s < t)
    (A w band a b : ℕ) (hb : b ≤ s) :
    (boundaryOrderSymbols A w s t band a b).length = (haloBoundary s t band a b).card*w := by
  rw [boundaryOrderSymbols_eq]
  have h : ∀ ks : List ℕ, (ks.flatMap (fun k => tblPairs A w k 0)).length = ks.length*w := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih => simp [ih,Nat.add_mul,Nat.add_comm]
  rw [h,boundaryIndices_length hst band a b hb]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
