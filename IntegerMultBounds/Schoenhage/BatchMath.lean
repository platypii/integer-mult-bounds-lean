import IntegerMultBounds.Schoenhage.Batch

/-! The batched recursion computes `ssMul` pair by pair: one level's up-sweep
of the next level's products of the down-sweep's batch gives this level's
products (`upList_nextBatch`). -/

namespace IntegerMultBounds.Schoenhage

open Schedule

theorem tpieces_eq (N x : ℕ) : tpieces (nextN N) (kOf N) (pieceOf N) x = xs N x := rfl

theorem pairsOf_zipFlat : ∀ (X Y R : List ℕ), X.length = Y.length →
    pairsOf (zipFlat X Y ++ R) = X.zip Y ++ pairsOf R
  | [], [], R, _ => by simp [zipFlat]
  | x :: X, y :: Y, R, h => by
    simp only [zipFlat, List.cons_append, pairsOf, List.zip_cons_cons]
    rw [pairsOf_zipFlat X Y R (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem upList_nextBatch {N : ℕ} (hN : N0 ≤ N) :
    ∀ (g : ℕ) (L : List ℕ), L.length = 2 * g →
      upList N (2 ^ kOf N) g ((pairsOf (nextBatch (nextN N) (kOf N) (pieceOf N) L)).map
          fun p => ssMul (nextN N) p.1 p.2) =
        (pairsOf L).map fun p => ssMul N p.1 p.2
  | 0, L, h => by
    have : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [upList, pairsOf]
  | g + 1, x :: y :: L, h => by
    have ih := upList_nextBatch hN g L (by simp at h; omega)
    simp only [nextBatch, tpieces_eq]
    rw [pairsOf_zipFlat _ _ _ (by simp [xs_length]), List.map_append, upList, pairsOf, List.map_cons]
    have hl : ((xs N x).zip (xs N y)).map (fun p => ssMul (nextN N) p.1 p.2) =
        List.zipWith (ssMul (nextN N)) (xs N x) (xs N y) := by
      rw [List.map_zip_eq_zipWith]; rfl
    have hK : (((xs N x).zip (xs N y)).map (fun p => ssMul (nextN N) p.1 p.2)).length = 2 ^ kOf N := by
      simp [xs_length]
    rw [List.take_left' hK, List.drop_left' hK, ih, hl, ssMul_eq N x y]
    simp only [show ¬ N < N0 by omega, ↓reduceIte]
  | g + 1, [], h => by simp at h
  | g + 1, [_], h => by simp at h; omega

end IntegerMultBounds.Schoenhage
