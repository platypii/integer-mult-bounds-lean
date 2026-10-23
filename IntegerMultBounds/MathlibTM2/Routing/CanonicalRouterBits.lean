module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterStage
public import IntegerMultBounds.MathlibTM2.Routing.OriginalMatchingRepairBits

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
def canonicalRouterMiddleEmbedding (n : ℕ) (hn : canonicalRouterStride n ≤ n) (k : Fin 3)
    (q : Fin (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n))) : Fin n :=
  reservoirPlacement n (routingReservoirWidth n (canonicalRouterGap n))
    (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k
    (middleCoordinate (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n))
      (reservoirMiddle_fit n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))) q)

theorem canonicalRouterMiddleEmbedding_injective (n : ℕ) (hn : canonicalRouterStride n ≤ n) (k : Fin 3) :
    Function.Injective (canonicalRouterMiddleEmbedding n hn k) := by
  intro q q' h
  apply middleCoordinate_injective _ _ _
  exact (reservoirPlacement n _ _ _ _ k).injective h

theorem canonicalRouterMiddleEmbedding_source (n : ℕ) (hn : canonicalRouterStride n ≤ n) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (q : Fin (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n))) :
    canonicalRouterMiddleEmbedding n hn k (canonicalRouterLocalMatching n hn k mate hinv q) =
      matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k
        (canonicalRouterMiddleEmbedding n hn k q) :=
  reservoirClassLocalMatching_coordinate n _ _ _ _ k mate hinv q

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen


theorem canonicalRouterStage_record (r : Fin (canonicalRouterStride n)) :
    fieldsLen (selectiveLen (input r).p (input r).X) = n :=
  routerProfileFieldsLen n (canonicalRouterStride n) (canonicalRouterGap n) hn r

theorem canonicalRouterStage_bits (r : Fin (canonicalRouterStride n))
    (i : Fin ((input r).R * 2 ^ fieldsLen (selectiveLen (input r).p (input r).X))) :
    (fun q : Fin n => ((input r).perm i).val.testBit q.val) =
      shear ((placedSelectiveTargets (input r).p (input r).X (input r).hK
        (profileActive (input r).p (input r).hK (input r).targets)
        (reservoirPlacement (fieldsLen (selectiveLen (input r).p (input r).X))
          (input r).Hslot (input r).hplacementFit (input r).p.wc (input r).hslotWidth (input r).reservoir)).image
        (Fin.cast (canonicalRouterStage_record n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r)))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
        (fun q => i.val.testBit q.val) := by
  have data := canonicalRouterStage_data n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  exact (input r).originalMatching_perm_shear_cast n
    (canonicalRouterStage_record n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r)
    rfl data.hsize (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
    mate hinv data.hsource reverse data.htargets i


theorem canonicalRouterStage_bulk_bits (r : Fin (canonicalRouterStride n))
    (i : Fin ((input r).R * 2 ^ fieldsLen (selectiveLen (input r).p (input r).X))) :
    (fun q : Fin n => ((input r).perm i).val.testBit q.val) =
      shear (((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).filter
          (fun q => q.val % canonicalRouterStride n = r.val)).image (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
        (fun q => i.val.testBit q.val) := by
  rw [canonicalRouterStage_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r i]
  congr 1
  exact routerPlacedLocalTargets_cast n (canonicalRouterStride n) (canonicalRouterGap n)
    (by have := canonicalRouterGap_pos n; unfold canonicalRouterStride; omega) hn r
    (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)
    (routingReservoirWidth n (canonicalRouterGap n)) _
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k


theorem canonicalRouterBulk_source :
    ∀ i ∈ (routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
      (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
        (canonicalRouterMiddleEmbedding n hn k),
      matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k i ∉
      (routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
          (canonicalRouterMiddleEmbedding n hn k) := by
  intro i hi hs
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨q', hq', he⟩ := Finset.mem_image.mp hs
  have heq : q' = canonicalRouterLocalMatching n hn k mate hinv q :=
    canonicalRouterMiddleEmbedding_injective n hn k
      (he.trans (canonicalRouterMiddleEmbedding_source n hn k mate hinv q).symm)
  exact matchingDirectionTargets_source (canonicalRouterLocalMatching n hn k mate hinv)
    (canonicalRouterLocalMatching_involutive n hn k mate hinv) reverse q
    (Finset.mem_filter.mp hq).1 (heq ▸ (Finset.mem_filter.mp hq').1)


/-- All normalized physical bulk residue shears compose to one bulk shear. -/
theorem canonicalRouterBulk_shears_of_order (stages : List (Fin (canonicalRouterStride n)))
    (hnodup : stages.Nodup) (hcover : ∀ r, r ∈ stages) (x : Fin n → Bool) :
    stages.foldr
      (fun r y => shear (((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).filter
          (fun q => q.val % canonicalRouterStride n = r.val)).image (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) y) x =
      shear ((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
          (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) x := by
  have hstride : 0 < canonicalRouterStride n := by
    have := canonicalRouterGap_pos n
    unfold canonicalRouterStride
    omega
  have h := partitionShears_image
    (routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
      (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse))
    (canonicalRouterMiddleEmbedding n hn k) (canonicalRouterMiddleEmbedding_injective n hn k)
    (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
    (fun q => (⟨q.val % canonicalRouterStride n, Nat.mod_lt _ hstride⟩ : Fin (canonicalRouterStride n)))
    ⟨0, hstride⟩ (canonicalRouterBulk_source n hn mate hinv k reverse)
    stages hnodup x
  simpa only [Fin.ext_iff, hcover, Finset.filter_true] using h


theorem canonicalRouterBulk_shears (x : Fin n → Bool) :
    (List.finRange (canonicalRouterStride n)).foldr
      (fun r y => shear (((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).filter
          (fun q => q.val % canonicalRouterStride n = r.val)).image (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) y) x =
      shear ((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
          (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) x := by
  exact canonicalRouterBulk_shears_of_order n hn mate hinv k reverse
    (List.finRange (canonicalRouterStride n)) (List.nodup_finRange _) (fun r => List.mem_finRange r) x


def canonicalRouterStagePerm (r : Fin (canonicalRouterStride n)) : Equiv.Perm (Fin (R * 2 ^ n)) :=
  castRankPerm (canonicalRouterStage_data n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r).count
    (input r).perm

theorem canonicalRouterStagePerm_bits (r : Fin (canonicalRouterStride n)) (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r i).val.testBit q.val) =
      shear (((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).filter
          (fun q => q.val % canonicalRouterStride n = r.val)).image (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
        (fun q => i.val.testBit q.val) := by
  have h := canonicalRouterStage_bulk_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
    (Fin.cast (canonicalRouterStage_data n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r).count.symm i)
  simpa only [canonicalRouterStagePerm, castRankPerm_apply_val, Fin.val_cast] using h


theorem canonicalRouterStages_foldr_bits (stages : List (Fin (canonicalRouterStride n)))
    (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (stages.foldr (fun r j => canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j) i).val.testBit q.val) =
      stages.foldr (fun r y => shear (((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).filter
          (fun q => q.val % canonicalRouterStride n = r.val)).image (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) y) (fun q => i.val.testBit q.val) := by
  induction stages with
  | nil => rfl
  | cons r stages ih =>
    simp only [List.foldr_cons]
    rw [canonicalRouterStagePerm_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r, ih]

theorem canonicalRouterBulk_foldr_bits (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => ((List.finRange (canonicalRouterStride n)).foldr
      (fun r j => canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j) i).val.testBit q.val) =
      shear ((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
          (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) (fun q => i.val.testBit q.val) := by
  rw [canonicalRouterStages_foldr_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen,
    canonicalRouterBulk_shears n hn mate hinv k reverse]

theorem canonicalRouterBulk_foldl_bits (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => ((List.finRange (canonicalRouterStride n)).foldl
      (fun j r => canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j) i).val.testBit q.val) =
      shear ((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
          (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) (fun q => i.val.testBit q.val) := by
  rw [List.foldl_eq_foldr_reverse]
  rw [canonicalRouterStages_foldr_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen]
  exact canonicalRouterBulk_shears_of_order n hn mate hinv k reverse
    (List.finRange (canonicalRouterStride n)).reverse
    (by simpa using List.nodup_finRange (canonicalRouterStride n)) (by intro r; simp) _


def canonicalRouterSchedulePerm (stages : List (Fin (canonicalRouterStride n))) :
    Equiv.Perm (Fin (R * 2 ^ n)) :=
  stages.foldr (fun r π => (canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r).trans π) (Equiv.refl _)

theorem canonicalRouterSchedulePerm_apply (stages : List (Fin (canonicalRouterStride n)))
    (i : Fin (R * 2 ^ n)) :
    canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages i =
      stages.foldl (fun j r => canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j) i := by
  induction stages generalizing i with
  | nil => rfl
  | cons r stages ih =>
    exact ih (canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r i)

theorem canonicalRouterSchedule_records (stages : List (Fin (canonicalRouterStride n))) :
    delimitedScheduleEffect (fun r => repairStreamEffect (canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r) B) stages l.flatten =
      (moveRecs (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten :=
  repairStreamEffects_moveRecs _ stages l hl (fun row hr => (hlen row hr).1)

theorem canonicalRouterSchedulePerm_bulk_bits (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
      (List.finRange (canonicalRouterStride n)) i).val.testBit q.val) =
      shear ((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
        (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
          (canonicalRouterMiddleEmbedding n hn k))
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) (fun q => i.val.testBit q.val) := by
  simp only [canonicalRouterSchedulePerm_apply]
  exact canonicalRouterBulk_foldl_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen i

end
end IntegerMultBounds.MathlibTM2.Routing
