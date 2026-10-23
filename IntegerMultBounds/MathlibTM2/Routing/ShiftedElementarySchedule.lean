module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySchedule

/-! Elementary rank schedules in a target field above arbitrary low borrowed bits.
The existing executed elementary permutations are used without extracting the field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

/-- Low bits, one target field and the unchanged upper row determine a rank. -/
theorem eq_of_shifted_bits (B W i j : ℕ)
    (hlow : ∀ q : Fin B, i.testBit q.val = j.testBit q.val)
    (hfield : (fun q : Fin W => i.testBit (B + q.val)) =
      (fun q : Fin W => j.testBit (B + q.val)))
    (hrow : i / 2 ^ (B + W) = j / 2 ^ (B + W)) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hlo : q < B
  · exact hlow ⟨q, hlo⟩
  · by_cases hmid : q < B + W
    · have h := congrFun hfield ⟨q - B, by omega⟩
      simpa only [Nat.add_sub_of_le (by omega : B ≤ q)] using h
    · have h := congrArg (fun x : ℕ => x.testBit (q - (B + W))) hrow
      simp only [Nat.testBit_div_two_pow] at h
      simpa only [Nat.sub_add_cancel (by omega : B + W ≤ q)] using h

variable {W : ℕ}

def shiftedCoordinate (B : ℕ) (q : Fin W) : Fin (B + W) :=
  ⟨B + q.val, by omega⟩

theorem shiftedCoordinate_injective (B : ℕ) : Function.Injective (shiftedCoordinate (W := W) B) := by
  intro q t h
  apply Fin.ext
  have he := congrArg Fin.val h
  change B + q.val = B + t.val at he
  omega

@[simp] theorem shiftedCoordinate_mem_image (B : ℕ) (targets : Finset (Fin W)) (q : Fin W) :
    shiftedCoordinate B q ∈ targets.image (shiftedCoordinate B) ↔ q ∈ targets := by
  simp only [Finset.mem_image, (shiftedCoordinate_injective B).eq_iff, exists_eq_right]

def shiftedSource (B : ℕ) (source : Fin W → Fin W) (q : Fin (B + W)) : Fin (B + W) :=
  if h : B ≤ q.val then shiftedCoordinate B (source ⟨q.val - B, by omega⟩) else q

@[simp] theorem shiftedSource_coordinate (B : ℕ) (source : Fin W → Fin W) (q : Fin W) :
    shiftedSource B source (shiftedCoordinate B q) = shiftedCoordinate B (source q) := by
  unfold shiftedSource
  simp only [shiftedCoordinate, Nat.le_add_right, dite_true, Nat.add_sub_cancel_left]

theorem shiftedSource_allowed (B : ℕ) (targets : Finset (Fin W)) (source : Fin W → Fin W)
    (hsource : ∀ q ∈ targets, source q ∉ targets) :
    ∀ q ∈ targets.image (shiftedCoordinate B),
      shiftedSource B source q ∉ targets.image (shiftedCoordinate B) := by
  intro q hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
  simpa only [shiftedSource_coordinate, shiftedCoordinate_mem_image] using hsource t ht

noncomputable def shiftedElementaryRankSchedule (B R : ℕ) (targets : Finset (Fin W))
    (source : Fin W → Fin W) : Equiv.Perm (Fin (R * 2 ^ (B + W))) :=
  elementaryRankSchedule R (shiftedSource B source) (targets.image (shiftedCoordinate B)).toList

/-- The target field has the exact local shear action at its physical offset. -/
theorem shiftedElementaryRankSchedule_bits (B R : ℕ) (targets : Finset (Fin W))
    (source : Fin W → Fin W) (hsource : ∀ q ∈ targets, source q ∉ targets)
    (i : Fin (R * 2 ^ (B + W))) :
    (fun q : Fin W => (shiftedElementaryRankSchedule B R targets source i).val.testBit (B + q.val)) =
      shear targets source (fun q => i.val.testBit (B + q.val)) := by
  funext q
  have h := congrFun (elementaryRankSchedule_shear R (targets.image (shiftedCoordinate B))
    (shiftedSource B source) (shiftedSource_allowed B targets source hsource) i) (shiftedCoordinate B q)
  simp only [shear, toggle, shiftedCoordinate_mem_image, shiftedSource_coordinate] at h
  exact h

/-- Low borrowed bits are spectators of every terminal elementary call. -/
theorem shiftedElementaryRankSchedule_low (B R : ℕ) (targets : Finset (Fin W))
    (source : Fin W → Fin W) (hsource : ∀ q ∈ targets, source q ∉ targets)
    (i : Fin (R * 2 ^ (B + W))) (q : Fin B) :
    (shiftedElementaryRankSchedule B R targets source i).val.testBit q.val = i.val.testBit q.val := by
  let q' : Fin (B + W) := ⟨q.val, by omega⟩
  have h := congrFun (elementaryRankSchedule_shear R (targets.image (shiftedCoordinate B))
    (shiftedSource B source) (shiftedSource_allowed B targets source hsource) i) q'
  have hout : q' ∉ targets.image (shiftedCoordinate B) := by
    intro he
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp he
    have hv := congrArg Fin.val ht
    change B + t.val = q.val at hv
    omega
  simpa only [shiftedElementaryRankSchedule, shear, toggle, hout, ite_false, q'] using h

/-- Every upper row, including the high borrowed fields, is restored. -/
theorem shiftedElementaryRankSchedule_row (B R : ℕ) (targets : Finset (Fin W))
    (source : Fin W → Fin W) (i : Fin (R * 2 ^ (B + W))) :
    (shiftedElementaryRankSchedule B R targets source i).val / 2 ^ (B + W) =
      i.val / 2 ^ (B + W) :=
  elementaryRankSchedule_row R (shiftedSource B source) _ i

end IntegerMultBounds.MathlibTM2.Routing
