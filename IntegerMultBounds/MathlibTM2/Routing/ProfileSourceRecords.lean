module

public import IntegerMultBounds.MathlibTM2.Routing.ProfileCompiler
public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceEncoding

/-! Canonical raw records for logical bulk profiles. The local-coordinate
encoding reconstructs exactly the original physical Y source coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

theorem sourceOfY_wire (p : Par) (hK : 0 < p.K) (X : ℕ) (q : Fin p.wy) :
    (sourceWire p X (sourceOfY p hK q)).val = q.val := by
  unfold sourceOfY
  split_ifs with hlo hmid
  · simp [sourceWire]
  · simp only [sourceWire]
    have hd := Nat.mod_add_div (q.val - p.ρ) p.K
    have hq : p.ρ ≤ q.val := by omega
    rw [Nat.mul_comm] at hd
    omega
  · simp only [sourceWire]
    omega

def profileSourceRecords (p : Par) (hK : 0 < p.K) (X : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (Li Lk : ℕ) : List (Fin (A + 4)) :=
  gatedSelectedSourceWords Li Lk (List.ofFn (fun c =>
    (profileSources (X := X) p hK targets source c).gatedChoice (profileActive p hK targets c)))

theorem profileSourceRecords_length (p : Par) (hK : 0 < p.K) (X : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (Li Lk : ℕ) :
    (profileSourceRecords (A := A) p hK X targets source Li Lk).length =
      p.n * (Li + (Li + Lk) + 5) := by
  simp [profileSourceRecords, gatedSelectedSourceWords_length]

theorem profileSourceChoice_position (p : Par) (hK : 0 < p.K) (X : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (c : Fin p.n) :
    ((profileSources (X := X) p hK targets source c).gatedChoice
      (profileActive p hK targets c)).position p.K (SlotSource.regionBase p) =
      (profileSourceCoordinate p hK targets source c).val := by
  rw [SlotSource.gatedChoice_position]
  exact sourceOfY_wire p hK X _

theorem profileSourceChoice_active_position (p : Par) (hK : 0 < p.K) (X : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (c : Fin p.n)
    (hc : profileActive p hK targets c = true) :
    ((profileSources (X := X) p hK targets source c).gatedChoice true).position
      p.K (SlotSource.regionBase p) = (source (profileTarget p hK c)).val := by
  have ht : profileTarget p hK c ∈ targets := by simpa [profileActive] using hc
  rw [← hc, profileSourceChoice_position]
  simp [profileSourceCoordinate, ht]

end
end IntegerMultBounds.MathlibTM2.Routing
