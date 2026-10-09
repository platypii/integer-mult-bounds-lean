import IntegerMultBounds.Compact.Layout

/-! Concrete existing-axis reservations from compact-control-layout.tex.
The two front fields and back field fit without adding address coordinates. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationCapacity

def chunks (bits K : ℕ) := (bits+K-1)/K
def capacity (d G : ℕ) := d*G
def frontChunks (d G K : ℕ) := chunks (2*capacity d G) K
def backChunks (d G K : ℕ) := chunks (capacity d G) K
def frontSlack (d G K : ℕ) := frontChunks d G K*K-2*capacity d G
def backSlack (d G K : ℕ) := backChunks d G K*K-capacity d G

theorem capacities (d G K : ℕ) (hK : 0 < K) :
    2*capacity d G ≤ frontChunks d G K*K ∧
    capacity d G ≤ backChunks d G K*K := by
  exact ⟨(Compact.Layout.ceiling_chunks (2*capacity d G) K hK).1,
    (Compact.Layout.ceiling_chunks (capacity d G) K hK).1⟩

theorem slack_small (d G K : ℕ) (hK : 0 < K) :
    frontSlack d G K < K ∧ backSlack d G K < K := by
  have hf := Compact.Layout.ceiling_chunks (2*capacity d G) K hK
  have hb := Compact.Layout.ceiling_chunks (capacity d G) K hK
  change 2*capacity d G ≤ frontChunks d G K*K ∧
    frontChunks d G K*K < 2*capacity d G+K at hf
  change capacity d G ≤ backChunks d G K*K ∧
    backChunks d G K*K < capacity d G+K at hb
  unfold frontSlack backSlack
  omega

theorem front_exact (d G K : ℕ) (hK : 0 < K) :
    2*capacity d G+frontSlack d G K = frontChunks d G K*K := by
  have hf := (capacities d G K hK).1
  unfold frontSlack
  omega

theorem back_exact (d G K : ℕ) (hK : 0 < K) :
    capacity d G+backSlack d G K = backChunks d G K*K := by
  have hb := (capacities d G K hK).2
  unfold backSlack
  omega

/-- Every recursive packed call carves n*G bits from each complete H field. -/
theorem carved (n d G : ℕ) (hn : n ≤ d) : n*G ≤ capacity d G :=
  Nat.mul_le_mul_right G hn

theorem selected_slots (f d G : ℕ) (hf : f ≤ d) :
    (f-1)*G ≤ capacity d G := carved (f-1) d G (by omega)

/-- The active middle axes and every reserved axis are original coordinates. -/
theorem axes_exact (D q0 d G K : ℕ)
    (hD : q0+frontChunks d G K+backChunks d G K ≤ D) :
    q0+frontChunks d G K+(D-(q0+frontChunks d G K+backChunks d G K))+
      backChunks d G K = D := by omega

end IntegerMultBounds.Machine.CompactGadgetReservationCapacity
