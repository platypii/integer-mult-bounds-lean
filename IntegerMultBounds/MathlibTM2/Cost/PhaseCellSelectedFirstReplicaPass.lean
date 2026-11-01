module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaCouplingFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaCouplingRowsResources

/-! The executed first pass reuses the initialized interior and active-row
coupling estimates. Shared setup and native traffic stay in one explicit ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem firstReplicaPassTime_split {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    firstReplicaPassTime H = initializedReplicaCouplingRowsTime H+releasedReplicaCouplingCost H := by
  unfold firstReplicaPassTime initializedReplicaCouplingRowsTime realInitializedReplicaHaloTime initializedReplicaHaloTime
  rfl

def firstReplicaPassNativeTime {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (cV : ℕ) : ℕ :=
  initializedReplicaHaloSharedTime H+18+H.Fs.length*(38*(H.span*H.wordWidth)+37)+
    (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+
    releasedReplicaCouplingNativeTime H+H.Fs.length*(H.span*(20*H.wordWidth+26)+2)

theorem selectedFirstReplicaPass_fast_le (ct ce : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    let cV := (2*cw+426009)*cw
    ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ firstReplicaPassTime H →
      (steps : ℝ) ≤ firstReplicaPassNativeTime H cV+
        (D*(replicaHaloLocalCoordinates H : ℕ)+
          E*(retainedCouplingActiveRows false (Sizes.s n i) H.t H.band H.origin (H.origin+H.span) H.origin H.span)*
            ((H.band+1 : ℕ) : ℝ))*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ) := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  obtain ⟨D,hD,hrows⟩ := selectedInitializedReplicaCouplingRows_fast_le ct ce
  obtain ⟨E,hE,hcoupling⟩ := releasedReplicaCoupling_fast_le cw
  refine ⟨D,E,hD,hE,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hn
  have hr := hrows h i H hp ht hl hu htarget hrhs (initializedReplicaCouplingRowsTime H) (le_refl _)
  obtain ⟨_,_,hw,_⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by
    simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hc := hcoupling H hwH
  have hs : (steps : ℝ) ≤ (initializedReplicaCouplingRowsTime H : ℝ)+releasedReplicaCouplingCost H := by
    rw [firstReplicaPassTime_split] at hn
    exact_mod_cast hn
  unfold firstReplicaPassNativeTime
  push_cast at hr hc hs ⊢
  nlinarith only [hr,hc,hs]

end IntegerMultBounds.MathlibTM2.Cost
