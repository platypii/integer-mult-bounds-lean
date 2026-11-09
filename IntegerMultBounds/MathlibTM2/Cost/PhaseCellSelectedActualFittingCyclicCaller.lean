module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFittingCyclicCaller
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicReplicaSizing

/-! The selected fitting estimate instantiated with the actual cyclic problems
and their actual joint precision. Only construction identities remain. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedActualFittingCyclicCaller_time_le (ct : ℕ) :
    let cw := 1032+8*ct
    ∃ E C : ℝ, 0 ≤ E ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] {u : ℕ} {α d : ℝ},
      ∀ axis : RecoveryAxisBounds (Sizes.s n i) (Sizes.t n i) (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) α d,
      ∀ width depth L replicas target : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      let p := Sizes.p n
      let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
      let band := PhaseCellBand.width p u
      let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
      let origin := fun k => coreStart width k-depth*band
      let N := fun k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band (origin k) L).card
      let stage := fun k => initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (N k)) 2
      let q := fun k => executionPrecision p l (stage k) 2
      0 < width → width ≤ Sizes.s n i → depth*band ≤ width →
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width → p^2+band^2 ≤ width →
      ∀ H K : ℕ → ReplicaHaloProblem (Sizes.s n i),
      (∀ k ∈ jobs, ∃ (ha : origin k < Sizes.s n i) (hn : L ≤ Sizes.s n i)
        (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
        (hF : ∀ F ∈ Fs, ∀ j, ‖value (q k) (F j)‖ ≤ (2 : ℝ)^2),
        Fs.length = replicas ∧
        H k = axis.cyclicLeftReplicaProblem (stage k) 2 (origin k) L ha Fs hF ∧
        K k = axis.cyclicRightReplicaProblem (stage k) 2 (origin k) L hn Fs hF) →
      ((jobs.map (fun k => cachedCyclicReplicaBoundaryBill (H k) (K k) p u l (Sizes.t n i)
        (origin k) L (boundaryRecoveryTarget p (target+1)) (q k) (2*q k+8)
        (N k) (24*band+1) replicas+
        solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))).sum : ℝ) ≤
      2*(Sizes.T n : ℝ)+
      4200*replicas*(Sizes.s n i : ℝ)*(cw*Sizes.p n+1 : ℕ)+
      2800*(replicas+1)*(Sizes.s n i : ℝ)*(cw*Sizes.p n+1 : ℕ)+
      800*((30*cw+50 : ℕ)*(replicas+1)*(Sizes.p n : ℝ)+
        replicas*C*(Sizes.p n : ℝ)^(129/128 : ℝ))*
          ((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)+
      680*E*replicas*((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  dsimp only
  let cw := 1032+8*ct
  let cV := (2*(16*20+8*cw+8*2+128)+426009)*cw
  obtain ⟨E,C,hE,hC,htime⟩ := selectedFittingCyclicCaller_time_le cw 2 cw cV 20 20
  refine ⟨E,C,hE,hC,?_⟩
  filter_upwards [htime] with n ht
  intro h i _ u α d axis width depth L replicas target hu htarget
  intro hw hwidth hguard hcell hprepare H K hactual
  let p := Sizes.p n
  let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
  let band := PhaseCellBand.width p u
  let origin := fun k => coreStart width k-depth*band
  let N := fun k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band (origin k) L).card
  let stage := fun k => initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (N k)) 2
  let q := fun k => executionPrecision p l (stage k) 2
  have heq (k : ℕ) : executionWidth p l (stage k) 2 = 2*q k+8 := by
    dsimp only [q]
    unfold executionWidth executionPrecision
    omega
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have htarget' : target ≤ cw*Sizes.p n := htarget.trans
    (Nat.mul_le_mul_right _ (by dsimp only [cw]; omega))
  apply ht h i width band depth L replicas u target hu htarget' rfl axis.hband
    hw hwidth hguard (PhaseCellBand.width_pos p u) hcell hprepare H K q
  · intro k hk
    obtain ⟨ha,hn,Fs,hF,hlen,hH,hK⟩ := hactual k hk
    rw [hH,hK]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro k hk
    obtain ⟨ha,hn,Fs,hF,hlen,hH,hK⟩ := hactual k hk
    obtain ⟨hl,hr,hs,hw,hV⟩ := selectedCyclicReplicaSizing ct h i u target
      (origin k) L hu htarget axis.hband
    change stage k ≤ cw*p at hs
    change executionWidth p l (stage k) 2 ≤ cw*p at hw
    change weightWorkspaceWidth (2^15*p) (q k) (executionWidth p l (stage k) 2)
      (Sizes.t n i) u ≤ cV*p at hV
    rw [hH,hK]
    exact ⟨rfl,rfl,hu,hu,hs,hs,by change 2 ≤ 2*p; omega,by change 2 ≤ 2*p; omega,
      hlen,hlen,heq k,heq k,by rwa [←heq k],hV,hV⟩
  · intro k hk R hR
    obtain ⟨ha,hn,Fs,hF,hlen,hH,hK⟩ := hactual k hk
    have hprofile := selectedCyclicReplicaProblems_profile ct h i axis target (origin k) L ha hn hu htarget Fs hF
    rw [hH,hK] at hR
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hl,hr⟩ := hprofile R hR
    exact ⟨hl,hr⟩

end IntegerMultBounds.MathlibTM2.Cost
