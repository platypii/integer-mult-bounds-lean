module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicRuntimeReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicLoadIterate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicGeometrySeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicProducerSolve

/-! Construct the periodic producer input by executing page preparation, header
and counter setup, the ordered iterate load, and release of derived metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement

def periodicPrepareProducer {Q A : ℕ} {P U : Type} : Pr P 242 Q A U :=
  .seq (.seq (generateWordWidth 119 130 135)
      (embProg (Fin.castLE (by decide : 168 ≤ 242)) Empty.elim sharedCouplingCoefficientInterval))
    (.seq (.seq (embProg (Fin.castLE (by decide : 144 ≤ 242)) Empty.elim installCouplingHeaders)
        (embProg (Fin.castLE (by decide : 117 ≤ 242)) Empty.elim couplingReadiness))
      (.seq (moveRightOrdered 132 107 141) (clearWords periodicGeometryDerived)))

def periodicProducerPreparationCost (p q s t u band V : ℕ) : ℕ :=
  ((8*q+9)+sharedCouplingCoefficientIntervalCost (2^15*p) q (2*q+8) s t u band 0 s V)+
    ((installCouplingHeadersCost (2^15*p) q s t u band 0 s+
      (prepareCost q (2*q+8)+6*q+4*band+10))+((4*(s*(2*q+8))+4)+(8*V+9)))

def periodicPreparedProducerBank {A : ℕ} (p q s t u band : ℕ) [NeZero s]
    (S : Stacks 242 A) : Stacks 242 A :=
  let xs := couplingCoefficientPageInterval (2^15*p) q s t u band 0 s 0 s
  let B := periodicCouplingPageBank band (2*q+8) xs (periodicCouplingWidthBank q S)
  periodicGeometrySeed (periodicIterateBank (periodicRuntimeBank (2^15*p) q s t u band B))

theorem periodicPrepareProducer_exec {Q A p stage q l s t u band V W N : ℕ} [NeZero s]
    {P U : Type} {body : P → Pr P 242 Q A U}
    (hA : 4 ≤ A) (hp : 0 < p) (hst : s < t) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : (s+2*band)+s < 2^V)
    (C R : ZMod s → GaussianInt) (rhsTail : List (Fin (A+4)))
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : PackedHaloBetweenInputs (2^15*p) stage q l s t u band 0 s V (2*q+8) W N
      (extendStacks (by decide) S))
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s C))
    (hrhs : S.R 93 = cstream A (2*q+8) (packedInterval 0 s R)++rhsTail)
    (h160 : S.R 160 = []) :
    let F := periodicPreparedProducerBank p q s t u band S
    ∃ v' n, v'.user = v.user ∧ n ≤ periodicProducerPreparationCost p q s t u band V ∧
      Exec body periodicPrepareProducer (mk v S) n (mk v' F) ∧
      PeriodicProducerInput p q (2*q+8) t u band 0 s V C R [] rhsTail (S.R 110)
        (embStk (Fin.castLE (by decide : 168 ≤ 242)) F) ∧
      PackedPreparedBank q (2*q+8) W N F ∧
      ∀ bo hf df, PackedBoundaryFactorPages bo hf df S → PackedBoundaryFactorPages bo hf df F := by
  dsimp only
  let xs := couplingCoefficientPageInterval (2^15*p) q s t u band 0 s 0 s
  let B := periodicCouplingPageBank band (2*q+8) xs (periodicCouplingWidthBank q S)
  let K := periodicRuntimeBank (2^15*p) q s t u band B
  let L := periodicIterateBank K
  let F := periodicGeometrySeed L
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,_,_⟩ := periodicPreparedPage_exec (body := body) hA
    (by norm_num; omega) hst hwide hfitV v S h
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hready,hbank,h93,h107,h141,hframe,hpages⟩ :=
    periodicRuntimeReady_exec (body := body) xs v₁ S h
  change K.R 93 = S.R 93 at h93
  change K.R 107 = [] at h107
  change K.R 141 = [] at h141
  obtain ⟨v₃,hu₃,he₃,hreadyL,hbankL,hpagesL⟩ := periodicLoadIterate_exec (body := body)
    (S.R 110) v₂ K h107 h141 hready hbank
  have hmetadataFrame (k : Fin 242) (hk : 145 ≤ k.val) : L.R k = S.R k := by
    have hn : k.val ≠ 130 ∧ k.val ≠ 132 ∧ k.val ≠ 135 ∧ k.val ≠ 138 ∧
        k.val ≠ 139 ∧ k.val ≠ 140 ∧ k.val ≠ 141 ∧ k.val ≠ 143 := by omega
    have hload : L.R k = K.R k := by
      simp [L,periodicIterateBank,Fin.ext_iff,hn.2.1,hn.2.2.2.2.2.2.1]
    rw [hload,hframe k (by omega)]
    simp [periodicCouplingPageBank,periodicCouplingWidthBank,Fin.ext_iff,
      hn.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.2]
  have hview : embStk packedRecoveryRuntimeReg (extendStacks (by decide : 242 ≤ 248) S) = embStk e S := by
    refine Stacks.ext rfl rfl ?_ ?_
    all_goals
      funext i
      have hi := i.isLt
      simp [e,embStk,packedRecoveryRuntimeReg,extendStacks,show i.val < 242 by omega]; rfl
  have hmeta := h.headers.geometry
  rw [hview] at hmeta
  simp only [Nat.sub_zero] at hmeta
  have hmetaL : CouplingIntervalMetadata V s t band 0 s 0 s (embStk e L) := by
    apply hmeta.of_frame
    · exact hmetadataFrame 163 (by decide)
    · intro k hk
      have hr : 145 ≤ k.val := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hmetadataFrame (e k) hr
  obtain ⟨v₄,hu₄,he₄⟩ := periodicGeometrySeed_exec (body := body) v₃ L hmetaL
  have hlength : (K.R 132).length = s*(2*q+8) := by
    rw [hframe 132 (by decide)]
    simp [periodicCouplingPageBank,periodicCouplingWidthBank,hsource]
  have he₃' : Exec body (moveRightOrdered 132 107 141) (mk v₂ K)
      (4*(s*(2*q+8))+4) (mk v₃ L) := by simpa only [hlength] using he₃
  have hFframe (k : Fin 242) (hk : 117 ≤ k.val) (hnot : k ∉ periodicGeometryDerived)
      (h132 : k ≠ 132) (h141 : k ≠ 141) : F.R k = B.R k := by
    rw [show F.R k = L.R k from periodicGeometrySeed_frame L k hnot]
    simpa only [L,periodicIterateBank,Function.update_of_ne h132,Function.update_of_ne h141] using hframe k hk
  have hf (k : Fin 242) (hk : k ∈ ([130,135,138,139,140,143,158,160,166,167] : List (Fin 242))) : F.R k = B.R k := by
    have hc : ([130,135,138,139,140,143,158,160,166,167] : List (Fin 242)).all (fun k => decide
        (117 ≤ k.val ∧ k ∉ periodicGeometryDerived ∧ k ≠ 132 ∧ k ≠ 141)) = true := by decide +kernel
    obtain ⟨h117,hnot,h132,h141⟩ := of_decide_eq_true (List.all_eq_true.mp hc k hk)
    exact hFframe k h117 hnot h132 h141
  have hdata := periodicGeometrySeed_data hmetaL
  refine ⟨v₄,n₁+(n₂+((4*(s*(2*q+8))+4)+(8*V+9))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄)),?_,
    periodicGeometrySeed_bank hbankL,?_⟩
  · exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · constructor
    · change RetainedCouplingReady _ _ _ _ _ _ _ _ _ _ (embStk (Fin.castLE (by decide : 117 ≤ 242)) F)
      rw [periodicGeometrySeed_core]
      exact hreadyL
    · change F.R 141 = _
      rw [show F.R 141 = L.R 141 from periodicGeometrySeed_frame L 141 (by decide)]
      change K.R 132 = _
      rw [hframe 132 (by decide)]
      simpa [B,periodicCouplingPageBank,periodicCouplingWidthBank] using hsource
    · intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl
      · change F.R 107 = []
        simpa [F,L,periodicGeometrySeed,periodicGeometryDerived,periodicIterateBank] using h107
      · change F.R 160 = []
        rw [hf 160 (by decide)]
        simpa [B,periodicCouplingPageBank,periodicCouplingWidthBank] using h160
    · change (F.R 140).length = _
      rw [hf 140 (by decide)]; simp [B,periodicCouplingPageBank]
    · change F.R 138 = _
      rw [hf 138 (by decide)]
      have h138 : S.R 138 = [] := h.scratch 138 (by decide)
      simp [B,xs,periodicCouplingPageBank,periodicCouplingWidthBank,h138]
    · change F.R 93 = _
      rw [show F.R 93 = L.R 93 from periodicGeometrySeed_frame L 93 (by decide)]
      simpa [L,periodicIterateBank,h93] using hrhs
    · change F.R 143 = []
      rw [hf 143 (by decide)]; simp [B,periodicCouplingPageBank]
    · change F.R 166 = []
      rw [hf 166 (by decide)]
      simpa [B,periodicCouplingPageBank,periodicCouplingWidthBank,extendStacks] using h.scratch 166 (by decide)
    · change (F.R 139).length = _
      rw [hf 139 (by decide)]; simp [B,xs,periodicCouplingPageBank]
    · omega
    · omega
    · exact hband
    · exact hwide
    · simpa only [Nat.zero_add] using hfitV
    · exact hdata.1
    · exact hdata.2.1
    · intro k hk
      have hm : e k ∈ periodicGeometryDerived := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide
      exact hdata.2.2 (e k) hm
    · change F.R 158 = []
      rw [hf 158 (by decide)]
      simpa [B,periodicCouplingPageBank,periodicCouplingWidthBank,extendStacks] using h.scratch 158 (by decide)
    · change F.R 135 = []
      rw [hf 135 (by decide)]; simp [B,periodicCouplingPageBank]
    · change F.R 167 = []
      rw [hf 167 (by decide)]
      simpa [B,periodicCouplingPageBank,periodicCouplingWidthBank,extendStacks] using h.scratch 167 (by decide)
    · change (F.R 130).length = _
      rw [hf 130 (by decide)]; simp [B,periodicCouplingPageBank,periodicCouplingWidthBank]
  · intro bo hh df hpagesS
    exact periodicGeometrySeed_factorPages (hpagesL bo hh df (hpages bo hh df hpagesS))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
