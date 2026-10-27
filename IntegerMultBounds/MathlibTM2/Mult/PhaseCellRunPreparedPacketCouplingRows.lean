module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketSpatialCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePrefixInPlace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def runPreparedPacketCouplingRows (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (ucopy 97 143 104) (.seq (packetSpatialCouplingRowLoop hQ)
    (.seq restoreSpatialCouplingCursor (.seq (reversePrefixInPlace 97 104 94 113 115 105 106 108 109) (uclear 107))))

def runPreparedPacketCouplingRowsCost (P q w s t u band : ℕ) : ℕ :=
  packetSpatialCouplingRowLoopCost P q w s t u band s+32*s*w+34*s+28+transferCountedLineCost s w

def runPreparedPacketGuardedCost (boundary : Bool) (P q w s t u band a b : ℕ) : ℕ :=
  packetSpatialGuardedLoopCost boundary P q w s t u band a b s+32*s*w+34*s+28+transferCountedLineCost s w

theorem runPreparedPacketGuardedCost_le (boundary : Bool) (P q w s t u band a b : ℕ) :
    runPreparedPacketGuardedCost boundary P q w s t u band a b ≤ runPreparedPacketCouplingRowsCost P q w s t u band := by
  have h := packetSpatialGuardedLoopCost_le boundary P q w s t u band a b s
  dsimp [runPreparedPacketGuardedCost,runPreparedPacketCouplingRowsCost]
  omega

theorem runPreparedPacketCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hbS : b ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail packetTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hmask : S.R 136 = couplingGuardSymbols boundary A s t band a b++maskTail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band 0++packetTail)
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runPreparedPacketGuardedCost boundary P q w s t u band a b ∧
      Exec (body) (runPreparedPacketCouplingRows hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band s++packetTail)) 93 rhsTail)
          113 (cstream A w (couplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body)
    (show (97 : Fin 144) ≠ 143 by decide) (show (97 : Fin 144) ≠ 104 by decide)
    (show (143 : Fin 144) ≠ 104 by decide) v S (hready.fresh 104 (by simp))
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 143 (List.replicate s tick)}
  have he₁' : Exec (body) (ucopy 97 143 104) (mk v S) (4*s+4) (mk v₁ S₁) := by
    simpa [S₁,hs,h143] using he₁
  have hready₁ : CouplingReady P q w s t u band a b raw (embStk groupReg S₁) := by
    rw [show embStk groupReg S₁ = embStk groupReg S from groupProject_updateR S 143 _ (by decide)]
    exact hready
  have htake : (couplingGuardSymbols boundary A s t band a b).take s = couplingGuardSymbols boundary A s t band a b :=
    List.take_of_length_le (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packetSpatialCouplingRowLoop_exec (body := body) hQ boundary hA hw5 hqw
    hst hbS hP C rhs (by omega) tail packetTail maskTail rhsTail raw v₁ S₁ hready₁
    (by simpa [S₁] using hsource) (by simpa [S₁] using hpacket) (by simpa [S₁,hlen,htake] using hmask) (by simpa [S₁] using hindex)
    (by simpa [S₁] using hrhs) (by simp [S₁,hlen])
    (by simpa only [hlen] using hxs) (by simpa only [hlen] using has)
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let source := cyclicPaddedLine F band
  let ys := couplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S₁.R 136 maskTail) 135
    (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band s++packetTail))
    93 rhsTail) 107 (List.replicate s tick)) 113 (cstream A w ys.reverse++S₁.R 113)) 143 [])
    141 (cstream A w (source.drop s)++tail))
    142 ((cstream A w (source.take s)).reverse++S.R 142))}
  have he₂' : Exec (body) (packetSpatialCouplingRowLoop hQ) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,ys,hlen,S₁,hindex,source,F] using he₂
  obtain ⟨vR,mR,huR,hmR,heR⟩ := restoreSpatialCouplingCursor_at (body := body) F band s w (by omega)
    tail (S.R 142) v₂ S₂ (by simp [S₂]) (by simpa [S₂,S₁] using hwS)
    (by simp [S₂,source]) (by simp [S₂,source])
    (by simpa [S₂,S₁] using (show S.R 109 = [] from hready.fresh 109 (by simp)))
    (by simpa [S₂,S₁] using (show S.R 104 = [] from hready.fresh 104 (by simp)))
    (by simpa [S₂,S₁] using (show S.R 105 = [] from hready.fresh 105 (by simp)))
  let SR : Stacks 144 A := {S₂ with R := (Function.update (Function.update S₂.R 142 (S.R 142))
    141 (cstream A w source++tail))}
  have hys : ys.length = s := by simp [ys,hlen]
  have hfresh : ∀ k ∈ [(104 : Fin 144),115,105,106,108,109], SR.R k = [] := by
    intro k hk
    have hlow : k.val < 117 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hn136 : k ≠ 136 := by intro he; subst k; norm_num at hlow
    have hn135 : k ≠ 135 := by intro he; subst k; norm_num at hlow
    have hn141 : k ≠ 141 := by intro he; subst k; norm_num at hlow
    have hn142 : k ≠ 142 := by intro he; subst k; norm_num at hlow
    let r : Fin 117 := ⟨k.val,hlow⟩
    have hne : k ≠ 93 ∧ k ≠ 107 ∧ k ≠ 113 ∧ k ≠ 143 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hr : r ∈ [(92 : Fin 117),96,102,104,105,106,108,109,115,116] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [r,Fin.ext_iff]
    have hh := hready.fresh r hr
    have hmap : groupReg r = k := by
      apply Fin.ext
      simp [groupReg,r]
    change S.R (groupReg r) = [] at hh
    rw [hmap] at hh
    simpa [SR,S₂,S₁,hn136,hn135,hn141,hn142,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using hh
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := reversePrefixInPlace_exec (body := body)
    (records := 97) (recordSaved := 104) (width := 94) (src := 113) (dst := 115)
    (saved := 105) (buf := 106) (tmp := 108) (count := 109) (by decide)
    w ys.reverse (S.R 113) vR SR
    (by simp [SR,S₂,S₁,hs,hys]) (by simpa [SR,S₂,S₁] using hwS) (by simp [SR,S₂,S₁]) hfresh
  let S₃ : Stacks 144 A := {SR with R := Function.update SR.R 113 (cstream A w ys++S.R 113)}
  have he₃' : Exec (body) (reversePrefixInPlace 97 104 94 113 115 105 106 108 109)
      (mk vR SR) m₃ (mk v₃ S₃) := by simpa [S₃] using he₃
  have h107₃ : S₃.R 107 = List.replicate s tick := by simp [S₃,SR,S₂]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 107 v₃ S₃
  refine ⟨v₄,(4*s+4)+(m₂+(mR+(m₃+(2*s+2)))),hu₄.trans (hu₃.trans (huR.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq heR (Exec.seq he₃' he₄)))).cast (by rw [h107₃]; simp) ?_⟩
  · have hm₂g : m₂ ≤ packetSpatialGuardedLoopCost boundary P q w s t u band a b s := by simpa [hlen] using hm₂
    have hm₃' : m₃ ≤ 32*s*w+28*s+22 := by simpa [hys] using hm₃
    dsimp only [runPreparedPacketGuardedCost]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h107 : k = 107 <;> by_cases h143' : k = 143 <;> by_cases h113 : k = 113 <;>
      by_cases h136 : k = 136 <;> by_cases h135 : k = 135 <;> by_cases h141 : k = 141 <;> by_cases h142 : k = 142 <;>
      simp [S₃,SR,S₂,S₁,h107,h143',h113,h136,h135,h141,h142,hindex,h143,ys,hsource,source,F,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
