module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketSpatialCouplingRowStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Counted consecutive residual/recovery rows with exact physical stream and frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def packetSpatialCouplingRowLoop (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  countedLoop 143 (packetSpatialCouplingRowStep hQ)

def packetSpatialCouplingRowLoopCost (P q w s t u band N : ℕ) : ℕ :=
  (Finset.range N).sum (fun _ => packetSpatialCouplingRowStepCost P q w s t u band+3)+2

def packetSpatialGuardedLoopCost (boundary : Bool) (P q w s t u band a b N : ℕ) : ℕ :=
  (Finset.range N).sum (fun j => packetSpatialGuardedStepCost (couplingSkipAt boundary s t band a b j) P q w s t u band+3)+2

theorem packetSpatialGuardedLoopCost_le (boundary : Bool) (P q w s t u band a b N : ℕ) :
    packetSpatialGuardedLoopCost boundary P q w s t u band a b N ≤ packetSpatialCouplingRowLoopCost P q w s t u band N := by
  unfold packetSpatialGuardedLoopCost packetSpatialCouplingRowLoopCost
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.add_le_add_right (packetSpatialGuardedStepCost_le _ P q w s t u band) 3

theorem packetSpatialCouplingRowLoop_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hbS : b ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hrows : rhs.length ≤ s)
    (tail packetTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band 0++packetTail)
    (hmask : S.R 136 = (couplingGuardSymbols boundary A s t band a b).take rhs.length++maskTail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (hcount : (S.R 143).length = rhs.length)
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packetSpatialGuardedLoopCost boundary P q w s t u band a b rhs.length ∧
      Exec (body) (packetSpatialCouplingRowLoop hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S.R 136 maskTail) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band rhs.length++packetTail))
          93 rhsTail) 107 (List.replicate rhs.length tick++S.R 107))
          113 (cstream A w (couplingRowWords P q t u band a b boundary C 0 rhs).reverse++S.R 113)) 143 [])
          141 (cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
            if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C j else 0) band).drop rhs.length)++tail))
          142 ((cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
            if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C j else 0) band).take rhs.length)).reverse++S.R 142))}) := by
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let source := cyclicPaddedLine F band
  let ys := couplingRowWords P q t u band a b boundary C 0 rhs
  let guards := (couplingGuardSymbols boundary A s t band a b).take rhs.length
  have hguards : guards.length = rhs.length := by simp [guards]; omega
  let Inv : ℕ → Stacks 144 A → Prop := fun j B =>
    B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
    (∀ k : Fin 144, k ≠ 93 → k ≠ 107 → k ≠ 113 → k ≠ 143 → k ≠ 141 → k ≠ 142 → k ≠ 135 → k ≠ 136 → B.R k = S.R k) ∧
    B.R 93 = cstream A w (rhs.drop j)++rhsTail ∧
    B.R 107 = List.replicate j tick++S.R 107 ∧
    B.R 113 = cstream A w (ys.take j).reverse++S.R 113 ∧
    B.R 141 = cstream A w (source.drop j)++tail ∧
    B.R 142 = (cstream A w (source.take j)).reverse++S.R 142 ∧
    B.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band j++packetTail ∧
    B.R 136 = guards.drop j++maskTail
  have hstable : ∀ j B cs, Inv j B → Inv j {B with R := Function.update B.R 143 cs} := by
    intro j B cs h
    rcases h with ⟨hi,ho,hl,hf,hr,hj,hy,hsrc,hsaved,hpacketB,hmaskB⟩
    exact ⟨hi,ho,hl,by intro k h93 h107 h113 h143 h141 h142 h135 h136; simpa [h143] using hf k h93 h107 h113 h143 h141 h142 h135 h136,
      by simpa using hr,by simpa using hj,by simpa using hy,by simpa using hsrc,by simpa using hsaved,by simpa using hpacketB,by simpa using hmaskB⟩
  have hstep : ∀ j < rhs.length, ∀ (vi : HS 144 Q A U) B, Inv j B →
      ∃ v' B' m, v'.user = vi.user ∧ m ≤ packetSpatialGuardedStepCost (couplingSkipAt boundary s t band a b j) P q w s t u band ∧
        Exec (body) (packetSpatialCouplingRowStep hQ) (mk vi B) m (mk v' B') ∧
        B'.R 143 = B.R 143 ∧ Inv (j+1) B' := by
    intro j hj vi B h
    rcases h with ⟨hiB,hoB,hlB,hf,hr,hjB,hyB,hsrcB,hsavedB,hpacketB,hmaskB⟩
    have hreadyB : CouplingReady P q w s t u band a b raw (embStk groupReg B) := by
      apply hready.of_frame
      · change B.L ∘ groupReg = S.L ∘ groupReg
        rw [hlB]
      · intro k h93 h107 h113
        apply hf (groupReg k)
        · exact groupReg_injective.ne h93
        · exact groupReg_injective.ne h107
        · exact groupReg_injective.ne h113
        · exact groupReg_off 143 (by decide) k
        · exact groupReg_off 141 (by decide) k
        · exact groupReg_off 142 (by decide) k
        · exact groupReg_off 135 (by decide) k
        · exact groupReg_off 136 (by decide) k
    have hindexB : (B.R 107).length = j := by simp [hjB,hindex]
    have hrhsB : B.R 93 = csyms A w rhs[j]++(cstream A w (rhs.drop (j+1))++rhsTail) := by
      rw [hr,List.drop_eq_getElem_cons hj,cstream_cons,List.append_assoc]
    have hjg : j < guards.length := by omega
    have hguardj : guards[j] = pairSym A (couplingSkipAt boundary s t band a b j) (couplingSkipAt boundary s t band a b j) := by
      simp [guards,couplingGuardSymbols]
    have hmaskj : B.R 136 = pairSym A (couplingSkipAt boundary s t band a b j) (couplingSkipAt boundary s t band a b j)::
        (guards.drop (j+1)++maskTail) := by
      rw [hmaskB,List.drop_eq_getElem_cons hjg,hguardj,List.cons_append]
    obtain ⟨v',m,hu,hm,he⟩ := packetSpatialCouplingRowStep_exec (body := body)
      hQ boundary (couplingSkipAt boundary s t band a b j) hA hw5 hqw hst (by omega) hP C tail packetTail
      (guards.drop (j+1)++maskTail) raw vi B hmaskj
      (couplingSkipAt_sound hst boundary band a b j hbS (by omega)) hreadyB hpacketB hsrcB
      rhs[j] (cstream A w (rhs.drop (j+1))++rhsTail) hrhsB (hxs j hj) (has j hj)
    let z := couplingRowWord P q t u band a b j boundary C rhs[j]
    let B' : Stacks 144 A := {B with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update B.R 136 (guards.drop (j+1)++maskTail)) 135
      (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (j+1)++packetTail))
      113 (csyms A w z++B.R 113)) 93 (cstream A w (rhs.drop (j+1))++rhsTail))
      141 (cstream A w (source.drop (j+1))++tail))
      142 ((csyms A w (F ((j : ZMod s)-(band : ZMod s)))).reverse++B.R 142)) 107 (tick::B.R 107))}
    have hylen : j < ys.length := by simpa [ys] using hj
    have hyget : ys[j] = z := by simpa [ys,z] using couplingRowWords_getElem P q t u band a b 0 boundary C rhs j hj
    have hnext : cstream A w (ys.take (j+1)).reverse = csyms A w z++cstream A w (ys.take j).reverse := by
      rw [List.take_succ_eq_append_getElem hylen,List.reverse_append,List.reverse_singleton,
        cstream_append,cstream_cons,cstream_nil,List.append_nil,hyget]
    have hsourceLen : j < source.length := by
      simp only [source,cyclicPaddedLine,List.length_map,List.length_range]
      omega
    have hsourceGet : source[j] = F ((j : ZMod s)-(band : ZMod s)) := by
      simp [source,cyclicPaddedLine]
    have hsnext : (cstream A w (source.take (j+1))).reverse =
        (csyms A w (F ((j : ZMod s)-(band : ZMod s)))).reverse ++
          (cstream A w (source.take j)).reverse := by
      rw [List.take_succ_eq_append_getElem hsourceLen,cstream_append,List.reverse_append,
        cstream_cons,cstream_nil,List.append_nil,hsourceGet]
    refine ⟨v',B',m,hu,hm,by simpa [B',z,source,F] using he,by simp [B'],hiB,hoB,hlB,?_,by simp [B'],?_,?_,?_,?_,?_,?_⟩
    · intro k h93 h107 h113 h143 h141 h142 h135 h136
      simpa [B',h93,h107,h113,h141,h142,h135,h136] using hf k h93 h107 h113 h143 h141 h142 h135 h136
    · simp [B',hjB,List.replicate_succ]
    · simp [B',hyB,hnext,List.append_assoc]
    · simp [B']
    · simp [B',hsavedB,hsnext,List.append_assoc]
    · simp [B']
    · simp [B']
  have hInv : Inv 0 S := by
    exact ⟨rfl,rfl,rfl,by intros; rfl,by simpa using hrhs,by simp,by simp,by simpa [source,F] using hsource,by simp,hpacket,by simpa [guards] using hmask⟩
  obtain ⟨v',S',m,hu,hm,he,h143,hI⟩ := countedLoop_exec_costs (body := body)
    143 (packetSpatialCouplingRowStep hQ) rhs.length
    (fun j => packetSpatialGuardedStepCost (couplingSkipAt boundary s t band a b j) P q w s t u band) Inv hstable hstep v S hcount hInv
  rcases hI with ⟨hi',ho',hl',hf,hr',hj',hy',hsrc',hsaved',hpacket',hmask'⟩
  refine ⟨v',m,hu,hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hi' ho' hl' ?_
  funext k
  by_cases h93 : k = 93
  · subst k; simpa using hr'
  by_cases h107 : k = 107
  · subst k; simpa using hj'
  by_cases h113 : k = 113
  · subst k
    have hlen : ys.length = rhs.length := by simp [ys]
    rw [← hlen,List.take_length] at hy'
    simpa [ys] using hy'
  by_cases h143' : k = 143
  · subst k; simpa using h143
  by_cases h141 : k = 141
  · subst k; simpa [source,F] using hsrc'
  by_cases h142 : k = 142
  · subst k; simpa [source,F] using hsaved'
  by_cases h135 : k = 135
  · subst k; simpa using hpacket'
  by_cases h136 : k = 136
  · subst k; simpa [← hguards] using hmask'
  simpa [h93,h107,h113,h143',h141,h142,h135,h136] using hf k h93 h107 h113 h143' h141 h142 h135 h136

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
