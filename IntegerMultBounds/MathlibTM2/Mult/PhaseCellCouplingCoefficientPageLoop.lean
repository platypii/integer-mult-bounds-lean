module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Counted generation of a complete sparse coefficient page and its actual word count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingCoefficientPageLoop : Pr P₀ 144 Q A U := countedLoop 143 couplingCoefficientPageStep

def couplingCoefficientPageLoopCost (P q w s t u band a b N : ℕ) : ℕ :=
  (Finset.range N).sum (fun i =>
    couplingCoefficientPageRowCost (couplingSkipAt true s t band a b i) P q w s t u band+4)+2

def couplingCoefficientPageIntervalLoopCost (P q w s t u band a b origin N : ℕ) : ℕ :=
  (Finset.range N).sum (fun j =>
    couplingCoefficientPageRowCost (couplingSkipAt true s t band a b (origin+j)) P q w s t u band+4)+2

theorem couplingCoefficientPageIntervalLoop_exec {P q w s t u band a b origin N : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (hN : origin+N ≤ s)
    (raw packetTail maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1) (hcount : (S.R 143).length = N)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band origin++packetTail)
    (hmask : S.R 136 = ((couplingGuardSymbols true A s t band a b).drop origin).take N++maskTail) :
    let xs := couplingCoefficientPageInterval P q s t u band a b origin N
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingCoefficientPageIntervalLoopCost P q w s t u band a b origin N ∧
      Exec body couplingCoefficientPageLoop (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          135 (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (origin+N)++packetTail))
          136 maskTail) 137 ((cstream A w xs).reverse++S.R 137))
          139 (List.replicate xs.length tick++S.R 139)) 143 [])}) := by
  dsimp only
  let page := couplingCoefficientPageInterval P q s t u band a b origin
  let guards := ((couplingGuardSymbols true A s t band a b).drop origin).take N
  have hguards : guards.length = N := by simp [guards]; omega
  let Inv : ℕ → Stacks 144 A → Prop := fun j B =>
    B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
    (∀ k : Fin 144, k ≠ 135 → k ≠ 136 → k ≠ 137 → k ≠ 139 → k ≠ 143 → B.R k = S.R k) ∧
    B.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (origin+j)++packetTail ∧
    B.R 136 = guards.drop j++maskTail ∧
    B.R 137 = (cstream A w (page j)).reverse++S.R 137 ∧
    B.R 139 = List.replicate (page j).length tick++S.R 139
  have hstable : ∀ j B cs, Inv j B → Inv j {B with R := Function.update B.R 143 cs} := by
    intro j B cs ⟨hi,ho,hl,hf,hpacketB,hmaskB,hpageB,hwordsB⟩
    exact ⟨hi,ho,hl,by intro k h135 h136 h137 h139 h143; simpa [h143] using hf k h135 h136 h137 h139 h143,
      by simpa using hpacketB,by simpa using hmaskB,by simpa using hpageB,by simpa using hwordsB⟩
  have hstep : ∀ j < N, ∀ (vi : HS 144 Q A U) B, Inv j B →
      ∃ v' B' m, v'.user = vi.user ∧
        m ≤ couplingCoefficientPageRowCost (couplingSkipAt true s t band a b (origin+j)) P q w s t u band+1 ∧
        Exec body couplingCoefficientPageStep (mk vi B) m (mk v' B') ∧
        B'.R 143 = B.R 143 ∧ Inv (j+1) B' := by
    intro j hj vi B ⟨hiB,hoB,hlB,hf,hpacketB,hmaskB,hpageB,hwordsB⟩
    have hview : embStk groupReg B = embStk groupReg S := by
      refine Stacks.ext hiB hoB ?_ ?_
      · funext k; exact congrFun hlB (groupReg k)
      · funext k
        apply hf (groupReg k)
        all_goals exact groupReg_off _ (by decide) k
    have hreadyB : CouplingReady P q w s t u band a b raw (embStk groupReg B) := by rw [hview]; exact hready
    have hrowsB : (B.R 140).length = 2*band+1 := by rw [hf 140 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hrows
    have hjg : j < guards.length := by omega
    have hguardj : guards[j] = pairSym A (couplingSkipAt true s t band a b (origin+j)) (couplingSkipAt true s t band a b (origin+j)) := by
      simp [guards,couplingGuardSymbols,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    have hmaskj : B.R 136 = pairSym A (couplingSkipAt true s t band a b (origin+j)) (couplingSkipAt true s t band a b (origin+j))::
        (guards.drop (j+1)++maskTail) := by rw [hmaskB,List.drop_eq_getElem_cons hjg,hguardj,List.cons_append]
    obtain ⟨v',m,hu,hm,he⟩ := couplingCoefficientPageStep_exec (body := body)
      hA hst hP (by omega) raw packetTail (guards.drop (j+1)++maskTail) vi B hreadyB hrowsB hpacketB hmaskj
    let chunk := couplingCoefficientPageChunk P q s t u band a b (origin+j)
    let B' : Stacks 144 A := {B with R := (Function.update (Function.update (Function.update (Function.update B.R
      136 (guards.drop (j+1)++maskTail)) 135
      (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (origin+(j+1))++packetTail))
      137 ((cstream A w chunk).reverse++B.R 137)) 139 (List.replicate chunk.length tick++B.R 139))}
    refine ⟨v',B',m,hu,hm,he,by simp [B'],hiB,hoB,hlB,?_,by simp [B'],by simp [B'],?_,?_⟩
    · intro k h135 h136 h137 h139 h143
      simpa [B',h135,h136,h137,h139] using hf k h135 h136 h137 h139 h143
    · simp [B',page,couplingCoefficientPageInterval_succ,cstream_append,List.reverse_append,hpageB,List.append_assoc,chunk]
    · change List.replicate chunk.length tick++B.R 139 = List.replicate (page (j+1)).length tick++S.R 139
      rw [hwordsB]
      change List.replicate chunk.length tick++(List.replicate (page j).length tick++S.R 139) = _
      rw [← List.append_assoc,← List.replicate_add]
      congr 2
      simp [page,couplingCoefficientPageInterval_succ,chunk,Nat.add_comm]
  have hinit : Inv 0 S := by
    refine ⟨rfl,rfl,rfl,by intros; rfl,hpacket,?_,?_,?_⟩
    · simpa [guards] using hmask
    · simp [page]
    · simp [page]
  obtain ⟨v',B,m,hu,hm,he,hc,hi⟩ := countedLoop_exec_costs (body := body) 143 couplingCoefficientPageStep N
    (fun j => couplingCoefficientPageRowCost (couplingSkipAt true s t band a b (origin+j)) P q w s t u band+1)
    Inv hstable hstep v S hcount hinit
  rcases hi with ⟨hi,ho,hl,hf,hp,hg,hpage,hwords⟩
  refine ⟨v',m,hu,by simpa [couplingCoefficientPageIntervalLoopCost,Nat.add_assoc] using hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hi ho hl ?_
  funext k
  by_cases h135 : k = 135
  · subst k; simpa using hp
  by_cases h136 : k = 136
  · subst k; rw [← hguards,List.drop_length,List.nil_append] at hg; simpa using hg
  by_cases h137 : k = 137
  · subst k; simpa [page] using hpage
  by_cases h139 : k = 139
  · subst k; simpa [page] using hwords
  by_cases h143 : k = 143
  · subst k; simpa using hc
  simpa [h135,h136,h137,h139,h143] using hf k h135 h136 h137 h139 h143

theorem couplingCoefficientPageLoop_exec {P q w s t u band a b N : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hP : 13 ≤ P) (hN : N ≤ s)
    (raw packetTail maskTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hrows : (S.R 140).length = 2*band+1) (hcount : (S.R 143).length = N)
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band 0++packetTail)
    (hmask : S.R 136 = (couplingGuardSymbols true A s t band a b).take N++maskTail) :
    let xs := couplingCoefficientPage P q s t u band a b N
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingCoefficientPageLoopCost P q w s t u band a b N ∧
      Exec body couplingCoefficientPageLoop (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          135 (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band N++packetTail))
          136 maskTail) 137 ((cstream A w xs).reverse++S.R 137))
          139 (List.replicate xs.length tick++S.R 139)) 143 [])}) := by
  simpa [couplingCoefficientPageIntervalLoopCost,couplingCoefficientPageLoopCost,
    couplingCoefficientPageInterval,couplingCoefficientPage] using
    couplingCoefficientPageIntervalLoop_exec (body := body) (origin := 0)
      hA hst hP (by simpa using hN) raw packetTail maskTail v S hready hrows hcount
      hpacket (by simpa using hmask)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
