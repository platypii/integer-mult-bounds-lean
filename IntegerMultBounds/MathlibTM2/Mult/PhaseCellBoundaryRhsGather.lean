module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Gather a folded boundary RHS with a descending runtime rank clock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def boundaryRhsGather : Pr P 148 Q A U := countedLoop 0 boundaryRhsWord

def boundaryRhsGatherCost (V w N s : ℕ) : ℕ := N*(boundaryRhsWordCost V w N s+3)+2

theorem boundaryRhsGather_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (C : ZMod s → GaussianInt)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hindex : (S.R 0).length = B.card) (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsGatherCost V w B.card s ∧
      Exec body boundaryRhsGather (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 0 []) 143
          (cstream A w ((List.range B.card).map (fun j => C (bFoldAt s B j)))++S.R 143))}) := by
  let F := fun j => C (bFoldAt s B j)
  let cost := boundaryRhsWordCost V w B.card s
  have hloop : ∀ (clock : List (Fin (A+4))) (vi : HS 148 Q A U) (Si : Stacks 148 A),
      Si.R 0 = clock → clock.length ≤ B.card → (Si.R 115).length = V → (Si.R 94).length = w →
      Si.R 109 = S.R 109 → Si.R 110 = S.R 110 → Si.R 106 = [] → Si.R 139 = [] →
      (∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → Si.R r = []) → vi.flag = clock.head?.isSome →
      ∃ vf n, vf.user = vi.user ∧ n ≤ clock.length*(cost+3)+1 ∧
        Exec body (.loop (·.flag) (countedLoopBody 0 boundaryRhsWord)) (mk vi Si) n
          (mk vf {Si with R := (Function.update (Function.update Si.R 0 []) 143
            (cstream A w ((List.range clock.length).map F)++Si.R 143))}) := by
    intro clock
    induction clock with
    | nil =>
      intro vi Si hc _ _ _ _ _ _ _ _ hflag
      refine ⟨vi,1,rfl,by simp,?_⟩
      have he : Exec body (.loop (·.flag) (countedLoopBody 0 boundaryRhsWord))
          (mk vi Si) 1 (mk vi Si) := Exec.loop_false (by simpa using hflag)
      refine he.cast rfl ?_
      apply congrArg (mk vi)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk : k = 0 <;> by_cases hk143 : k = 143 <;> simp [hk,hk143,hc,cstream]
    | cons x clock ih =>
      intro vi Si hc hN hV' hw' hcoords hrhs' h106' h139' hblank' hflag
      let S₁ : Stacks 148 A := {Si with R := Function.update Si.R 0 clock}
      have hpop : Exec body (.act (.pop (.rt 0) (fun v _ => v) .done)) (mk vi Si) 1 (mk vi S₁) := by
        simpa [S₁,Action.run,hc,update_rt] using
          (Exec.act (body := body) (.pop (.rt 0) (fun v _ => v) .done) (mk vi Si))
      obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryRhsWord_exec (body := body) B V w clock.length hA hs
        (by simp only [List.length_cons] at hN; omega) C coordinateTail rhsTail vi S₁
        (by simp [S₁]) (by simpa [S₁] using hV') (by simpa [S₁] using hw')
        (by simpa [S₁,hcoords] using hcoordinates) (by simpa [S₁,hrhs'] using hrhs)
        (by simpa [S₁] using h106') (by simpa [S₁] using h139') (by
          intro r hr1 hr7
          simpa [S₁,show r ≠ 0 by omega] using hblank' r hr1 hr7)
      have hclock : clock.length ≤ B.card := by simp only [List.length_cons] at hN; omega
      have hn₁' : n₁ ≤ cost := hn₁.trans (by
        dsimp [cost,boundaryRhsWordCost]
        gcongr <;> exact (bFoldAt s B clock.length).val_lt.le)
      let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 143 (csyms A w (F clock.length)++S₁.R 143)}
      have hpeek := Exec.act (body := body) (peekR 0) (mk v₁ S₂)
      rw [peekR_run] at hpeek
      obtain ⟨vf,n₂,hu₂,hn₂,he₂⟩ := ih {v₁ with flag := (S₂.R 0).head?.isSome} S₂
        (by simp [S₂,S₁]) (by simp only [List.length_cons] at hN; omega)
        (by simpa [S₂,S₁] using hV') (by simpa [S₂,S₁] using hw')
        (by simpa [S₂,S₁] using hcoords) (by simpa [S₂,S₁] using hrhs')
        (by simpa [S₂,S₁] using h106') (by simpa [S₂,S₁] using h139') (by
          intro r hr1 hr7
          simpa [S₂,S₁,show r ≠ 0 by omega,show r ≠ 143 by omega] using hblank' r hr1 hr7)
        (by simp [S₂,S₁])
      refine ⟨vf,1+(n₁+1)+n₂+1,hu₂.trans hu₁,?_,
        (Exec.loop_true (by simpa using hflag) (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂).cast rfl ?_⟩
      · simp only [List.length_cons,Nat.succ_mul]
        omega
      · apply congrArg (mk vf)
        refine Stacks.ext rfl rfl rfl ?_
        funext k
        by_cases hk0 : k = 0 <;> by_cases hk143 : k = 143 <;>
          simp [S₂,S₁,hk0,hk143,List.range_succ,cstream,List.append_assoc]
  have hpeek := Exec.act (body := body) (peekR 0) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v',n,hu,hn,he⟩ := hloop (S.R 0) {v with flag := (S.R 0).head?.isSome} S rfl
    hindex.le hV hw rfl rfl h106 h139 hblank rfl
  refine ⟨v',1+n,hu,?_,?_⟩
  · dsimp [boundaryRhsGatherCost]
    rw [hindex] at hn
    dsimp only [cost] at hn
    omega
  · simpa [boundaryRhsGather,countedLoop,hindex,F] using Exec.seq hpeek he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
