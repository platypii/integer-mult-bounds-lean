module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexBatchStep

/-! Release a retained page under a batch-sized result clock without changing the row master. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def sharedComplexBatchReleaseReg (i : Fin 240) : Fin 248 :=
  if i = 121 then 240 else sharedComplexBatchCoreReg i

theorem sharedComplexBatchReleaseReg_injective : Function.Injective sharedComplexBatchReleaseReg := by
  intro i j he
  by_cases hi : i = 121 <;> by_cases hj : j = 121
  · exact hi.trans hj.symm
  · simp only [sharedComplexBatchReleaseReg,hi,hj,ite_true,ite_false] at he
    exact False.elim (sharedComplexBatchCoreReg_off j 240 (by decide) he.symm)
  · simp only [sharedComplexBatchReleaseReg,hi,hj,ite_true,ite_false] at he
    exact False.elim (sharedComplexBatchCoreReg_off i 240 (by decide) he)
  · simp only [sharedComplexBatchReleaseReg,hi,hj,ite_false] at he
    exact sharedComplexBatchCoreReg_injective he

theorem sharedComplexBatchReleaseReg_owned (i : Fin 240) (hi : i ∈ sharedPageOwnedRegs) :
    sharedComplexBatchReleaseReg i = sharedComplexBatchCoreReg i := by
  have hn : i ≠ 121 := by
    intro he
    subst i
    norm_num [sharedPageOwnedRegs_mem] at hi
  simp only [sharedComplexBatchReleaseReg,hn,ite_false]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def sharedComplexBatchRelease : Pr P 248 Q A U :=
  .seq (unaryProduct 121 246 240 244 245)
    (.seq (embProg sharedComplexBatchReleaseReg Empty.elim (sharedPageRelease (P := Empty))) (uclear 240))

theorem sharedComplexBatchReleaseReg_off (i : Fin 240) :
    sharedComplexBatchReleaseReg i ≠ 244 ∧ sharedComplexBatchReleaseReg i ≠ 245 ∧
      sharedComplexBatchReleaseReg i ≠ 246 := by
  by_cases hi : i = 121
  · simp [sharedComplexBatchReleaseReg,hi]
  · simp only [sharedComplexBatchReleaseReg,hi,ite_false]
    exact ⟨sharedComplexBatchCoreReg_off i 244 (by decide),
      sharedComplexBatchCoreReg_off i 245 (by decide),sharedComplexBatchCoreReg_off i 246 (by decide)⟩

def sharedComplexBatchReleaseInput {A : ℕ} (S : Stacks 248 A) (rows : ℕ) : Stacks 248 A :=
  {S with R := Function.update S.R 240 (List.replicate rows tick)}

def sharedComplexBatchReleaseResult {A : ℕ} (S : Stacks 248 A) (rows : ℕ)
    (result tail : List (Fin (A+4))) : Stacks 248 A :=
  let M := sharedComplexBatchReleaseInput S rows
  let T := embStk sharedComplexBatchReleaseReg M
  let T' : Stacks 240 A := {T with R := fun i => if i ∈ sharedPageOwnedRegs then [] else
    (Function.update T.R 132 (result++tail)) i}
  let R := embOvr sharedComplexBatchReleaseReg T'.get M
  {R with R := Function.update R.R 240 []}

theorem sharedComplexBatchRelease_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (N W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (result tail : List (Fin (A+4))) (hresult : result.length = (N*s)*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hs : (S.R 121).length = s) (hcount : (S.R 246).length = N)
    (hW : (S.R 190).length = W) (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = result++(bandTableWords A w B W columns 0++tail))
    (hfresh : ∀ i ∈ ([152,151,131,134,135,136,137,138,231,232,233,237] : List (Fin 240)),
      S.R (sharedComplexBatchCoreReg i) = [])
    (h240 : S.R 240 = []) (h244 : S.R 244 = []) (h245 : S.R 245 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ s*(4*N+9)+4+
        sharedPageReleaseCost (N*s) B.card W w
          (embStk sharedComplexBatchReleaseReg (sharedComplexBatchReleaseInput S (N*s)))+(2*(N*s)+2) ∧
      Exec body sharedComplexBatchRelease (mk v S) n
        (mk v' (sharedComplexBatchReleaseResult S (N*s) result tail)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 246) (dst := 240) (t₁ := 244) (t₂ := 245) (by decide) v S h244 h245
  let M := sharedComplexBatchReleaseInput S (N*s)
  have he₁' : Exec body (unaryProduct 121 246 240 244 245) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hs,hcount,h240,List.append_nil, M, sharedComplexBatchReleaseInput, Nat.mul_comm] using he₁
  have hn₁' : n₁ ≤ s*(4*N+9)+4 := by simpa only [hs,hcount] using hn₁
  let T := embStk sharedComplexBatchReleaseReg M
  have hz : ∀ i ∈ ([152,151,131,134,135,136,137,138,231,232,233,237] : List (Fin 240)), T.R i = [] := by
    intro i hi
    have hn : i ≠ 121 := by intro he; subst i; norm_num at hi
    change Function.update S.R 240 (List.replicate (N*s) tick) (sharedComplexBatchReleaseReg i) = []
    rw [show sharedComplexBatchReleaseReg i = sharedComplexBatchCoreReg i from by
      simp only [sharedComplexBatchReleaseReg,hn,ite_false]]
    rw [Function.update_of_ne (sharedComplexBatchCoreReg_off i 240 (by decide))]
    exact hfresh i hi
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := sharedPageRelease_exec (body := fun p : Empty => nomatch p)
    (rows := N*s) B W w columns hlen result tail hresult (embDn sharedComplexBatchReleaseReg v₁) T
    (by simp [T,M,sharedComplexBatchReleaseInput,embStk,sharedComplexBatchReleaseReg])
    (by simpa [T,M,sharedComplexBatchReleaseInput,embStk,sharedComplexBatchReleaseReg,sharedComplexBatchCoreReg] using hW)
    (by simpa [T,M,sharedComplexBatchReleaseInput,embStk,sharedComplexBatchReleaseReg,sharedComplexBatchCoreReg] using hN)
    (by simpa [T,M,sharedComplexBatchReleaseInput,embStk,sharedComplexBatchReleaseReg,sharedComplexBatchCoreReg] using hw)
    (by simpa [T,M,sharedComplexBatchReleaseInput,embStk,sharedComplexBatchReleaseReg,sharedComplexBatchCoreReg] using hsource) hz
  obtain ⟨v₃,hv₃,hu₃,he₃⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedComplexBatchReleaseReg_injective (fun p => nomatch p) he₂ v₁ rfl M rfl
  let T' : Stacks 240 A := {T with R := fun i => if i ∈ sharedPageOwnedRegs then [] else
    (Function.update T.R 132 (result++tail)) i}
  let R := embOvr sharedComplexBatchReleaseReg T'.get M
  have hclock : (R.R 240).length = N*s := by
    have hread := congrArg (fun X : Stacks 240 A => X.R 121)
      (embStk_ovr sharedComplexBatchReleaseReg_injective T' M)
    have hn121 : (121 : Fin 240) ∉ sharedPageOwnedRegs := by norm_num [sharedPageOwnedRegs_mem]
    simpa [R,T',T,M,sharedComplexBatchReleaseInput,embStk,sharedComplexBatchReleaseReg,hn121] using
      congrArg List.length hread
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 240 v₃ R
  have he₄' : Exec body (uclear 240) (mk v₃ R) (2*(N*s)+2)
      (mk v₄ {R with R := Function.update R.R 240 []}) := by simpa only [hclock] using he₄
  refine ⟨v₄,n₁+(n₂+(2*(N*s)+2)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    Exec.seq he₁' (Exec.seq he₃ he₄')⟩
  exact (Nat.add_le_add hn₁' (Nat.add_le_add_right hn₂ _)).trans_eq (Nat.add_assoc _ _ _).symm

theorem sharedComplexBatchReleaseResult_off {A : ℕ} (S : Stacks 248 A) (rows : ℕ)
    (result tail : List (Fin (A+4))) (j : Fin 248) (hj : j ≠ 240)
    (hoff : ∀ i, sharedComplexBatchReleaseReg i ≠ j) :
    (sharedComplexBatchReleaseResult S rows result tail).R j = S.R j := by
  unfold sharedComplexBatchReleaseResult
  dsimp only
  rw [Function.update_of_ne hj]
  exact (embOvr_off (e := sharedComplexBatchReleaseReg) _ _ hoff).2.trans
    (Function.update_of_ne hj _ _)

theorem sharedComplexBatchReleaseResult_rowMaster {A : ℕ} (S : Stacks 248 A) (rows : ℕ)
    (result tail : List (Fin (A+4))) :
    (sharedComplexBatchReleaseResult S rows result tail).R 121 = S.R 121 := by
  apply sharedComplexBatchReleaseResult_off S rows result tail 121 (by decide)
  intro i
  by_cases hi : i = 121
  · simp [sharedComplexBatchReleaseReg,hi]
  · have hn : sharedComplexBatchCoreReg i ≠ 121 := sharedComplexBatchCoreReg_injective.ne hi
    simpa only [sharedComplexBatchReleaseReg,hi,ite_false] using hn

theorem sharedComplexBatchReleaseCost_eq {A : ℕ} (S : Stacks 248 A) (rows N W w : ℕ) :
    sharedPageReleaseCost rows N W w
      (embStk sharedComplexBatchReleaseReg (sharedComplexBatchReleaseInput S rows)) =
    sharedPageReleaseCost rows N W w (embStk sharedComplexBatchCoreReg S) := by
  unfold sharedPageReleaseCost
  have hsum :
      (sharedPageOwnedRegs.map (fun i =>
        ((embStk sharedComplexBatchReleaseReg (sharedComplexBatchReleaseInput S rows)).R i).length)) =
      (sharedPageOwnedRegs.map (fun i => ((embStk sharedComplexBatchCoreReg S).R i).length)) := by
    apply List.map_congr_left
    intro i hi
    simp only [embStk,Function.comp_def,sharedComplexBatchReleaseInput,
      sharedComplexBatchReleaseReg_owned i hi,
      Function.update_of_ne (sharedComplexBatchCoreReg_off i 240 (by decide))]
  rw [hsum]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
