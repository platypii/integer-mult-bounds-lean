module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatchLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Generate batch controls, reuse one factor page, restore borrowed RHS bytes and publish all solutions in order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def preparedResidualBatchWorkspace (P : Type) (hQ : SS.states ≤ Q)
    (q w N W replicas : ℕ) : ℕ :=
  3*(N*(4*w+9)+4)+(3*(4*replicas+4)+
    (replicas*N*w+preparedResidualBatchStepWorkspace (A := A) (U := U) P hQ q w N W))

theorem preparedResidualBatch_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    let solve := fun (b : List GaussianInt) => (bandSolveVec q W Lc Uc rcs
      (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (bs : List (List GaussianInt)), (∀ b ∈ bs, b.length = B.card) →
    (∀ b ∈ bs, ∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u) ∧ |gv q x.im| ≤
      (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (v : HS 234 Q A U) (S : Stacks 234 A) (tail : List (Fin (A+4))),
    let T := embStk preparedBoundaryBatchCoreReg S
    let σ := boundaryFactorState (embStk preparedBoundaryCoreReg T)
    (∀ i, (embStk preparedBoundaryCoreReg T).L i = []) →
    (∀ i : Fin 64, (embStk preparedBoundaryCoreReg T).R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    (S.R 119).length = q → S.R 223 = [] → S.R 184 = [] → S.R 220 = [] → S.R 221 = [] →
    S.R 206 = [] → S.R 225 = [] → S.R 227 = [] → S.R 228 = [] → S.R 230 = [] → S.R 231 = [] →
    S.R 232 = [] → S.R 233 = [] →
    (S.R 229).length = bs.length → S.R 226 = cstream A w bs.flatten++tail →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualBatchCost q w B.card W bs.length ∧
      ExecWithin (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          preparedResidualBatchWorkspace (A := A) (U := U) P hQ q w B.card W bs.length) 0
        (preparedResidualBatch hQ) (mk v S) n
        (mk v' {S with R := Function.update S.R 224 (cstream A w (bs.map solve).flatten++S.R 224)}) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let Lc := naturalLineLc q K W B.card AZ
  let Uc := naturalLineUc q K W B.card AZ
  let rcs := naturalLineRcs q K W B.card AZ
  let solve := fun (b : List GaussianInt) => (bandSolveVec q W Lc Uc rcs
      (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
  intro hformat hstage bs hrows hbound v S tail hleft hmul hready hbo hhf hdf hmaster h223 h184 h220 h221 h206 h225 h227 h228 h230 h231 h232 h233 hcount hsource
  let raw := cstream A w bs.flatten
  let ys := cstream A w (bs.map solve).flatten
  let outerBody := embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body)
  have h192 : (S.R 192).length = B.card := hready.sn
  have h160 : (S.R 160).length = w := hready.ready.wn
  have hrawLen : raw.length = bs.length*B.card*w := cstream_flatten_length w B.card bs hrows
  have hsolRows : ∀ y ∈ bs.map solve, y.length = B.card := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    simpa only [solve,List.length_map] using naturalLineSolve_length q K W B.card AZ
      (b.map (normalizeBoundaryWord q (q/2-1))) (by simp [hrows b hb])
  have hysLen : ys.length = bs.length*B.card*w := by
    simpa only [List.length_map] using cstream_flatten_length (A := A) w B.card (bs.map solve) hsolRows
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := outerBody)
    (a := 192) (b := 160) (dst := 231) (t₁ := 232) (t₂ := 233) (by decide) v S h232 h233
  let S₁ : Stacks 234 A := {S with R := Function.update S.R 231 (List.replicate (B.card*w) tick)}
  have he₁' : Exec outerBody (unaryProduct 192 160 231 232 233) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [h192,h160,h231,List.append_nil] using he₁
  have hn₁' : n₁ ≤ B.card*(4*w+9)+4 := by simpa only [h192,h160] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := outerBody) (a := 229) (b := 230) (t := 233)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h233)
  let S₂ : Stacks 234 A := {S₁ with R := Function.update S₁.R 230 (List.replicate bs.length tick)}
  have he₂' : Exec outerBody (ucopy 229 230 233) (mk v₁ S₁) (4*bs.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hcount,h230] using he₂
  have hcore : embStk preparedBoundaryBatchCoreReg S₂ = embStk preparedBoundaryBatchCoreReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have h230' := preparedBoundaryBatchCoreReg_off i 230 (by decide)
    have h231' := preparedBoundaryBatchCoreReg_off i 231 (by decide)
    simp [embStk,S₂,S₁,h230',h231']
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := preparedResidualBatchLoop_exec (body := body) hQ hA p u l target rhsExp B W columns hp hlen
    hformat hstage bs hrows hbound v₂ S₂ tail
    (by rw [hcore]; exact hleft) (by rw [hcore]; exact hmul) (by rw [hcore]; exact hready)
    (by rw [hcore]; exact hbo) (by rw [hcore]; exact hhf) (by rw [hcore]; exact hdf)
    (by simpa [S₂,S₁] using hmaster)
    (by simpa [S₂,S₁] using h223)
    (by simpa [S₂,S₁] using h184)
    (by simpa [S₂,S₁] using h220)
    (by simpa [S₂,S₁] using h221)
    (by simpa [S₂,S₁] using h206) (by simpa [S₂,S₁] using h225)
    (by simpa [S₂,S₁] using h227) (by simpa [S₂,S₁] using h228)
    (by simpa [S₂,S₁] using h232) (by simpa [S₂,S₁] using h233)
    (by change (S₂.R 231).length = B.card*w; simp [S₂,S₁]) (by simp [S₂]) (by simpa [S₂,S₁] using hsource)
  let S₃ : Stacks 234 A := {S₂ with R := (Function.update (Function.update (Function.update (Function.update S₂.R
    226 tail) 227 raw.reverse) 228 ys.reverse) 230 [])}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec outerBody 227 226 (by decide) id v₃ S₃
  let S₄ : Stacks 234 A := {S₃ with R := movedR S₃.R 227 226 id (S₃.R 227)}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec outerBody 228 224 (by decide) id v₄ S₄
  let S₅ : Stacks 234 A := {S₄ with R := movedR S₄.R 228 224 id (S₄.R 228)}
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec outerBody 231 v₅ S₅
  have h227Len : (S₃.R 227).length = bs.length*B.card*w := by simp [S₃,hrawLen]
  have h228Len : (S₄.R 228).length = bs.length*B.card*w := by simp [S₄,S₃,movedR,hysLen]
  have h231Len : (S₅.R 231).length = B.card*w := by simp [S₅,S₄,S₃,S₂,S₁,movedR]
  have hproduct : mnNativePushBound 3 (unaryProduct (P := P) (Q := Q) (A := A) (U := U)
      (192 : Fin 234) 160 231 232 233) := by
    simp [unaryProduct,umulSym,ucopy,scanP,scanR,drainR,popDo,keepIn,pushN,
      moveR,whileR,moveStep,peekR,popPush,mnNativePushBound,mnActPush]
  have hcopy : mnNativePushBound 3 (ucopy (P := P) (Q := Q) (A := A) (U := U)
      (229 : Fin 234) 230 233) := by
    simp [ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,
      moveR,whileR,moveStep,peekR,popPush,mnNativePushBound,mnActPush]
  have hw₁ := mn_native_exec_within he₁' 3 hproduct 0
    (mnSize (mk v S)+0+3*(B.card*(4*w+9)+4))
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₁') _)
  have hw₂ := mn_native_exec_within he₂' 3 hcopy 0 _ (le_refl _)
  let loopSpace := bs.length*B.card*w+preparedResidualBatchStepWorkspace (A := A) (U := U) P hQ q w B.card W
  have hw₃ : ExecWithin outerBody (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+0+loopSpace) 0
      (countedLoop 230 (preparedResidualBatchStep hQ)) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    apply he₃.mono
    intro d z hz
    simpa only [loopSpace,Nat.add_assoc,Nat.add_zero] using hz
  let limit := mnSize (mk v₂ S₂)+0+loopSpace
  have hw₄ := moveR_within 227 226 id he₄ 0 limit hw₃.final
  have hw₅ := moveR_within 228 224 id he₅ 0 limit hw₄.final
  have hw₆ := mn_native_exec_within he₆ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) 0 limit
    (by simpa only [Nat.zero_mul,Nat.add_zero] using hw₅.final)
  have hrest := ExecWithin.seq hw₃ (ExecWithin.seq hw₄ (ExecWithin.seq hw₅ hw₆))
  have hcopyRest := execWithin_seq_two_budget outerBody _ _ _ _ _ _ _ 0 _ _ hw₂ hrest
  have hwithin := execWithin_seq_two_budget outerBody _ _ _ _ _ _ _ 0 _ _ hw₁ hcopyRest
  refine ⟨v₆,n₁+((4*bs.length+4)+(n₃+((2*(S₃.R 227).length+2)+((2*(S₄.R 228).length+2)+(2*(S₅.R 231).length+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    hwithin.cast rfl ?_⟩
  · change n₁+((4*bs.length+4)+(n₃+((2*(S₃.R 227).length+2)+((2*(S₄.R 228).length+2)+(2*(S₅.R 231).length+2))))) ≤
        preparedResidualBatchCost q w B.card W bs.length
    rw [h227Len,h228Len,h231Len]
    have hn₃' : n₃ ≤ bs.length*(preparedResidualBatchStepCost q w B.card W+3)+2 := hn₃
    dsimp only [preparedResidualBatchCost,preparedResidualBatchStepCost] at *
    nlinarith only [hn₁',hn₃']
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have hsource' : S.R 226 = raw++tail := hsource
    by_cases h224 : i = 224 <;> by_cases h226 : i = 226 <;> by_cases h227' : i = 227 <;>
      by_cases h228' : i = 228 <;> by_cases h230' : i = 230 <;> by_cases h231' : i = 231 <;>
      simp [S₅,S₄,S₃,S₂,S₁,movedR,h224,h226,h227',h228',h230',h231',hsource',h227,h228,h230,h231] <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
