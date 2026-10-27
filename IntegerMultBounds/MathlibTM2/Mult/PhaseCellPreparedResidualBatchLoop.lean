module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatchStep

/-! Reuse one prepared page across a counted list of RHS vectors, without repaying setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem preparedResidualBatchLoop_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    S.R 206 = [] → S.R 225 = [] → S.R 227 = [] → S.R 228 = [] → S.R 232 = [] → S.R 233 = [] →
    (S.R 231).length = B.card*w → (S.R 230).length = bs.length → S.R 226 = cstream A w bs.flatten++tail →
    ∃ v' n, v'.user = v.user ∧ n ≤ bs.length*(preparedResidualBatchStepCost q w B.card W+3)+2 ∧
      Exec (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body))
        (countedLoop 230 (preparedResidualBatchStep hQ)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          226 tail) 227 (cstream A w bs.flatten).reverse) 228 (cstream A w (bs.map solve).flatten).reverse) 230 [])}) := by
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
  intro hformat hstage bs hrows hbound v S tail hleft hmul hready hbo hhf hdf hmaster h223 h184 h220 h221 h206 h225 h227 h228 h232 h233 hclock hcount hsource
  let outerBody := embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg body)
  let changed : List (Fin 234) := [226,227,228,230]
  let Inv := fun j (R : Stacks 234 A) =>
    R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ k, k ∉ changed → R.R k = S.R k) ∧
    R.R 226 = cstream A w (bs.drop j).flatten++tail ∧
    R.R 227 = (cstream A w (bs.take j).flatten).reverse ∧
    R.R 228 = (cstream A w ((bs.take j).map solve).flatten).reverse
  have hstable : ∀ j R xs, Inv j R → Inv j {R with R := Function.update R.R 230 xs} := by
    intro j R xs ⟨hi,ho,hl,hf,hs,ha,hb⟩
    refine ⟨hi,ho,hl,?_,?_,?_,?_⟩
    · intro k hk
      have h230 : k ≠ 230 := by intro he; subst k; exact hk (by simp [changed])
      simpa only [Function.update_of_ne h230] using hf k hk
    · simpa using hs
    · simpa using ha
    · simpa using hb
  have hstep : ∀ j < bs.length, ∀ (v : HS 234 Q A U) R, Inv j R →
      ∃ v' R' n, v'.user = v.user ∧ n ≤ preparedResidualBatchStepCost q w B.card W ∧
        Exec outerBody (preparedResidualBatchStep hQ) (mk v R) n (mk v' R') ∧
        R'.R 230 = R.R 230 ∧ Inv (j+1) R' := by
    intro j hj vi R ⟨hi,ho,hl,hf,hs,ha,hb⟩
    have hcore : embStk preparedBoundaryBatchCoreReg R = embStk preparedBoundaryBatchCoreReg S := by
      refine Stacks.ext hi ho ?_ ?_
      · funext i; simp only [embStk,hl]
      · funext i
        apply hf
        have h226 := preparedBoundaryBatchCoreReg_off i 226 (by decide)
        have h227 := preparedBoundaryBatchCoreReg_off i 227 (by decide)
        have h228 := preparedBoundaryBatchCoreReg_off i 228 (by decide)
        have h230 := preparedBoundaryBatchCoreReg_off i 230 (by decide)
        simp [changed,h226,h227,h228,h230]
    have hsrc : R.R 226 = cstream A w bs[j]++(cstream A w (bs.drop (j+1)).flatten++tail) := by
      rw [List.drop_eq_getElem_cons hj] at hs
      simpa only [List.flatten_cons,cstream_append,List.append_assoc] using hs
    have hmem : bs[j] ∈ bs := List.getElem_mem hj
    obtain ⟨vf,n,hu,hn,he⟩ := preparedResidualBatchStep_exec (body := body) hQ hA p u l target rhsExp B W columns hp hlen
      hformat hstage bs[j] (hrows _ hmem) (hbound _ hmem) vi R (cstream A w (bs.drop (j+1)).flatten++tail)
      (by rw [hcore]; exact hleft) (by rw [hcore]; exact hmul) (by rw [hcore]; exact hready)
      (by rw [hcore]; exact hbo) (by rw [hcore]; exact hhf) (by rw [hcore]; exact hdf)
      (by rw [hf 119 (by decide)]; exact hmaster)
      ((hf 223 (by decide)).trans h223) ((hf 184 (by decide)).trans h184)
      ((hf 220 (by decide)).trans h220) ((hf 221 (by decide)).trans h221)
      ((hf 206 (by decide)).trans h206) ((hf 225 (by decide)).trans h225)
      ((hf 232 (by decide)).trans h232) ((hf 233 (by decide)).trans h233)
      (by rw [hf 231 (by decide)]; exact hclock) hsrc
    let R' : Stacks 234 A := {R with R := (Function.update (Function.update (Function.update R.R
      226 (cstream A w (bs.drop (j+1)).flatten++tail)) 227 ((cstream A w bs[j]).reverse++R.R 227))
        228 ((cstream A w (solve bs[j])).reverse++R.R 228))}
    refine ⟨vf,R',n,hu,hn,he,by simp [R'],hi,ho,hl,?_,?_,?_,?_⟩
    · intro k hk
      have h226 : k ≠ 226 := by intro he; subst k; exact hk (by simp [changed])
      have h227 : k ≠ 227 := by intro he; subst k; exact hk (by simp [changed])
      have h228 : k ≠ 228 := by intro he; subst k; exact hk (by simp [changed])
      simpa [R',h226,h227,h228] using hf k hk
    · simp [R']
    · change (cstream A w bs[j]).reverse++R.R 227 = (cstream A w (bs.take (j+1)).flatten).reverse
      rw [ha,List.take_succ_eq_append_getElem hj,List.flatten_append]
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,cstream_append,List.reverse_append]
    · change (cstream A w (solve bs[j])).reverse++R.R 228 =
        (cstream A w ((bs.take (j+1)).map solve).flatten).reverse
      rw [hb,List.take_succ_eq_append_getElem hj,List.map_append,List.flatten_append]
      simp only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,cstream_append,List.reverse_append]
  have hInv : Inv 0 S := by
    refine ⟨rfl,rfl,rfl,fun _ _ => rfl,?_,?_,?_⟩
    · simpa using hsource
    · simpa using h227
    · simpa using h228
  obtain ⟨v',S',n,hu,hn,he,h230,hi,ho,hl,hf,hs,ha,hb⟩ := countedLoop_exec (body := outerBody)
    230 (preparedResidualBatchStep hQ) bs.length (preparedResidualBatchStepCost q w B.card W)
      Inv hstable hstep v S hcount hInv
  refine ⟨v',n,hu,hn,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hi ho hl ?_
  funext k
  by_cases h226 : k = 226
  · subst k; simpa using hs
  by_cases h227' : k = 227
  · subst k; simpa using ha
  by_cases h228' : k = 228
  · subst k; simpa using hb
  by_cases h230' : k = 230
  · subst k; simpa using h230
  simpa [h226,h227',h228',h230'] using hf k (by simp [changed,h226,h227',h228',h230'])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
