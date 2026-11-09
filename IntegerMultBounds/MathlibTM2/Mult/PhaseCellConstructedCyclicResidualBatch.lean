module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicFactorFactoryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPreparedResidualBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeBoundaryUnfoldWorkspace
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! One executed cyclic factor setup serves the whole ordered residual batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- The factory's structural workspace with the actual fixed programs' push counts. -/
noncomputable def actualCyclicFactorWorkspace (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  let J := mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr)
  let ringPush := mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
    Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR)
  let batchPush := mnProgPush (cmulBlock cr (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr))
  let rowPush := mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr)
  constructedCyclicFactorWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    hQ J ringPush batchPush rowPush p u l s t a n target 2

noncomputable def constructedCyclicResidualBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 234 Q A U :=
  .seq (embProg preparedBoundaryBatchCoreReg id (preparedCyclicFactorFactory hR hQ)) (preparedResidualBatch hQ)

theorem constructedCyclicResidualBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (v : HS 234 Q A U) (S : Stacks 234 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg S)))))))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 224, S.L (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = [])
    (bs : List (List GaussianInt))
    (hrowsB : ∀ b ∈ bs, b.length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hbound : ∀ b ∈ bs, ∀ z ∈ b,
      |gv (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) z.re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
      |gv (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) z.im| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u))
    (rhsTail : List (Fin (A+4)))
    (h225 : S.R 225 = []) (h227 : S.R 227 = []) (h228 : S.R 228 = [])
    (h230 : S.R 230 = []) (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = [])
    (hcount : (S.R 229).length = bs.length)
    (hsource : S.R 226 = cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) bs.flatten++rhsTail) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*PhaseCellBand.width p u+1
    let K := factorNewtonSteps p q
    ∃ v' page steps, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg page))
      let AZ := factorRankIntegerMatrix B W columns
      let solve := fun (b : List GaussianInt) => (bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
        (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
      let F : Stacks 234 A := {page with R := (Function.update page.R 224
        (cstream A w (bs.map solve).flatten++page.R 224))}
      v'.user = v.user ∧ steps ≤ constructedCyclicFactorCost p u l s t a n target 2+
        preparedResidualBatchCost q w B.card W bs.length ∧
      ExecWithin (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body)))))))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          (actualCyclicFactorWorkspace (P₀ := P₀) (A := A) (U := U) hR hQ p u l s t a n target+
            preparedResidualBatchWorkspace (A := A) (U := U) P₀ hQ q w B.card W bs.length)) 0
        (constructedCyclicResidualBatch hR hQ) (mk v S) steps (mk v' F) ∧
      Exec (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body)))))))
        (constructedCyclicResidualBatch hR hQ) (mk v S) steps
        (mk v' F) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^bits) columns ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      (∀ b ∈ bs, (solve b).length = B.card ∧ ∀ z ∈ solve b, Fits w z) ∧
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg F)) = σ ∧
      page.inp = S.inp ∧ page.out = S.out ∧ page.L = S.L ∧
      page.R 224 = S.R 224 ∧ (∀ k : Fin 234, 226 ≤ k.val → page.R k = S.R k) ∧
      NativeBoundaryUnfoldWorkspace B.card F := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 24*PhaseCellBand.width p u+1
  let K := factorNewtonSteps p q
  let T := embStk preparedBoundaryBatchCoreReg S
  let coreBody := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  let native := embTab preparedBoundaryCoreReg coreBody
  obtain ⟨v₁,T₁,m₁,columns,hu₁,hm₁,he₁,hprepared,hacc,hsolve,hbo,hhf,hdf,hvk,hdout,
    hinp,hout,hL,htable,h224,h225',hmul,h119,h223,h184,h220,h221,h116⟩ :=
    preparedCyclicFactorFactory_spec_within (body := body) (rhsExp := 2) hR hQ hA axis has hbs
      _ _ _ (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) _ (Nat.le_refl _)
      (embDn preparedBoundaryBatchCoreReg v) T tail pageTail hrows hpageWidth hpage hready
      haSrc hleftEnd hrightEnd h141 h142 h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr_within_stock preparedBoundaryBatchCoreReg (ι := id)
    preparedBoundaryBatchCoreReg_injective (body := native) (body' := embTab preparedBoundaryBatchCoreReg native)
    (by intro f; rfl) he₁ v rfl S rfl
  let page := embOvr preparedBoundaryBatchCoreReg T₁.get S
  have hproj : embStk preparedBoundaryBatchCoreReg page = T₁ :=
    embStk_ovr preparedBoundaryBatchCoreReg_injective T₁ S
  have hread (k : Fin 234) (hk : k.val < 226) : page.R k = T₁.R ⟨k.val,hk⟩ :=
    congrArg (fun F => F.R ⟨k.val,hk⟩) hproj
  have hprivate (k : Fin 234) (hk : 226 ≤ k.val) : page.R k = S.R k :=
    (embOvr_off T₁.get S (fun i => preparedBoundaryBatchCoreReg_off i k hk)).2
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := cyclicPreparedResidualBatch_exec (body := coreBody)
    hQ hA p u l target t a n columns axis.hp hprepared bs hrowsB hbound v₂ page rhsTail
    (by intro i
        rw [hproj]
        change T₁.L (preparedBoundaryCoreReg i) = []
        rw [hL]
        exact hleft i)
    (by rw [hproj]; exact hmul)
    (by rw [hproj]; exact hsolve)
    (by rw [hproj]; exact hbo) (by rw [hproj]; exact hhf) (by rw [hproj]; exact hdf)
    (by simpa [hread 119 (by decide)] using h119)
    (by simpa [hread 223 (by decide)] using h223)
    (by simpa [hread 184 (by decide)] using h184)
    (by simpa [hread 220 (by decide)] using h220)
    (by simpa [hread 221 (by decide)] using h221)
    (by simpa [hread 206 (by decide),boundaryFactorState,boundaryFactorReg,embStk,preparedBoundaryCoreReg] using hvk)
    (by simpa [hread 225 (by decide),T,embStk,preparedBoundaryBatchCoreReg,h225] using h225')
    (by rw [hprivate 227 (by decide)]; exact h227)
    (by rw [hprivate 228 (by decide)]; exact h228)
    (by rw [hprivate 230 (by decide)]; exact h230)
    (by rw [hprivate 231 (by decide)]; exact h231)
    (by rw [hprivate 232 (by decide)]; exact h232)
    (by rw [hprivate 233 (by decide)]; exact h233)
    (by rw [hprivate 229 (by decide)]; exact hcount)
    (by rw [hprivate 226 (by decide)]; exact hsource)
  have hwithin := execWithin_seq_two_budget (embTab preparedBoundaryBatchCoreReg native)
    _ _ _ _ _ _ _ 0 _ _ he₂ he₃
  refine ⟨v₃,page,m₁+m₃,columns,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hm₁ hm₃,
    hwithin,Exec.seq he₂.toExec he₃.toExec,hprepared,hacc,?_,?_,?_,?_,?_,?_,hinp,hout,embOvr_left_of_eq S T₁ hL,?_,hprivate,?_⟩
  · simpa only [hproj] using hsolve
  · simpa only [hproj] using hbo
  · simpa only [hproj] using hhf
  · simpa only [hproj] using hdf
  · intro b hb
    exact boundary_residual_solution_format A p u l target 2 B W columns axis.hp (by omega)
      hprepared.length hprepared.format hprepared.stage b (hrowsB b hb) (hbound b hb)
  · funext r
    change Function.update page.R 224 _
      (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg (boundaryFactorReg r))) =
        page.R (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg (boundaryFactorReg r)))
    apply Function.update_of_ne
    intro heq
    have hv := congrArg Fin.val heq
    have hi := (boundaryFactorReg r).isLt
    simp only [preparedBoundaryBatchCoreReg,preparedBoundaryCoreReg] at hv
    omega
  · simpa [hread 224 (by decide),T,embStk,preparedBoundaryBatchCoreReg] using h224

  · have hworkspace : NativeBoundaryUnfoldWorkspace B.card page := by
      refine ⟨?_,(hread 184 (by decide)).trans h184,(hread 223 (by decide)).trans h223,?_⟩
      · intro i
        have hh := congrArg (fun S => S.R (preparedBoundaryCoreReg (boundaryFactorMulReg i))) hproj
        exact hh.trans (hmul i)
      · have hh := congrArg List.length ((hread 116 (by decide)).trans h116)
        exact hh.trans hrows
    exact hworkspace.updateR 224 _ (by decide) (by decide) (by decide) (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
