module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualBatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedExportCyclicResidualRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaResidualAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundarySolutionAccuracy

/-! Execute cached residual export followed by one actual cyclic factor factory
and the shared residual solver. No numerical RHS-row or factor supplier remains. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def generatedCyclicResidualBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 234 Q A U :=
  .seq preparedExportCyclicResidualRows (constructedCyclicResidualBatch hR hQ)

theorem generatedCyclicResidualBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {s t p u l target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let bits := boundaryTableBits p target 2 B.card
    let cellTarget := initialSchurTarget p u bits 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    let W := 24*band+1
    let K := factorNewtonSteps p q
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2)
      (Cs Ds : List (ZMod s → GaussianInt)),
    Cs.length = Fs.length → Ds.length = Fs.length →
    (∀ j : Fin Cs.length, ReplicaCouplingResidualSpec
      (axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF)
      (Fs.length-1-j.val) (Cs[j.val]'j.isLt)) →
    (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec
      (axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF)
      (Fs.length-1-j.val) (Ds[j.val]'j.isLt)) →
    let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
    ∀ (v : HS 234 Q A U) (S : Stacks 234 A) (tail pageTail : List (Fin (A+4))),
    CyclicReplicaBoundaryInputs (s := s) t band a n w
      (embStk cyclicResidualRowsReg (cyclicResidualVolumeState (min n (s-a)) (n-min n (s-a)) w S)) →
    (∀ r : Fin 180, r.val < 6 → S.R (cyclicResidualRowsReg r) = []) →
    S.R 169 = Cs.flatMap (fun C => cstream A w (packedInterval a (min n (s-a)) C)) →
    S.R 172 = Ds.flatMap (fun D => cstream A w (packedInterval 0 (n-min n (s-a)) D)) →
    (S.R 229).length = Fs.length →
    (∀ r ∈ [(168 : Fin 234),171,174,175,176,177,178], S.R r = []) →
    CyclicResidualBatchInput p l s t u target a n tail pageTail
      (exportedCyclicResidualRows S (cstream A w rows.flatten)) →
    ∃ vf page steps, ∃ columns : List (ZMod s → GaussianInt),
      let E := exportedCyclicResidualRows S (cstream A w rows.flatten)
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg page))
      let AZ := factorRankIntegerMatrix B W columns
      let solve := fun (b : List GaussianInt) => (bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
        (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
      let F : Stacks 234 A := {page with R := (Function.update page.R 224
        (cstream A w (rows.map solve).flatten++page.R 224))}
      vf.user = v.user ∧
      steps ≤ (cyclicReplicaBoundaryVolumesCost a n w+exportCyclicResidualRowsCost Fs.length n B.card w)+
        (constructedCyclicFactorCost p u l s t a n target 2+preparedResidualBatchCost q w B.card W Fs.length) ∧
      Exec (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body)))))))
        (generatedCyclicResidualBatch hR hQ) (mk v S) steps (mk vf F) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t band a n).toList).1 (1/(2 : ℝ)^bits) columns ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      (∀ b ∈ rows, (solve b).length = B.card ∧ ∀ z ∈ solve b, Fits w z) ∧
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg F)) = σ ∧
      page.inp = S.inp ∧ page.out = S.out ∧ page.L = S.L ∧
      page.R 224 = S.R 224 ∧ (∀ k : Fin 234, 226 ≤ k.val → page.R k = E.R k) ∧
      (∀ j : Fin Fs.length, ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) →
        let solution := solve (rows.getD j.val [])
        solution.length = B.card ∧ ∀ i < B.card,
          ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
          ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧
      ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
        (∀ rhs, SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) (R rhs) rhs) ∧
        ∀ j : Fin Fs.length, ∀ i ∈ B,
          |(value q (cyclicReplicaResidualField a n (Cs.getD j.val (fun _ => 0))
            (Ds.getD j.val (fun _ => 0)) i)).re-
            SchurDominance.residual (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) R
              (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i| ≤
            haloResidualError p u q 2 cellTarget := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p target 2 B.card
  let cellTarget := initialSchurTarget p u bits 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  let W := 24*band+1
  intro Fs hF Cs Ds hCs hDs hC hD v S tail pageTail inputs hblank hleft hright hreplicas hfresh factory
  let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
  let E := exportedCyclicResidualRows S (cstream A w rows.flatten)
  let native := embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
    (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))))
  have hzip : (Cs.zip Ds).length = Fs.length := by simp [hCs,hDs]
  have hleftPairs := congrArg
    (fun fields => fields.flatMap (fun C => cstream A w (packedInterval a (min n (s-a)) C)))
    (List.map_fst_zip (by omega : Cs.length ≤ Ds.length))
  have hrightPairs := congrArg
    (fun fields => fields.flatMap (fun D => cstream A w (packedInterval 0 (n-min n (s-a)) D)))
    (List.map_snd_zip (by omega : Ds.length ≤ Cs.length))
  simp only [List.flatMap_map] at hleftPairs hrightPairs
  have haSrc : (S.R 144).length = a := by
    simpa [E,exportedCyclicResidualRows,cyclicResidualRowsRetired] using factory.origin
  have hleftEnd : (S.R 145).length = a+min n (s-a) := by
    simpa [E,exportedCyclicResidualRows,cyclicResidualRowsRetired] using factory.leftEnd
  have hrightEnd : (S.R 146).length = n-min n (s-a) := by
    simpa [E,exportedCyclicResidualRows,cyclicResidualRowsRetired] using factory.rightEnd
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preparedExportCyclicResidualRows_exec (body := native)
    axis.hst (by omega) band a n ha hn (Cs.zip Ds) w v S inputs hblank
    (by rw [hleftPairs]; exact hleft) (by rw [hrightPairs]; exact hright)
    (by rw [hzip]; exact hreplicas) haSrc hleftEnd hrightEnd hfresh
  have he₁' : Exec native preparedExportCyclicResidualRows (mk v S) m₁ (mk v₁ E) := by
    simpa only [cyclicReplicaBoundaryRows_stream] using he₁
  obtain ⟨hlen,hrows,hreal,hbound⟩ :=
    cyclicReplicaBoundaryRows_format axis cellTarget 2 a n ha hn Fs hF Cs Ds hCs hDs hC hD
  have hrowsLen : rows.length = Fs.length := hlen
  have hcount : (E.R 229).length = rows.length := by
    simpa [E,exportedCyclicResidualRows,cyclicResidualRowsRetired,hrowsLen] using hreplicas
  have hsource : E.R 226 = cstream A w rows.flatten++[] := by
    simp [E,exportedCyclicResidualRows,cyclicResidualRowsRetired]
  obtain ⟨vf,page,m₂,columns,hu₂,hm₂,he₂,hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,
    hinp,hout,hL,h224,hprivate⟩ := constructedCyclicResidualBatch_spec (body := body)
    hR hQ hA axis ha hn v₁ E tail pageTail factory.rows factory.pageWidth factory.page factory.arithmetic
    factory.origin factory.leftEnd factory.rightEnd
    (factory.fresh 141 (by simp)) (factory.fresh 142 (by simp))
    (factory.fresh 0 (by simp)) (factory.fresh 139 (by simp))
    (factory.fresh 127 (by simp)) (factory.fresh 138 (by simp))
    (factory.fresh 143 (by simp)) (factory.fresh 147 (by simp))
    (factory.fresh 151 (by simp)) (factory.fresh 152 (by simp)) (factory.fresh 153 (by simp))
    factory.left factory.new rows hrows hbound []
    (factory.privateFresh 225 (by simp)) (factory.privateFresh 227 (by simp))
    (factory.privateFresh 228 (by simp)) (factory.privateFresh 230 (by simp))
    (factory.privateFresh 231 (by simp)) (factory.privateFresh 232 (by simp))
    (factory.privateFresh 233 (by simp)) hcount hsource
  refine ⟨vf,page,m₁+m₂,columns,hu₂.trans hu₁,?_,Exec.seq he₁' he₂,
    hprepared,hacc,hsolve,hbo,hhf,hdf,hformat,hfactor,hinp,hout,hL,?_,hprivate,?_,?_⟩
  · exact Nat.add_le_add (by simpa only [hzip] using hm₁) (by simpa only [hrowsLen] using hm₂)
  · simpa [E,exportedCyclicResidualRows,cyclicResidualRowsRetired] using h224
  · intro j x hx
    have hjC : j.val < Cs.length := by rw [hCs]; exact j.isLt
    have hjD : j.val < Ds.length := by rw [hDs]; exact j.isLt
    have hrow : rows.getD j.val [] = cyclicReplicaBoundaryRow t band a n
        (Cs.getD j.val (fun _ => 0)) (Ds.getD j.val (fun _ => 0)) :=
      cyclicReplicaBoundaryRows_getD t band a n j.val Cs Ds hjC hjD
    have haccuracy := cyclicReplicaBoundary_solution_accuracy A p u l target a n axis ha hn (by omega)
      Fs hF Cs Ds hCs hDs hC hD columns hprepared hacc j x hx
    rw [← hrow] at haccuracy
    exact haccuracy
  · exact cyclicReplicaResiduals_accurate axis cellTarget 2 a n ha hn Fs hF Cs Ds hCs hDs
      (replicaCouplingResiduals_accurate _ axis.hp axis.hpacket Cs hCs hC)
      (replicaCouplingResiduals_accurate _ axis.hp axis.hpacket Ds hDs hD)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
