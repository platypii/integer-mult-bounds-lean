module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U} {body'' : P → Pr P 249 Q A U}

theorem packedHaloNumericalBatch_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target finalTarget rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hwidth : 8*p ≤ 2^u) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ)))
    (hC : ∀ x ∈ inputs, ∀ k, ‖value (executionPrecision p l target rhsExp) (x.1 k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail : List (Fin (A+4)))
    (v : HS 249 Q A U) (S : Stacks 249 A)
    (hcount : (S.R 248).length = inputs.length)
    (hsource : (embStk packedHaloBatchReg S).R 110 = (inputs.map (fun x => cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) x.1))).flatten++tail)

    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)

    (hsep : b-a+PhaseCellBand.width p u ≤ s)

    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hq : executionPrecision p l target rhsExp = executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
 :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*PhaseCellBand.width p u+1
    PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u band a b V w W B.card (embStk packedHaloBatchReg S) →
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    target = boundaryHaloTarget p u boundaryTarget rhsExp B.card →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    let AZ := factorRankIntegerMatrix B W columns
    let K := factorNewtonSteps p q
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg S)) →
    boundaryTarget = boundaryRecoveryTarget p finalTarget →
    (∀ x ∈ inputs, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x.2
      (fun k => (value q (x.1 k)).re)) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, v'.user = v.user ∧
      n ≤ packedHaloBatchCost inputs.length
        (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V) ∧
      Exec body'' (packedHaloBatch hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = [] ∧
      ((embStk packedHaloBatchReg F).R 132).length =
        inputs.length*((b-a)*w)+((embStk packedHaloBatchReg S).R 132).length ∧
      (embStk packedHaloBatchReg F).R 110 = tail ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b V w W B.card (embStk packedHaloBatchReg F) ∧
      PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
        (cstream A w (Uc.map colC).flatten)
        (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt)))
        (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg F)) ∧
      PackedHaloInputTrace (fun x S F => ∃ D : ZMod s → GaussianInt,
        F.R 132 = cstream A w (packedInterval a (b-a) D)++S.R 132 ∧
        PhaseCellInterface.ErrorOn (haloVertices s a b)
          (fun i => (packedIntervalRead q w a (F.R 132) i).re) x.2 (1/(2 : ℝ)^finalTarget))
        inputs (embStk packedHaloBatchReg S) (embStk packedHaloBatchReg F) ∧
      (∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
        (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg F)).R k =
          (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg S)).R k) ∧
      ((embStk packedHaloBatchReg F).L = (embStk packedHaloBatchReg S).L ∧
      (embStk packedHaloBatchReg F).inp = S.inp ∧ (embStk packedHaloBatchReg F).out = S.out ∧
      (∀ k : Fin 168, k ∈ haloAuxiliaryPorts →
        (embStk packedHaloBatchReg F).R (packedRecoveryRuntimeReg k) =
          (embStk packedHaloBatchReg S).R (packedRecoveryRuntimeReg k)) ∧
      (embStk packedHaloBatchReg F).R 93 = S.R 93 ∧
      (embStk packedHaloBatchReg F).R 238 = S.R 238) ∧
      IntegerMultBounds.MathlibTM2.Fast.Main.mnSize
        (mk (embDn packedHaloBatchReg v') (embStk packedHaloBatchReg F)) ≤
      IntegerMultBounds.MathlibTM2.Fast.Main.mnSize
        (mk (embDn packedHaloBatchReg v) (embStk packedHaloBatchReg S))+inputs.length*((b-a)*w)+V := by
  dsimp only
  intro hbetween columns hcolumns hcell htable hpages hboundary hy hcoeff
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  let encode := fun x : (ZMod s → GaussianInt) × (ZMod s → ℝ) =>
    cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) x.1)
  let pages := fun T : Stacks 248 A => PackedBoundaryFactorPages
    (cstream A w ((naturalLineLc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
    (cstream A w ((naturalLineUc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
    (cstream A w ((naturalLineRcs q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt)))
    (embStk packedBoundaryRecoveryBase T)
  let Ready := fun (xs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ))) (T : Stacks 248 A) =>
    (∀ x ∈ xs, x ∈ inputs) ∧ T.R 110 = (xs.map encode).flatten++tail ∧
    PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u band a b V w W B.card T ∧ pages T ∧
    (∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
      (embStk packedBoundaryRecoveryBase T).R k =
        (embStk packedBoundaryRecoveryBase (embStk packedHaloBatchReg S)).R k) ∧
    T.L = (embStk packedHaloBatchReg S).L ∧ T.inp = S.inp ∧ T.out = S.out ∧
    (∀ k : Fin 168, k ∈ haloAuxiliaryPorts → T.R (packedRecoveryRuntimeReg k) =
      (embStk packedHaloBatchReg S).R (packedRecoveryRuntimeReg k)) ∧ T.R 93 = S.R 93 ∧ T.R 238 = S.R 238
  obtain ⟨vf,F,n,hu',hn,he,hcounter,hready,htrace⟩ := packedHaloBatch_list_exec
    hbody' hR hQ
    (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)
    Ready (fun x S F => ∃ D : ZMod s → GaussianInt,
      F.R 132 = cstream A w (packedInterval a (b-a) D)++S.R 132 ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) x.2 (1/(2 : ℝ)^finalTarget))
    (by
      intro x xs vi T hready
      obtain ⟨hmem,hsource,hbetween,hpages,hsetup,hleft,hinput,houtput,hauxiliary,h93,h238⟩ := hready
      have hx : x ∈ inputs := hmem x (by simp)
      have hsrc : T.R 110 = encode x++((xs.map encode).flatten++tail) := by
        simpa only [List.map_cons,List.flatten_cons,List.append_assoc] using hsource
      obtain ⟨vf,G,m,D,hu',hm,he,hout,herr,hsrc',hbetween',hpages',hsetup',hleft',hinput',houtput',hauxiliary',h93',h238'⟩ :=
        packedHaloNextInput_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
          hbudget hpad x.1 (hC x hx) hab hb hband hwide hVeq hwV hcoords hunits
          ((xs.map encode).flatten++tail) vi T hsrc haLt hfitV hsep hdom hq
          hbetween columns hcolumns hcell htable hpages hboundary x.2 (hy x hx) hcoeff
      refine ⟨vf,G,m,hu',hm,he,⟨?_,hsrc',hbetween',hpages' _ _ _ hpages,?_,hleft'.trans hleft,hinput'.trans hinput,houtput'.trans houtput,fun k hk => (hauxiliary' k hk).trans (hauxiliary k hk),h93'.trans h93,h238'.trans h238⟩,D,hout,herr⟩
      · intro z hz
        exact hmem z (by simp only [List.mem_cons]; exact Or.inr hz)
      · intro k hk hne
        exact (hsetup' k hk hne).trans (hsetup k hk hne))
    inputs v S hcount ⟨(by intro x hx; exact hx),hsource,hbetween,hpages,(by intros; rfl),rfl,rfl,rfl,(by intros; rfl),rfl,rfl⟩
  have hlength := htrace.output_length (L := (b-a)*w) (by
    intro x T G hresult
    obtain ⟨D,hout,herror⟩ := hresult
    rw [hout,List.length_append,length_cstream,packedInterval_length D (by omega)])
  have hf := hready.2.2.2.2.2
  have hstock := htrace.ready_stock_le (L := (b-a)*w) (by
    intro x T G hresult
    obtain ⟨D,hout,herror⟩ := hresult
    rw [hout,List.length_append,length_cstream,packedInterval_length D (by omega)])
    hbetween hready.2.2.1 hf.2.1 hf.2.2.1 hf.1 hf.2.2.2.2.1 hf.2.2.2.1 (by
      intro k hk hk'
      by_cases h238 : k = 238
      · subst k; exact hf.2.2.2.2.2
      · let j : Fin 242 := ⟨k.val,hk'⟩
        exact hready.2.2.2.2.1 j hk (by
          intro he; apply h238; exact Fin.ext (congrArg (fun i : Fin 242 => i.val) he)))
    encode [] tail (by simpa only [List.append_nil] using hsource)
    (by simpa only [List.map_nil,List.flatten_nil,List.nil_append] using hready.2.1)
    (embDn packedHaloBatchReg v) (embDn packedHaloBatchReg vf)
  exact ⟨vf,F,n,hu',hn,he,hcounter,hlength,by simpa only [List.map_nil,List.flatten_nil,List.nil_append] using hready.2.1,
    hready.2.2.1,hready.2.2.2.1,htrace,hready.2.2.2.2.1,hready.2.2.2.2.2,hstock⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
