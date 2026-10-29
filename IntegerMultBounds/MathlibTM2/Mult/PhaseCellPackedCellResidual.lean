module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualReadyPackedCellBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

/-! Execute the packed cell stage and its residual coupling in one machine.
The retained coefficient page is shared setup; source, result and scratch
contracts come from the actual preceding execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedCellResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (residualReadyPackedCellBatch hR hQ) (preparedSharedLocalFeedCouplingInterval hQ false)

theorem packedCellResidual_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp origin N V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : origin+N < 2^V) (hunits : (origin+N)*executionWidth p l target rhsExp < 2^V)
    (tail outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L offsets.length
      (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
      (cstream A (executionWidth p l target rhsExp) (packedInterval origin N C)++tail) outTail inp out)
    (hPmaster : (S.R 117).length = 2^15*p)
    (hqmaster : (S.R 119).length = executionPrecision p l target rhsExp)
    (hsmaster : (S.R 121).length = s) (htmaster : (S.R 122).length = t)
    (humaster : (S.R 123).length = u) (hbandmaster : (S.R 124).length = PhaseCellBand.width p u)
    (hamaster : (S.R 141).length = origin) (hbmaster : (S.R 142).length = origin+N)
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], S.L k = [])
    (hpublication : ∀ k ∈ [(128 : Fin 168),130,131,134,135,140], S.R k = [])
    (h166 : S.R 166 = []) (h153 : S.R 153 = [])
    (pageTail : List (Fin (A+4)))
    (hpage : S.R 138 = cstream A (executionWidth p l target rhsExp)
      (couplingCoefficientPageInterval (2^15*p) (executionPrecision p l target rhsExp)
        s t u (PhaseCellBand.width p u) origin (origin+N) origin N)++pageTail)
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval (2^15*p)
      (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) origin (origin+N) origin N).length)
    (hgeometry : CouplingIntervalMetadata V s t (PhaseCellBand.width p u) origin (origin+N) origin N S)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hfitV : origin+(N+2*PhaseCellBand.width p u)+s < 2^V)
    (hsep : N+PhaseCellBand.width p u ≤ s)
    (hfresh : ∀ k ∈ [(127 : Fin 168),143,158,167], S.R k = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let lo := packedCellOrigin (s := s) origin offsets
    let words := scatterRows L (packedInterval origin N C)
      (publishedWords offsets.length L (executedOutputWords s t p u q l offsets.length L
        (executionStagePrecision p l target rhsExp) (sourceExponent l target rhsExp) lo (fun _ => C)))
      (windowGaps L 0 offsets)
    let D := packedField (s := s) origin words
    let E := cstream A w (packedInterval origin N C)
    let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
    let Z := cstream A w (packedInterval origin N
      (guardedCouplingRowField (2^15*p) q t u band origin (origin+N) false D C))
    ∃ v' F m, v'.user = v.user ∧
      m ≤ residualReadyPackedCellBatchCost p l target rhsExp V N L offsets.length s t u+
        preparedSharedLocalFeedCouplingIntervalCost false (2^15*p) q w s t u band origin (origin+N) origin N V ∧
      Exec body (packedCellResidual hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = outTail ∧ F.R 110 = Z++(rhs++(E++tail)) ∧
      F.R 132 = cstream A w (packedInterval origin N D)++S.R 132 ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      embStk packedCellCoreReg F = releasedCellBank (Z++rhs) (E++tail) outTail inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 → k ≠ 140 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      F.R 128 = List.replicate L tick ∧ F.R 130 = List.replicate w tick ∧
      F.R 140 = List.replicate (2*band+1) tick ∧
      PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (F.R 132) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let lo := packedCellOrigin (s := s) origin offsets
  let words := scatterRows L (packedInterval origin N C)
    (publishedWords offsets.length L (executedOutputWords s t p u q l offsets.length L
      (executionStagePrecision p l target rhsExp) (sourceExponent l target rhsExp) lo (fun _ => C)))
    (windowGaps L 0 offsets)
  let D := packedField (s := s) origin words
  let E := cstream A w (packedInterval origin N C)
  let rhs := cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C)))
  let Z := cstream A w (packedInterval origin N
    (guardedCouplingRowField (2^15*p) q t u band origin (origin+N) false D C))
  have h165 := hgeometry.count
  have hV := hgeometry.width
  have h155 : S.R 155 = binSyms V origin := by
    simpa [couplingIntervalValue] using hgeometry.encoded 155 (by simp [couplingIntervalPorts])
  have h154 : S.R 154 = binSyms V 0 := by
    simpa [couplingIntervalValue] using hgeometry.encoded 154 (by simp [couplingIntervalPorts])
  obtain ⟨v₁,F,m₁,hu₁,hm₁,he₁,h93F,h140F,houtput,hDnorm,hDfits,hproj,hframe,h128,h130,hready,hacc,hvalid⟩ :=
    residualReadyPackedCellBatch_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad C hC offsets hne hdis hhalo hfit hVeq hwV hcoords hunits tail outTail inp out v S hbank
      hPmaster hqmaster hsmaster htmaster humaster hbandmaster hamaster hbmaster hleft hpublication
      h165 h166 hV h153 h155 h154
  have hpass (k : Fin 168) (hk : 143 ≤ k.val) : F.R k = S.R k := by
    have hn (j : Fin 168) (hj : j.val < 143) : k ≠ j := by
      intro he
      have hv := congrArg (fun i : Fin 168 => i.val) he
      omega
    exact (hframe k (by omega) (hn 128 (by decide)) (hn 130 (by decide))
      (hn 132 (by decide)) (hn 140 (by decide))).2
  have hgeometryF : CouplingIntervalMetadata V s t band origin (origin+N) origin N F := by
    constructor
    · rw [hpass 163 (by decide)]; exact hV
    · intro k hk
      have hh : 143 ≤ k.val := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hpass k hh]
      exact hgeometry.encoded k hk
  have h127F : F.R 127 = [] :=
    (hframe 127 (by decide) (by decide) (by decide) (by decide) (by decide)).2.trans (hfresh 127 (by simp))
  have h135F : F.R 135 = [] :=
    (hframe 135 (by decide) (by decide) (by decide) (by decide) (by decide)).2.trans (hpublication 135 (by simp))
  have hw5 : 5 ≤ w := by dsimp [w,executionWidth]; omega
  have hqw : q+4 ≤ w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hwcoef : q+(8*p+1)+2 ≤ w := by
    dsimp [q,w,executionPrecision,executionWidth,executionExponent,inputExponent,sourceExponent]
    omega
  have has : ∀ j < N, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (origin+j),
      Fits w z ∧ z.im = 0 := by
    intro j _ z hz
    have hh := couplingCoefficientWords_bounds hp (NeZero.pos s) hst hαu hθ hgap hbudget z hz
    exact ⟨fits_of_value_power hwcoef z hh.1,hh.2⟩
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := preparedSharedLocalFeedCouplingInterval_exec (body := body)
    hQ false hA hw5 hqw hst D C hhalo (S.R 132) pageTail outTail (rhs++(E++tail)) v₁ F
    hready rfl rfl hsep houtput h127F (by simpa only [List.length_replicate,band] using congrArg List.length h140F)
    (by rw [(hframe 138 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact hpage)
    h93F (by rw [hpass 143 (by decide)]; exact hfresh 143 (by simp)) hDfits has V
    (by rw [hpass 166 (by decide)]; exact h166)
    (by rw [(hframe 139 (by decide) (by decide) (by decide) (by decide) (by decide)).2]; exact h139)
    (by omega) hhalo (by omega) hwide hfitV hgeometryF
    (by rw [hpass 158 (by decide)]; exact hfresh 158 (by simp)) h135F
    (by rw [hpass 167 (by decide)]; exact hfresh 167 (by simp))
  have h110F : F.R 110 = rhs++(E++tail) := by
    simpa [embStk,packedCellCoreReg,releasedCellBank,rhs,E,w,q,lo] using
      congrArg (fun B : Stacks 117 A => B.R 110) hproj
  let H : Stacks 168 A := {F with R := (Function.update (Function.update F.R 93 outTail) 110 (Z++F.R 110))}
  have hprojH : embStk packedCellCoreReg H = releasedCellBank (Z++rhs) (E++tail) outTail inp out := by
    have hinp := congrArg (fun B : Stacks 117 A => B.inp) hproj
    have hout := congrArg (fun B : Stacks 117 A => B.out) hproj
    refine Stacks.ext hinp hout ?_ ?_
    · funext k
      simpa [embStk,H,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.L k) hproj
    · funext k
      by_cases h93 : k.val = 93
      · have hk : k = 93 := Fin.ext h93
        subst k; simp [embStk,H,packedCellCoreReg,releasedCellBank]
      by_cases h110 : k.val = 110
      · have hk : k = 110 := Fin.ext h110
        subst k; simp [embStk,H,packedCellCoreReg,releasedCellBank,h110F,List.append_assoc]
      · simpa [embStk,H,packedCellCoreReg,Function.update_apply,Fin.ext_iff,h93,h110,releasedCellBank] using
          congrArg (fun B : Stacks 117 A => B.R k) hproj
  have hframeH : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 → k ≠ 140 →
      H.L k = S.L k ∧ H.R k = S.R k := by
    intro k hk hn128 hn130 hn132 hn140
    have hn93 : k ≠ 93 := by intro he; subst k; norm_num at hk
    have hn110 : k ≠ 110 := by intro he; subst k; norm_num at hk
    simpa [H,hn93,hn110] using hframe k hk hn128 hn130 hn132 hn140
  exact ⟨v₂,H,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,
    by simp [H],by simp [H,h110F,Z,rhs,E,w,q,band,D,words,lo],by simpa [H] using houtput,hDnorm,hDfits,hprojH,hframeH,
    by simpa [H] using h128,by simpa [H] using h130,by simpa [H] using h140F,
    by simpa [H] using hacc⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
