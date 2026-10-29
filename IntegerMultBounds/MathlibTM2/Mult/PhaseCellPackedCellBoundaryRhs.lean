module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataPackedBoundaryRhs

/-! The actual cell execution supplies the packed field, residual, released
workspace and retained geometry used to extract its boundary RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedCellBoundaryRhs (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (packedCellResidual hR hQ) metadataPackedBoundaryRhs

theorem packedCellBoundaryRhs_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let B := PhaseCellDiscreteGeometry.haloBoundary s t band origin (origin+N)
    let selected := cstream A w ((PhaseCellMatrix.bOrder s B).map
      (couplingRowField (2^15*p) q t u band origin (origin+N) false D C))
    ∃ v' F m, v'.user = v.user ∧
      m ≤ residualReadyPackedCellBatchCost p l target rhsExp V N L offsets.length s t u+
        preparedSharedLocalFeedCouplingIntervalCost false (2^15*p) q w s t u band origin (origin+N) origin N V +
        metadataPackedBoundaryRhsCost V N w ∧
      Exec body (packedCellBoundaryRhs hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = selected++outTail ∧
      F.R 167 = couplingSourceIntervalMaskSymbols true A s t band origin (origin+N) origin N ∧ F.R 110 = Z++(rhs++(E++tail)) ∧
      F.R 132 = cstream A w (packedInterval origin N D)++S.R 132 ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      embStk packedCellCoreReg F = releasedCellBank (Z++rhs) (E++tail) (selected++outTail) inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 → k ≠ 140 → k ≠ 167 →
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
  let B := PhaseCellDiscreteGeometry.haloBoundary s t band origin (origin+N)
  let selected := cstream A w ((PhaseCellMatrix.bOrder s B).map
    (couplingRowField (2^15*p) q t u band origin (origin+N) false D C))
  obtain ⟨v₁,F,m₁,hu₁,hm₁,he₁,h93,h110,h132,hDnorm,hDfits,hproj,hframe,h128,h130,h140,hacc⟩ :=
    packedCellResidual_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad
      C hC offsets hne hdis hhalo hfit hVeq hwV hcoords hunits tail outTail inp out v S hbank
      hPmaster hqmaster hsmaster htmaster humaster hbandmaster hamaster hbmaster hleft hpublication
      h166 h153 pageTail hpage h139 hgeometry hwide hfitV hsep hfresh
  have hpass (k : Fin 168) (hk : 143 ≤ k.val) : F.R k = S.R k := by
    have hn (j : Fin 168) (hj : j.val < 143) : k ≠ j := by
      intro he
      have hv := congrArg (fun i : Fin 168 => i.val) he
      omega
    exact (hframe k (by omega) (hn 128 (by decide)) (hn 130 (by decide))
      (hn 132 (by decide)) (hn 140 (by decide))).2
  have hgeometryF : CouplingIntervalMetadata V s t band origin (origin+N) origin N F := by
    constructor
    · rw [hpass 163 (by decide)]; exact hgeometry.width
    · intro k hk
      have hh : 143 ≤ k.val := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hpass k hh]
      exact hgeometry.encoded k hk
  have hblank : ∀ k : Fin 168, k.val < 32 → F.R k = [] := by
    intro k hk
    let i : Fin 117 := ⟨k.val,by omega⟩
    have hi : packedCellCoreReg i = k := Fin.ext rfl
    have hn93 : i.val ≠ 93 := by dsimp [i]; omega
    have hn110 : i.val ≠ 110 := by dsimp [i]; omega
    have hh := congrArg (fun X : Stacks 117 A => X.R i) hproj
    simpa only [embStk,Function.comp_apply,hi,releasedCellBank,ite_eq_right hn93,ite_eq_right hn110] using hh
  have hB : ∀ i ∈ B, origin ≤ i.val ∧ i.val < origin+N := by
    intro i hi
    exact (PhaseCellDiscreteGeometry.mem_haloVertices _ _ _).mp (Finset.mem_sdiff.mp hi).1
  have h167 : F.R 167 = [] := by rw [hpass 167 (by decide)]; exact hfresh 167 (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := metadataPackedBoundaryRhs_exec (body := body) v₁ F hgeometryF
    hhalo hst (by omega) hhalo (by omega) (by dsimp [band]; omega) hfitV hblank hB
    (guardedCouplingRowField (2^15*p) q t u band origin (origin+N) false D C) w
    (rhs++(E++tail)) h110 h167 (by simpa only [List.length_replicate] using congrArg List.length h130)
  have hrows : (PhaseCellMatrix.bOrder s B).map
      (guardedCouplingRowField (2^15*p) q t u band origin (origin+N) false D C) =
      (PhaseCellMatrix.bOrder s B).map (couplingRowField (2^15*p) q t u band origin (origin+N) false D C) := by
    apply List.map_congr_left
    intro i hi
    apply guardedCouplingRowField_eq hst _ _ _ _ _ _ false hhalo D C i
    exact Or.inr (of_decide_eq_true (List.mem_filter.mp hi).2)
  let H : Stacks 168 A := {F with R := (Function.update
    (Function.update F.R 167 (couplingSourceIntervalMaskSymbols true A s t band origin (origin+N) origin N))
    93 (selected++F.R 93))}
  have he₂' : Exec body metadataPackedBoundaryRhs (mk v₁ F) m₂ (mk v₂ H) := by
    have hh := hrows
    dsimp only [B] at hh
    simpa only [H,selected,B,hh] using he₂
  have hprojH : embStk packedCellCoreReg H =
      releasedCellBank (Z++rhs) (E++tail) (selected++outTail) inp out := by
    have hinp := congrArg (fun X : Stacks 117 A => X.inp) hproj
    have hout := congrArg (fun X : Stacks 117 A => X.out) hproj
    refine Stacks.ext hinp hout ?_ ?_
    · funext k
      simpa only [embStk,H,releasedCellBank] using congrArg (fun X : Stacks 117 A => X.L k) hproj
    · funext k
      have h167k : packedCellCoreReg k ≠ 167 := by
        intro he; have hh := congrArg Fin.val he; have hk := k.isLt
        change k.val = 167 at hh; omega
      have hv167 : k.val ≠ 167 := by have hk := k.isLt; omega
      by_cases h93k : k.val = 93
      · have hk : k = 93 := Fin.ext h93k
        subst k; simp [embStk,H,packedCellCoreReg,releasedCellBank,h93]
      · have hh := congrArg (fun X : Stacks 117 A => X.R k) hproj
        simpa [embStk,H,Function.update_apply,packedCellCoreReg,Fin.ext_iff,h93k,hv167,releasedCellBank,Z,rhs,E,w,q,band,D,words,lo] using hh
  have hframeH : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 → k ≠ 140 → k ≠ 167 →
      H.L k = S.L k ∧ H.R k = S.R k := by
    intro k hk hn128 hn130 hn132 hn140 hn167
    have hn93 : k ≠ 93 := by intro he; subst k; norm_num at hk
    simpa [H,hn93,hn167] using hframe k hk hn128 hn130 hn132 hn140
  refine ⟨v₂,H,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂',?_,?_,?_,?_,
    hDnorm,hDfits,hprojH,hframeH,?_,?_,?_,?_⟩
  · simp [H,h93,selected,B,q,w,band,D,words,lo]
  · simp [H,band]
  · simpa [H] using h110
  · simpa [H] using h132
  · simpa [H] using h128
  · simpa [H] using h130
  · simpa [H] using h140
  · simpa [H] using hacc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
