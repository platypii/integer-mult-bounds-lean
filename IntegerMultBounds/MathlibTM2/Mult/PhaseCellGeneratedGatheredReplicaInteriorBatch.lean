module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredReplicaInteriorPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaWeightFactoryBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredReplicaInteriorStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGatherData

/-! Actual cache preparation, shared local gathering, counted handoff and one
same-key numerical batch. The scan's reversed replica order is the output ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def generatedGatheredReplicaInteriorBatch (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (embProg (fun i => plan.solver (weightCacheCoreReg i)) Empty.elim
    (generateReplicaWeightPage (P₀ := Empty))) (gatheredReplicaInteriorBatch plan hR hQ)

theorem generatedGatheredReplicaInteriorBatch_exec_within (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (V origin span : ℕ) (offsets : List ℕ) (Fs : List (ZMod s → GaussianInt))
    (hne : offsets ≠ []) (hspan : origin+span ≤ s) (hordered : offsets.Pairwise (· ≤ ·))
    (hlocalFit : ∀ j ∈ offsets, j+L ≤ span)
    (hwV : executionWidth p l target rhsExp < 2^V) (hcoords : span < 2^V)
    (hunits : span*executionWidth p l target rhsExp < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (tail borrowed suffix packedBorrowed : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let stage := executionStagePrecision p l target rhsExp
    let lo := fun j => ((origin+offsets.getD j 0 : ℕ) : ZMod s)
    let C := fun r => Fs.reverse.getD r (fun _ => 0)
    (∀ r < Fs.length, ∀ k, ‖value q (C r k)‖ ≤ (2 : ℝ)^rhsExp) →
    ∀ (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ),
    (∀ r < Fs.length, SchurDominance.Solves (realMatrix s t p u) I (x r)
      (fun k => (value q (C r k)).re)) →
    (∀ j < offsets.length, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo j+(k : ZMod s)) ∧
      lo j+(k : ZMod s) ∈ I) →
    (∀ j < offsets.length, ∀ k < L, cell s t (lo j+(k : ZMod s)) = cell s t (lo j)) →
    (∀ j < offsets.length, ∀ k ∈ I, cell s t k = cell s t (lo j) → ∃ i < L, lo j+(i : ZMod s) = k) →
    embStk weightCacheCoreReg (embStk plan.solver S) =
      replicaWeightFactoryInputBank A (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
        Fs.length offsets.length L w (fun j => (lo j).val) [] borrowed tail inp out →
    (∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = []) →
    (S.R (plan.gather 115)).length = V → (S.R (plan.gather 94)).length = w →
    (S.R (plan.gather 102)).length = L →
    S.R (plan.gather 109) = offsets.flatMap (binSyms V)++suffix →
    S.R (plan.gather 116) = List.replicate offsets.length tick →
    (S.R (plan.gather 121)).length = Fs.length → (S.R (plan.gather 123)).length = span*w →
    S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++packedBorrowed →
    (∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = []) →
    (∀ k ∈ [(88 : Fin 126),89,90,91,92,104,105,106,122,125], S.R (plan.gather k) = []) →
    ∃ v' F n, v'.user = v.user ∧
      n ≤ generateReplicaWeightPageCost Fs.length (2^15*p) s t u q L w offsets.length+
        gatheredReplicaInteriorBatchCost p l Fs.length offsets.length V span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S) + depth +
        (mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
          generateReplicaWeightPageCost Fs.length (2^15*p) s t u q L w offsets.length+
          (3 * (prepareReplicaInteriorCacheCost Fs.length offsets.length L w +
            sharedPackedReplicaGatherCost V Fs.length span L w offsets.length) +
          (2 * generatedPrefixHandoffCost (Fs.length*offsets.length) L w +
            cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l
              (Fs.length*offsets.length) L s t u target rhsExp))))
        depth (generatedGatheredReplicaInteriorBatch plan hR hQ) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = embStk plan.gather S ∧
      (∀ k, (embStk weightCacheCoreReg (embStk plan.solver F)).L k = []) ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg (embStk plan.solver F)).R k = []) ∧
      (embStk weightCacheCoreReg (embStk plan.solver F)).R 110 =
        cstream A w ((List.range Fs.length).flatMap (fun r =>
          (List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C r))))++borrowed ∧
      F.R (plan.solver 117) = batchWeightPage A w q (2^15*p) s t u
        (Fs.length*offsets.length) L (fun n => (lo (n%offsets.length)).val)++S.R (plan.solver 117) ∧
      F.R (plan.solver 118) = List.replicate (2*((Fs.length*offsets.length)*(L*w))) tick ∧
      F.R (plan.solver 119) = [] ∧ F.R (plan.solver 120) = [] ∧
      (∀ r : Fin Fs.length, ∀ j : Fin offsets.length, PhaseCellInterface.ErrorOn (publishedCellCore (lo j) L)
        (publishedBatchRead q w (r.val*offsets.length+j.val) L (lo j)
          ((embStk weightCacheCoreReg (embStk plan.solver F)).R 93)) (x r) (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp),
        ys.val.length = (Fs.length*offsets.length)*L*w ∧
          (embStk weightCacheCoreReg (embStk plan.solver F)).R 93 = ys++tail := by
  dsimp only
  intro hC I x hx hint hcell hmax hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas
    hvolume hsource hblank hfresh
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let stage := executionStagePrecision p l target rhsExp
  let lo := fun j => ((origin+offsets.getD j 0 : ℕ) : ZMod s)
  let e := fun i => plan.solver (weightCacheCoreReg i)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  have hprecision : 13 ≤ 2^15*p := by omega
  obtain ⟨vi,n₁,huser,hn₁,hei⟩ := replicaWeightFactoryBank_exec_within
    (Q := Q) (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u) Fs.length offsets.length L w
    (fun j => (lo j).val) hprecision (NeZero.pos s) hst hu
    (fun j hj => (lo j).val_lt) hLs (embDn e v) [] borrowed tail inp out depth
  rw [← hbank] at hei
  obtain ⟨v₁,M,hv₁,hu₁,he₁,hproj,hoff⟩ := exec_emb_within_stock e
    (body' := body) (ι := Empty.elim) he (fun p => nomatch p) hei v rfl S rfl
  have hgR (k : Fin 126) : M.R (plan.gather k) = S.R (plan.gather k) :=
    (hoff _ (fun j => (plan.disjoint k (weightCacheCoreReg j)).symm)).2
  have hg : embStk plan.gather M = embStk plan.gather S := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact (congrArg Stacks.inp hproj).trans (congrArg Stacks.inp hbank).symm
    · exact (congrArg Stacks.out hproj).trans (congrArg Stacks.out hbank).symm
    · funext k
      exact (hoff _ (fun j => (plan.disjoint k (weightCacheCoreReg j)).symm)).1
    · funext k
      exact hgR k
  have hhigh (k : Fin 121) (hk : 117 ≤ k.val) : M.R (plan.solver k) = S.R (plan.solver k) := by
    apply (hoff _ ?_).2
    intro j hj
    have hh := plan.solver_injective hj
    have hv := congrArg (fun i : Fin 121 => i.val) hh
    have hjlt := j.isLt
    dsimp [weightCacheCoreReg] at hv
    omega
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hrest⟩ := gatheredReplicaInteriorBatch_exec_within (body := body)
    plan hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad
    V origin span offsets Fs hne hspan hordered hlocalFit hwV hcoords hunits
    v₁ M tail borrowed suffix packedBorrowed inp out R K hpushR hpushK depth
    hC I x hx hint hcell hmax hproj
    (by intro k hk; rw [hhigh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl <;> decide)]; exact hcacheFresh k hk)
    (by rw [hgR]; exact hV) (by rw [hgR]; exact hw) (by rw [hgR]; exact hLcount)
    (by rw [hgR]; exact hpackets) (by rw [hgR]; exact hcount) (by rw [hgR]; exact hreplicas)
    (by rw [hgR]; exact hvolume) (by rw [hgR]; exact hsource)
    (by intro k hk; rw [hgR]; exact hblank k hk)
    (by intro k hk; rw [hgR]; exact hfresh k hk)
  refine ⟨v₂,F,n₁+n₂,hu₂.trans (hu₁.trans huser),Nat.add_le_add hn₁ hn₂,
    mn_seq_within_add he₁ he₂,?_⟩
  simpa only [hg,hhigh 117 (by decide)] using hrest

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
