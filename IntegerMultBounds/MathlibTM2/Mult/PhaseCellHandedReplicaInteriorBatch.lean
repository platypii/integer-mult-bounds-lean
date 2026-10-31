module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorBatch

/-! The generated prefix handoff feeds the actual cached interior execution.
Local gather coordinates and ambient numerical headers occupy disjoint banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def handedReplicaInteriorBatch (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq plan.handoff (embProg plan.solver Empty.elim (cachedBatchFromOrigins (P₀ := Empty) hR hQ))

theorem handedReplicaInteriorBatch_exec (plan : ReplicaInteriorPlacement T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l N B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ r < N, ∀ k, ‖value (executionPrecision p l target rhsExp) (C r k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ r < N, SchurDominance.Solves (realMatrix s t p u) I (x r)
      (fun k => (value (executionPrecision p l target rhsExp) (C r k)).re))
    (hfit : ∀ j < B, (lo j).val+L ≤ s)
    (hint : ∀ j < B, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo j+(k : ZMod s)) ∧
      lo j+(k : ZMod s) ∈ I)
    (hcell : ∀ j < B, ∀ k < L, cell s t (lo j+(k : ZMod s)) = cell s t (lo j))
    (hmax : ∀ j < B, ∀ k ∈ I, cell s t k = cell s t (lo j) → ∃ i < L, lo j+(i : ZMod s) = k)
    (v : HS T Q A U) (S : Stacks T A) (tail borrowed cacheTail gatherTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let stage := executionStagePrecision p l target rhsExp
    let origins := fun n => lo (n%B)
    let rhs := cstream A w ((List.range N).flatMap (fun r =>
      (List.range B).flatMap (cellSourceRows L lo (fun _ => C r))))
    embStk weightCacheCoreReg (embStk plan.solver S) = batchInputBank (2^15*p) (stage+1) q l s t u
      (PhaseCellBand.width p u) L (N*B) (fun n => (origins n).val) [] borrowed tail inp out →
    (embStk plan.solver S).R 117 = batchWeightPage A w q (2^15*p) s t u (N*B) L
      (fun n => (origins n).val)++cacheTail →
    ((embStk plan.solver S).R 118).length = 2*((N*B)*(L*w)) →
    (embStk plan.solver S).R 119 = [] → (embStk plan.solver S).R 120 = [] →
    S.R (plan.gather 110) = rhs++gatherTail → (S.R (plan.gather 94)).length = w →
    (∀ k ∈ [(88 : Fin 126),89,6,7], S.R (plan.gather k) = []) →
    ∃ v' F n, v'.user = v.user ∧
      n ≤ generatedPrefixHandoffCost (N*B) L w+cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp ∧
      Exec body (handedReplicaInteriorBatch plan hR hQ) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = {embStk plan.gather S with R := Function.update (embStk plan.gather S).R 110 gatherTail} ∧
      (∀ k : Fin 121, 117 ≤ k.val →
        (embStk plan.solver F).L k = (embStk plan.solver S).L k ∧
        (embStk plan.solver F).R k = (embStk plan.solver S).R k) ∧
      (∀ k, (embStk weightCacheCoreReg (embStk plan.solver F)).L k = []) ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg (embStk plan.solver F)).R k = []) ∧
      (embStk weightCacheCoreReg (embStk plan.solver F)).R 110 = rhs++borrowed ∧
      (∀ r : Fin N, ∀ j : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo j) L)
        (publishedBatchRead q w (r.val*B+j.val) L (lo j)
          ((embStk weightCacheCoreReg (embStk plan.solver F)).R 93)) (x r) (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp),
        ys.val.length = (N*B)*L*w ∧ (embStk weightCacheCoreReg (embStk plan.solver F)).R 93 = ys++tail := by
  dsimp only
  intro hbank hcache hclock h119 h120 hprefix hword hfresh
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let stage := executionStagePrecision p l target rhsExp
  let origins := fun n => lo (n%B)
  let rhs := cstream A w ((List.range N).flatMap (fun r =>
    (List.range B).flatMap (cellSourceRows L lo (fun _ => C r))))
  have hlen : rhs.length = (N*B)*L*w := by
    simp only [rhs,length_cstream,List.length_flatMap,cellSourceRows_length,List.map_const',
      List.length_range,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
    ring
  have hN : (S.R (plan.solver 116)).length = N*B := by
    have hh := congrArg (fun M : Stacks 117 A => (M.R 116).length) hbank
    simpa [embStk,weightCacheCoreReg,batchInputBank] using hh
  have hLcount : (S.R (plan.solver 103)).length = L := by
    have hh := congrArg (fun M : Stacks 117 A => (M.R 103).length) hbank
    simpa [embStk,weightCacheCoreReg,batchInputBank] using hh
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hg,hs⟩ := plan.handoff_exec (body := body) N B L w rhs gatherTail hlen v S
    hN hLcount hword hprefix hfresh
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (plan.gather 110) gatherTail)
    (plan.solver 110) (rhs++S.R (plan.solver 110)))}
  have hs' : embStk plan.solver M = {embStk plan.solver S with R := (Function.update (embStk plan.solver S).R 110
      (rhs++(embStk plan.solver S).R 110))} := hs
  have hmeta (k : Fin 121) (hk : k ≠ 110) : (embStk plan.solver M).R k = (embStk plan.solver S).R k := by
    rw [hs']
    exact Function.update_of_ne hk _ _
  have hinput : embStk weightCacheCoreReg (embStk plan.solver M) =
      batchInputBank (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u) L (N*B)
        (fun n => (origins n).val) rhs borrowed tail inp out := by
    have hh := congrArg (embStk weightCacheCoreReg) hs'
    have hv := embStk_updateR weightCacheCoreReg_injective (embStk plan.solver S) 110
      (rhs++(embStk plan.solver S).R 110)
    refine hh.trans (hv.trans ?_)
    change {embStk weightCacheCoreReg (embStk plan.solver S) with R :=
      (Function.update (embStk weightCacheCoreReg (embStk plan.solver S)).R 110
        (rhs++(embStk weightCacheCoreReg (embStk plan.solver S)).R 110))} = _
    rw [hbank]
    have hb := batchInputBank_prepend_rhs (A := A) (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
      L (N*B) (fun n => (origins n).val) rhs borrowed tail inp out
    simpa [batchInputBank,q,stage,origins] using hb
  obtain ⟨vi,Fsmall,n₂,hui,hn₂,hei,hframe,hI,hO,hleft,hsource,hblank,herror,hys⟩ :=
    replicaInteriorBatch_exec (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hB hL hLs hpad lo C hC I x hx hfit hint hcell hmax (embDn plan.solver v₁) (embStk plan.solver M)
      tail borrowed cacheTail inp out hinput
      (by rw [hmeta 117 (by decide)]; exact hcache)
      (by rw [hmeta 118 (by decide)]; exact hclock)
      (by rw [hmeta 119 (by decide)]; exact h119)
      (by rw [hmeta 120 (by decide)]; exact h120)
  rw [←replicaInteriorBatchCost_eq] at hn₂
  obtain ⟨v₂,F,he₂,hv₂,hu₂,hproj,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    plan.solver_injective (fun p => nomatch p) hei v₁ rfl M rfl
  have hMinp : M.inp = inp := congrArg Stacks.inp hinput
  have hMout : M.out = out := congrArg Stacks.out hinput
  have hFg : embStk plan.gather F = embStk plan.gather M := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact (congrArg Stacks.inp hproj).trans (hI.trans hMinp.symm)
    · exact (congrArg Stacks.out hproj).trans (hO.trans hMout.symm)
    · funext k
      exact (hoff (plan.gather k) (fun j => (plan.disjoint k j).symm)).1
    · funext k
      exact (hoff (plan.gather k) (fun j => (plan.disjoint k j).symm)).2
  refine ⟨v₂,F,n₁+n₂,hu₂.trans (hui.trans hu₁),Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    hFg.trans hg,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    rw [hproj]
    have hh := hframe k hk
    have hML := congrArg Stacks.L hs'
    exact ⟨hh.1.trans (congrFun hML k),hh.2.trans (hmeta k (by intro he; subst k; norm_num at hk))⟩
  · simpa only [hproj] using hleft
  · simpa only [hproj] using hblank
  · simpa only [hproj] using hsource
  · simpa only [hproj] using herror
  · simpa only [hproj] using hys

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
