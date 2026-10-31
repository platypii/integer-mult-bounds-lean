module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredReplicaInteriorPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHandedReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGatherData

/-! Actual cache preparation, shared local gathering, counted handoff and one
same-key numerical batch. The scan's reversed replica order is the output ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def gatheredReplicaInteriorBatch (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (gatheredReplicaInteriorPreparation plan) (handedReplicaInteriorBatch plan hR hQ)

def gatheredReplicaInteriorBatchCost (p l N B V span L s t u target rhsExp : ℕ) : ℕ :=
  let w := executionWidth p l target rhsExp
  prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B+
    (generatedPrefixHandoffCost (N*B) L w+cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp)

theorem gatheredReplicaInteriorBatch_exec (plan : ReplicaInteriorPlacement T)
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
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
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
      replicaInteriorCacheInputBank A (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
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
      n ≤ gatheredReplicaInteriorBatchCost p l Fs.length offsets.length V span L s t u target rhsExp ∧
      Exec body (gatheredReplicaInteriorBatch plan hR hQ) (mk v S) n (mk v' F) ∧
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
  let C := fun r => Fs.reverse.getD r (fun _ => 0)
  have hfit : ∀ j < offsets.length, (lo j).val+L ≤ s := by
    intro j hj
    have hmem : offsets.getD j 0 ∈ offsets := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hlocal := hlocalFit _ hmem
    have horigin : origin+offsets.getD j 0 < s := by omega
    simpa only [lo,ZMod.val_natCast_of_lt horigin] using
      (show origin+offsets.getD j 0+L ≤ s by omega)
  let rhs := cstream A w ((List.range Fs.length).flatMap (fun r =>
    (List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C r))))
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hg,hbankM,hcache,hclock,h119,h120⟩ :=
    gatheredReplicaInteriorPreparation_exec (body := body) plan (2^15*p) (stage+1) q l t u
      (PhaseCellBand.width p u) V origin span L w offsets Fs (fun j => (lo j).val)
      hne hspan hordered hlocalFit hwV hcoords hunits v S tail borrowed suffix packedBorrowed inp out
      hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas hvolume hsource hblank hfresh
  have hbytes : Fs.reverse.flatMap (fun F => cstream A w (offsets.flatMap
      (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0))) = rhs := by
    simpa only [List.length_reverse] using
      packedReplicaStream_list_eq_batch w origin L offsets Fs.reverse (fun _ => 0)
  rw [hbytes] at hg
  have hMR (k : Fin 126) (hk : k ≠ 110) : M.R (plan.gather k) = S.R (plan.gather k) := by
    have hh := congrArg (fun G : Stacks 126 A => G.R k) hg
    simpa only [embStk,Function.comp_apply,Function.update_of_ne hk] using hh
  have hprefix : M.R (plan.gather 110) = rhs++S.R (plan.gather 110) := by
    have hh := congrArg (fun G : Stacks 126 A => G.R 110) hg
    simpa only [Function.update_self,embStk,Function.comp_apply] using hh
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hgF,hframe,hleft,hclean,hinput,herror,hys⟩ :=
    handedReplicaInteriorBatch_exec (body := body) plan hR hQ hA hp hst hu hαu hθ hgap hbudget
      (List.length_pos_iff.mpr hne) hL hLs hpad lo C hC I x hx hfit hint hcell hmax
      v₁ M tail borrowed (S.R (plan.solver 117)) (S.R (plan.gather 110)) inp out
      hbankM hcache (by change (M.R (plan.solver 118)).length = _; rw [hclock,List.length_replicate]) h119 h120 hprefix
      (by rw [hMR 94 (by decide)]; exact hw) (by
        intro k hk
        have hk110 : k ≠ 110 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl <;> decide
        rw [hMR k hk110]
        rcases List.mem_cons.mp hk with hk | hk
        · subst k; exact hfresh 88 (by simp)
        rcases List.mem_cons.mp hk with hk | hk
        · subst k; exact hfresh 89 (by simp)
        rcases List.mem_cons.mp hk with hk | hk
        · subst k; exact hblank 6 (by decide)
        have hk7 : k = 7 := by simpa using hk
        subst k; exact hblank 7 (by decide))
  have hRg : embStk plan.gather F = embStk plan.gather S := by
    rw [hgF,hg]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 110
    · subst k; rfl
    · simp only [Function.update_of_ne hk]
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    hRg,hleft,hclean,hinput,?_,?_,?_,?_,herror,hys⟩
  · exact ((hframe 117 (by decide)).2).trans hcache
  · exact ((hframe 118 (by decide)).2).trans hclock
  · exact ((hframe 119 (by decide)).2).trans h119
  · exact ((hframe 120 (by decide)).2).trans h120

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
