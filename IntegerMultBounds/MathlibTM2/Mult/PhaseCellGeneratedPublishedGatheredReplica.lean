module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatheredReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedGatheredPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRead

/-! Complete generated same-key interior solve and packed halo publication.
The numerical error transfers by exact word equality, with no count factor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def generatedPublishedGatheredReplica (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (generatedGatheredReplicaInteriorBatch plan hR hQ) (preparedGatheredPublication plan)

def generatedPublishedGatheredReplicaCost (p l N B V span L s t u target rhsExp : ℕ) :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (generateReplicaWeightPageCost N (2^15*p) s t u q L w B+
    gatheredReplicaInteriorBatchCost p l N B V span L s t u target rhsExp)+
    preparedGatheredPublicationCost N V span L w B

noncomputable def generatedPublishedGatheredReplicaWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp : ℕ) :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
    generateReplicaWeightPageCost N (2^15*p) s t u q L w B+
    (3*(prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B)+
      (2*generatedPrefixHandoffCost (N*B) L w+
        cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l (N*B) L s t u target rhsExp)))+
    preparedGatheredPublicationWorkspace Q A U N V span L w B

theorem generatedPublishedGatheredReplica_exec_within (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (V origin span : ℕ) (windows : PublicationWindows span L) (Fs : List (ZMod s → GaussianInt))
    (hne : windows.origins ≠ []) (hspan : origin+span ≤ s)
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
    let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
    let C := fun r => Fs.reverse.getD r (fun _ => 0)
    (∀ r < Fs.length, ∀ k, ‖value q (C r k)‖ ≤ (2 : ℝ)^rhsExp) →
    ∀ (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ),
    (∀ r < Fs.length, SchurDominance.Solves (realMatrix s t p u) I (x r)
      (fun k => (value q (C r k)).re)) →
    (∀ j < windows.origins.length, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo j+(k : ZMod s)) ∧
      lo j+(k : ZMod s) ∈ I) →
    (∀ j < windows.origins.length, ∀ k < L, cell s t (lo j+(k : ZMod s)) = cell s t (lo j)) →
    (∀ j < windows.origins.length, ∀ k ∈ I, cell s t k = cell s t (lo j) → ∃ i < L, lo j+(i : ZMod s) = k) →
    embStk weightCacheCoreReg (embStk plan.solver S) =
      replicaWeightFactoryInputBank A (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
        Fs.length windows.origins.length L w (fun j => (lo j).val) [] borrowed tail inp out →
    (∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = []) →
    (S.R (plan.gather 115)).length = V → (S.R (plan.gather 94)).length = w →
    (S.R (plan.gather 102)).length = L →
    S.R (plan.gather 109) = windows.origins.flatMap (binSyms V)++suffix →
    S.R (plan.gather 116) = List.replicate windows.origins.length tick →
    (S.R (plan.gather 121)).length = Fs.length → (S.R (plan.gather 123)).length = span*w →
    S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++packedBorrowed →
    (∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = []) →
    (∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107,122,125], S.R (plan.gather k) = []) →
    S.R (plan.gather 110) = [] →
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = Fs.reverse.map (fun C => cstream A w (packedInterval origin span C)) ∧
      replicas.length = Fs.length ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧ v'.user = v.user ∧
      n ≤ generatedPublishedGatheredReplicaCost p l Fs.length windows.origins.length V span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        generatedPublishedGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l Fs.length
          windows.origins.length V span L s t u target rhsExp) depth
        (generatedPublishedGatheredReplica plan hR hQ) (mk v S) n (mk v' F) ∧
      F.R (plan.gather 124) = packedBorrowed ∧
      F.R (plan.gather 110) = replicas.flatMap (PublicationReplica.output windows w) ∧
      F.R (plan.gather 121) = [] ∧ F.R (plan.solver 93) = tail ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (embStk plan.gather F).L k = (embStk plan.gather S).L k) ∧
      (∀ k : Fin 126, k ≠ 124 → k ≠ 110 → k ≠ 121 → F.R (plan.gather k) = S.R (plan.gather k)) ∧
      (∀ k, (embStk weightCacheCoreReg (embStk plan.solver F)).L k = []) ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg (embStk plan.solver F)).R k = []) ∧
      (embStk weightCacheCoreReg (embStk plan.solver F)).R 110 =
        cstream A w ((List.range Fs.length).flatMap (fun r =>
          (List.range windows.origins.length).flatMap (cellSourceRows L lo (fun _ => C r))))++borrowed ∧
      F.R (plan.solver 117) = batchWeightPage A w q (2^15*p) s t u
        (Fs.length*windows.origins.length) L (fun n => (lo (n%windows.origins.length)).val)++S.R (plan.solver 117) ∧
      F.R (plan.solver 118) = List.replicate (2*((Fs.length*windows.origins.length)*(L*w))) tick ∧
      F.R (plan.solver 119) = [] ∧ F.R (plan.solver 120) = [] ∧
      (∀ r : Fin Fs.length, ∀ j : Fin windows.origins.length, PhaseCellInterface.ErrorOn (publishedCellCore (lo j) L)
        (fun k => (packedIntervalRead q w origin ((F.R (plan.gather 110)).drop (r.val*span*w)) k).re)
        (x r) (1/(2 : ℝ)^target)) := by
  dsimp only
  intro hC I x hx hint hcell hmax hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas
    hvolume hsource hblank hfresh h110
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
  let C := fun r => Fs.reverse.getD r (fun _ => 0)
  have hw1 : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hordered : windows.origins.Pairwise (· ≤ ·) := windows.disjoint.imp (fun h => by omega)
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hgather,hleft,hlow,hrhs,hcache,hreplay,h119,h120,herror,ys,hylen,hys⟩ :=
    generatedGatheredReplicaInteriorBatch_exec_within (body := body) plan hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad V origin span windows.origins Fs hne hspan hordered windows.fits hwV hcoords hunits
      v S tail borrowed suffix packedBorrowed inp out R K hpushR hpushK depth
      hC I x hx hint hcell hmax hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas hvolume hsource hblank
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  have hg (k : Fin 126) : M.R (plan.gather k) = S.R (plan.gather k) := congrFun (congrArg Stacks.R hgather) k
  obtain ⟨v₂,F,n₂,replicas,ha,hinput,hvalid,hu₂,hn₂,he₂,hs₂,hd₂,hout₂,hclock₂,hi₂,ho₂,hl₂,hframe₂⟩ :=
    preparedGatheredPublication_exec_within (body := body) plan V origin span Fs hspan windows hw1
      hwV hcoords hunits ys hylen tail packedBorrowed suffix v₁ M hys
      (by rw [hg]; exact hsource) (by rw [hg]; exact h110)
      (by rw [hg]; exact hreplicas) (by rw [hg]; exact hvolume)
      (by rw [hg]; exact hV) (by rw [hg]; exact hw) (by rw [hg]; exact hLcount)
      (by rw [hg]; exact hpackets) (by rw [hg]; exact hcount)
      (by intro k hk; rw [hg]; exact hblank k hk)
      (by intro k hk; rw [hg]; exact hfresh k hk) depth
  have hnrep : replicas.length = Fs.length := by
    have hh := congrArg List.length ha
    simpa only [List.length_map,List.length_reverse] using hh
  have hsolver (k : Fin 121) (hk : k ≠ 93) : F.R (plan.solver k) = M.R (plan.solver k) :=
    hframe₂ _ (plan.solver_injective.ne hk) (plan.disjoint 124 k).symm
      (plan.disjoint 110 k).symm (plan.disjoint 121 k).symm
  refine ⟨v₂,F,n₁+n₂,replicas,ha,hnrep,hvalid,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,
    hd₂,hout₂,hclock₂,hs₂,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [generatedPublishedGatheredReplica,generatedPublishedGatheredReplicaWorkspace] using mn_seq_within_add he₁ he₂
  · exact hi₂.trans (congrArg (fun B : Stacks 126 A => B.inp) hgather)
  · exact ho₂.trans (congrArg (fun B : Stacks 126 A => B.out) hgather)
  · intro k
    exact (congrFun hl₂ (plan.gather k)).trans (congrFun (congrArg Stacks.L hgather) k)
  · intro k h124 h110 h121
    exact (hframe₂ _ (plan.disjoint k 93) (plan.gather_injective.ne h124)
      (plan.gather_injective.ne h110) (plan.gather_injective.ne h121)).trans (hg k)
  · intro k
    exact (congrFun hl₂ (plan.solver (weightCacheCoreReg k))).trans (hleft k)
  · intro k hk93 hk110
    change F.R (plan.solver (weightCacheCoreReg k)) = []
    rw [hsolver _ (weightCacheCoreReg_injective.ne hk93)]
    exact hlow k hk93 hk110
  · change F.R (plan.solver (weightCacheCoreReg 110)) = _
    rw [hsolver _ (by decide)]
    exact hrhs
  · rw [hsolver 117 (by decide)]; exact hcache
  · rw [hsolver 118 (by decide)]; exact hreplay
  · rw [hsolver 119 (by decide)]; exact h119
  · rw [hsolver 120 (by decide)]; exact h120
  · intro r j
    let rr : Fin replicas.length := ⟨r.val,by rw [hnrep]; exact r.isLt⟩
    have he := publicationReplicas_errorOn windows q w origin hspan replicas hvalid tail x (1/(2 : ℝ)^target)
      (by
        intro ri n
        let ri' : Fin Fs.length := ⟨ri.val,by rw [←hnrep]; exact ri.isLt⟩
        have hh := herror ri' n
        rw [hys] at hh
        simpa only [hinput,lo,List.getD_eq_getElem _ _ n.isLt] using hh) rr j
    simpa only [hout₂,lo,List.getD_eq_getElem _ _ j.isLt] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
