module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatheredReplicaFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAccumulatingGatheredPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRange
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationSuffix

/-! Execute a generated same-key numerical solve into an independent accumulated
packed output. Original RHS, replica count and gather metadata are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def generatedAccumulatingGatheredReplica (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (generatedGatheredReplicaInteriorBatch plan hR hQ) (accumulatingGatheredPublication plan dst)

def generatedAccumulatingGatheredReplicaCost (p l N B V span L s t u target rhsExp : ℕ) :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (generateReplicaWeightPageCost N (2^15*p) s t u q L w B+
    gatheredReplicaInteriorBatchCost p l N B V span L s t u target rhsExp)+
    accumulatingGatheredPublicationCost N V span L w B

noncomputable def generatedAccumulatingGatheredReplicaWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp : ℕ) :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  (mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
    generateReplicaWeightPageCost N (2^15*p) s t u q L w B+
    (3*(prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B)+
      (2*generatedPrefixHandoffCost (N*B) L w+
        cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l (N*B) L s t u target rhsExp)))+
    accumulatingGatheredPublicationWorkspace Q A U N V span L w B

theorem generatedAccumulatingGatheredReplica_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (V origin span : ℕ) (windows : PublicationWindows span L) (Fs : List (ZMod s → GaussianInt))
    (ambientRows : List (List (Fin (A+4))))
    (hne : windows.origins ≠ []) (hspan : origin+span ≤ s)
    (hwV : executionWidth p l target rhsExp < 2^V) (hcoords : span < 2^V)
    (hunits : span*executionWidth p l target rhsExp < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (tail borrowed suffix packedBorrowed outputTail : List (Fin (A+4)))
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
    (∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107,120,122,125], S.R (plan.gather k) = []) →
    ambientRows.length = Fs.length →
    (∀ row ∈ ambientRows, row.length = span*w) →
    (∀ row ∈ ambientRows, EncodedRange A w q (interiorOutputExponent p l target rhsExp) row) →
    S.R dst = ambientRows.flatten++outputTail →
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.length = Fs.length ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧
      EncodedRange A w q (interiorOutputExponent p l target rhsExp)
        (replicas.flatMap (PublicationReplica.output windows w)) ∧ v'.user = v.user ∧
      n ≤ generatedAccumulatingGatheredReplicaCost p l Fs.length windows.origins.length V span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        generatedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l Fs.length
          windows.origins.length V span L s t u target rhsExp) depth
        (generatedAccumulatingGatheredReplica plan dst hR hQ) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = embStk plan.gather S ∧
      F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R (plan.solver 93) = tail ∧ F.inp = S.inp ∧ F.out = S.out ∧
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
        (fun k => (packedIntervalRead q w origin ((F.R dst).drop (r.val*span*w)) k).re)
        (x r) (1/(2 : ℝ)^target)) ∧
      ∀ r : Fin Fs.length, ∀ (core : Finset (ZMod s)) (old : ZMod s → ℝ) (error : ℝ),
        (∀ k ∈ core, origin ≤ k.val ∧ k.val < origin+span) →
        (∀ k ∈ core, ∀ j : Fin windows.origins.length,
          k.val-origin+1 ≤ windows.origins[j.val]'j.isLt ∨
            (windows.origins[j.val]'j.isLt)+L ≤ k.val-origin) →
        PhaseCellInterface.ErrorOn core
          (fun k => (packedIntervalRead q w origin ((S.R dst).drop (r.val*span*w)) k).re) old error →
        PhaseCellInterface.ErrorOn core
          (fun k => (packedIntervalRead q w origin ((F.R dst).drop (r.val*span*w)) k).re) old error := by
  dsimp only
  intro hC I x hx hint hcell hmax hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas
    hvolume hsource hblank hfresh hNambient hambient hambientRange hdst
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
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
  have hdstM : M.R dst = S.R dst :=
    generatedGatheredReplicaInteriorBatch_preserves_right plan hR hQ dst hgd hsd he₁.toExec
  obtain ⟨v₂,F,n₂,replicas,ha,hinput,hvalid,hu₂,hn₂,he₂,hs₂,hd₂,hi₂,ho₂,hl₂,hframe₂⟩ :=
    accumulatingGatheredPublication_exec_within (body := body) plan dst hgd hsd V w windows hw1
      hwV hcoords hunits ys ambientRows hambient (by simpa only [hNambient,Nat.mul_assoc] using hylen)
      tail outputTail suffix v₁ M hys (hdstM.trans hdst)
      (by rw [hg,hNambient]; exact hreplicas) (by rw [hg]; exact hvolume)
      (by rw [hg]; exact hV) (by rw [hg]; exact hw) (by rw [hg]; exact hLcount)
      (by rw [hg]; exact hpackets) (by rw [hg]; exact hcount)
      (by intro k hk; rw [hg]; exact hblank k hk)
      (by intro k hk; rw [hg]; exact hfresh k hk) depth
  have hnrep : replicas.length = Fs.length := by
    have hh := congrArg List.length ha
    simpa only [List.length_map,hNambient] using hh
  have houtputRange : EncodedRange A w q (interiorOutputExponent p l target rhsExp)
      (replicas.flatMap (PublicationReplica.output windows w)) :=
    publicationReplicas_output_range windows replicas hvalid
      (by
        intro r hr
        apply hambientRange r.ambient
        rw [←ha]
        exact List.mem_map.mpr ⟨r,hr,rfl⟩)
      (by rw [hinput]; exact ys.bounded)
  have hsolver (k : Fin 121) (hk : k ≠ 93) : F.R (plan.solver k) = M.R (plan.solver k) :=
    hframe₂ _ (plan.solver_injective.ne hk) (hsd k)
  have hgatherF : embStk plan.gather F = embStk plan.gather S := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hi₂.trans (congrArg (fun B : Stacks 126 A => B.inp) hgather)
    · exact ho₂.trans (congrArg (fun B : Stacks 126 A => B.out) hgather)
    · funext k
      exact (congrFun hl₂ (plan.gather k)).trans (congrFun (congrArg Stacks.L hgather) k)
    · funext k
      exact (hframe₂ _ (plan.disjoint k 93) (hgd k)).trans (hg k)
  refine ⟨v₂,F,n₁+n₂,replicas,ha,hnrep,hvalid,houtputRange,hu₂.trans hu₁,?_,?_,hgatherF,
    hd₂,hs₂,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [generatedAccumulatingGatheredReplicaCost,hNambient] using Nat.add_le_add hn₁ hn₂
  · have ht := mn_seq_within_add he₁ he₂
    simpa only [generatedAccumulatingGatheredReplica,generatedAccumulatingGatheredReplicaWorkspace,hNambient] using ht
  · exact hi₂.trans (congrArg (fun B : Stacks 126 A => B.inp) hgather)
  · exact ho₂.trans (congrArg (fun B : Stacks 126 A => B.out) hgather)
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
    have hcore : ∀ k ∈ publishedCellCore ((origin+(windows.origins[j.val]'j.isLt) : ℕ) : ZMod s) L,
        origin ≤ k.val ∧ k.val < origin+span := by
      intro k hk
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
      have hiL : i < L := Finset.mem_range.mp hi
      have hfit := windows.fits _ (List.getElem_mem j.isLt)
      have hsum : origin+(windows.origins[j.val]'j.isLt)+i < s := by omega
      have heq : ((origin+(windows.origins[j.val]'j.isLt) : ℕ) : ZMod s)+(i : ZMod s) =
          ((origin+(windows.origins[j.val]'j.isLt)+i : ℕ) : ZMod s) := by simp [Nat.cast_add]
      rw [heq,ZMod.val_natCast,Nat.mod_eq_of_lt hsum]
      omega
    have ht := publicationReplicas_errorOn_suffix windows q w replicas hvalid outputTail rr _ (x r.val)
      (1/(2 : ℝ)^target) hcore he
    simpa only [hd₂,lo,List.getD_eq_getElem _ _ j.isLt] using ht
  · intro r core old error hcore hoff hbefore
    let rr : Fin replicas.length := ⟨r.val,by rw [hnrep]; exact r.isLt⟩
    have hflat : replicas.flatMap PublicationReplica.ambient = ambientRows.flatten := by rw [List.flatMap_def,ha]
    have hb : PhaseCellInterface.ErrorOn core
        (fun k => (packedIntervalRead q w origin
          (((replicas.flatMap PublicationReplica.ambient)++outputTail).drop (rr.val*span*w)) k).re) old error := by
      simpa only [hflat,←hdst] using hbefore
    have ht := publicationReplicas_preserves_errorOn windows q w replicas hvalid outputTail rr
      core old error hcore hoff hb
    simpa only [hd₂] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
