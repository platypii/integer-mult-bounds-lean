module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaFactoryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedAccumulatingGatheredReplica

/-! A repeatable length-class operation: reload, solve, accumulate and retire.
Its numerical entry and exit banks agree; retained gather metadata survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def repeatableGatheredReplicaClass (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (reloadReplicaFactoryInput plan) (releasedAccumulatingGatheredReplica plan dst hR hQ)

def replicaClassReloadCost (p l N B L s t u target rhsExp : ℕ) :=
  reloadReplicaFactoryInputCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) N B L
    (executionWidth p l target rhsExp)

def repeatableGatheredReplicaClassCost (p l N B V span L s t u target rhsExp : ℕ) :=
  replicaClassReloadCost p l N B L s t u target rhsExp +
    releasedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp

noncomputable def repeatableGatheredReplicaClassWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp : ℕ) :=
  2*replicaClassReloadCost p l N B L s t u target rhsExp +
    releasedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp

theorem repeatableGatheredReplicaClass_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
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
    embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] borrowed tail S.inp S.out →
    (∀ r ∈ replicaFactoryHeaderCopies, (S.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
        Fs.length windows.origins.length L w r.1) →
    V = weightWorkspaceWidth (2^15*p) q w t u →
    S.R (plan.gather 113) = (List.range windows.origins.length).flatMap
      (fun j => binSyms V (lo j).val) ++ suffix →
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
      n ≤ repeatableGatheredReplicaClassCost p l Fs.length windows.origins.length V span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        repeatableGatheredReplicaClassWorkspace (A := A) (U := U) hQ R K p l Fs.length
          windows.origins.length V span L s t u target rhsExp) depth
        (repeatableGatheredReplicaClass plan dst hR hQ) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = embStk plan.gather S ∧
      F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R (plan.solver 93) = tail ∧ F.inp = S.inp ∧ F.out = S.out ∧
      embStk weightCacheCoreReg (embStk plan.solver F) = releasedCellBank [] borrowed tail S.inp S.out ∧
      F.R (plan.solver 117) = S.R (plan.solver 117) ∧
      (∀ k ∈ [(118 : Fin 121),119,120], F.R (plan.solver k) = []) ∧
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
  intro hC I x hx hint hcell hmax hbank hmasters hwidth hpage hcacheFresh hV hw hLcount
    hpackets hcount hreplicas hvolume hsource hblank hfresh hNambient hambient hambientRange hdst
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hfactory,hgather,hi₁,ho₁,hl₁,hframe⟩ :=
    reloadReplicaFactoryInput_exec_within (body := body) plan (2^15*p)
      (executionStagePrecision p l target rhsExp+1) q l s t u (PhaseCellBand.width p u)
      Fs.length windows.origins.length L w
      (by dsimp [w,q,executionWidth,executionPrecision]; omega) (fun j => (lo j).val)
      borrowed tail suffix v S hbank hmasters
      (hV.trans hwidth)
      (by simpa only [hwidth] using hpage)
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        · exact hblank _ (by decide)
        all_goals exact hfresh _ (by simp)) depth
  have hg (k : Fin 126) : M.R (plan.gather k) = S.R (plan.gather k) :=
    congrFun (congrArg Stacks.R hgather) k
  have hs (k : Fin 121) (hk : ∀ r ∈ replicaFactoryHeaderCopies,
      weightCacheCoreReg r.2 ≠ k) : M.R (plan.solver k) = S.R (plan.solver k) :=
    hframe _ (fun r hr => plan.solver_injective.ne (hk r hr))
  have hd : M.R dst = S.R dst := hframe _ (fun r _ => hsd _)
  have hhigh (k : Fin 121) (hk : 117 ≤ k.val) : M.R (plan.solver k) = S.R (plan.solver k) := by
    apply hs
    intro r _ he
    have hh := congrArg Fin.val he
    have hbound := r.2.isLt
    change r.2.val = k.val at hh
    omega
  have h117 : M.R (plan.solver 117) = S.R (plan.solver 117) := hhigh _ (by decide)
  have hcache : ∀ k ∈ [(118 : Fin 121),119,120], M.R (plan.solver k) = [] := by
    intro k hk
    have hbound : 117 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide
    rw [hhigh k hbound]
    exact hcacheFresh k hk
  obtain ⟨v₂,F,n₂,replicas,ha,hnrep,hvalid,hrange,hu₂,hn₂,he₂,hgather₂,hd₂,htail,hi₂,ho₂,
      hlow,hcache₂,hfresh₂,herror,hpreserve⟩ :=
    releasedAccumulatingGatheredReplica_exec_within (body := body) plan dst hgd hsd hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad V origin span windows Fs ambientRows hne hspan hwV hcoords hunits
      v₁ M tail borrowed suffix packedBorrowed outputTail S.inp S.out R K hpushR hpushK depth
      hC I x hx hint hcell hmax
      (by simpa only [hi₁,ho₁] using hfactory) hcache
      (by rw [hg]; exact hV) (by rw [hg]; exact hw) (by rw [hg]; exact hLcount)
      (by rw [hg]; exact hpackets) (by rw [hg]; exact hcount) (by rw [hg]; exact hreplicas)
      (by rw [hg]; exact hvolume) (by rw [hg]; exact hsource)
      (by intro k hk; rw [hg]; exact hblank k hk)
      (by intro k hk; rw [hg]; exact hfresh k hk)
      hNambient hambient hambientRange (hd.trans hdst)
  refine ⟨v₂,F,n₁+n₂,replicas,ha,hnrep,hvalid,hrange,hu₂.trans hu₁,?_,?_,
    hgather₂.trans hgather,hd₂,htail,hi₂.trans hi₁,ho₂.trans ho₁,?_,hcache₂.trans h117,hfresh₂,herror,?_⟩
  · exact Nat.add_le_add hn₁ hn₂
  · simpa only [repeatableGatheredReplicaClass,repeatableGatheredReplicaClassWorkspace,
      replicaClassReloadCost,q,w] using mn_seq_within_add he₁ he₂
  · simpa only [hi₁,ho₁] using hlow
  · simpa only [hd] using hpreserve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
