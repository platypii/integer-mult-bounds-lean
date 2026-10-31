module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatableGatheredReplicaClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseGatheredOriginPages
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassPublicationWindows

/-! Generate a halo class from ordinary geometry, solve and accumulate it, then
retire both numerical and coordinate ownership. Both bank ABIs are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def generatedHaloReplicaClass (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (placedPairedLocalHaloClass plan)
    (.seq (repeatableGatheredReplicaClass plan dst hR hQ) (releaseGatheredOriginPages plan))

def generatedHaloReplicaClassCost (p l N V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    (repeatableGatheredReplicaClassCost p l N B V span L s t u target rhsExp+releasePairedOriginPagesCost B V)

noncomputable def generatedHaloReplicaClassWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  3*preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    (repeatableGatheredReplicaClassWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp+
      2*releasePairedOriginPagesCost B V)

private theorem headerSources_avoid_pages (r : Fin 126 × Fin 117) (hr : r ∈ replicaFactoryHeaderCopies) :
    r.1 ≠ 109 ∧ r.1 ≠ 113 := by
  have hf : replicaFactoryHeaderCopies.all (fun r => decide (r.1 ≠ 109 ∧ r.1 ≠ 113)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hf r hr)

theorem generatedHaloReplicaClass_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hband : PhaseCellBand.width p u ≤ s) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (V origin span : ℕ) (windows : PublicationWindows span L)
    (hwindow : windows.origins = haloPackedOffsets s t (PhaseCellBand.width p u) origin (origin+span) L)
    (Fs : List (ZMod s → GaussianInt))
    (ambientRows : List (List (Fin (A+4))))
    (hne : windows.origins ≠ []) (hspan : origin+span ≤ s)
    (hwV : executionWidth p l target rhsExp < 2^V) (hcoords : span < 2^V)
    (hunits : span*executionWidth p l target rhsExp < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (tail borrowed packedBorrowed outputTail : List (Fin (A+4)))
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
    (∀ r ∈ replicaFactoryHeaderCopies, r.1 ≠ 116 → (S.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
        Fs.length windows.origins.length L w r.1) →
    V = weightWorkspaceWidth (2^15*p) q w t u →
    (S.R (plan.gather 111)).length = origin →
    (S.R (plan.gather 113)).length = origin+span →
    (∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = []) →
    (S.R (plan.gather 115)).length = V →
    (S.R (plan.gather 123)).length = span*w →
    S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++packedBorrowed →
    (∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) →
    (∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107,116,120,122,125], S.R (plan.gather k) = []) →
    ambientRows.length = Fs.length →
    (∀ row ∈ ambientRows, row.length = span*w) →
    (∀ row ∈ ambientRows, EncodedRange A w q (interiorOutputExponent p l target rhsExp) row) →
    S.R dst = ambientRows.flatten++outputTail →
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.length = Fs.length ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧
      EncodedRange A w q (interiorOutputExponent p l target rhsExp)
        (replicas.flatMap (PublicationReplica.output windows w)) ∧ v'.user = v.user ∧
      n ≤ generatedHaloReplicaClassCost p l Fs.length V origin span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        generatedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l Fs.length
          V origin span L s t u target rhsExp) depth
        (generatedHaloReplicaClass plan dst hR hQ) (mk v S) n (mk v' F) ∧
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
  intro hC I x hx hint hcell hmax hbank hmasters hwidth hOrigin hEnd hcacheFresh hV
    hvolume hsource hblank hfresh hNambient hambient hambientRange hdst
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
  have hB : windows.origins.length = (haloLengthGroup s t band origin (origin+span) L).length := by
    rw [hwindow,haloPackedOffsets_length]
  have h97 : (S.R (plan.gather 97)).length = s := by
    simpa [replicaFactoryHeaderValue] using hmasters (97,97) (by simp [replicaFactoryHeaderCopies]) (by decide)
  have h98 : (S.R (plan.gather 98)).length = t := by
    simpa [replicaFactoryHeaderValue] using hmasters (98,98) (by simp [replicaFactoryHeaderCopies]) (by decide)
  have h100 : (S.R (plan.gather 100)).length = band := by
    simpa [replicaFactoryHeaderValue] using hmasters (100,100) (by simp [replicaFactoryHeaderCopies]) (by decide)
  have h102 : (S.R (plan.gather 102)).length = L := by
    simpa [replicaFactoryHeaderValue] using hmasters (102,102) (by simp [replicaFactoryHeaderCopies]) (by decide)
  have h94 : (S.R (plan.gather 94)).length = w := by
    simpa [replicaFactoryHeaderValue] using hmasters (94,94) (by simp [replicaFactoryHeaderCopies]) (by decide)
  have h121 : (S.R (plan.gather 121)).length = Fs.length := by
    simpa [replicaFactoryHeaderValue] using hmasters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide)
  have hwide : 8*(t+1)^2+2*band+8 < 2^V := by
    rw [hwidth]
    exact (weightWorkspaceWidth_control (q := q) (w := w)
      (by norm_num; omega : 13 ≤ 2^15*p) (NeZero.pos s) hst hu hband).1
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedPairedLocalHaloClass_exec_within (body := body) plan
    V s t band origin (origin+span) L hwide (NeZero.pos s) hst hband (by omega) hspan hL hLs (by omega)
    v S h97 h98 h100 hOrigin hEnd h102 hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp)) hblank depth
  let M := pairedLocalHaloClassBank plan S V s t band origin (origin+span) L
  have hM (k : Fin 126) (h109 : k ≠ 109) (h113 : k ≠ 113) (h116 : k ≠ 116) :
      M.R (plan.gather k) = S.R (plan.gather k) := by
    simp [M,pairedLocalHaloClassBank,plan.gather_injective.eq_iff,h109,h113,h116]
  have hsolver : embStk plan.solver M = embStk plan.solver S := pairedLocalHaloClassBank_solver plan S V s t band origin (origin+span) L
  have hs (k : Fin 121) : M.R (plan.solver k) = S.R (plan.solver k) :=
    congrFun (congrArg Stacks.R hsolver) k
  have hd : M.R dst = S.R dst := by
    simp [M,pairedLocalHaloClassBank,(hgd 109).symm,(hgd 113).symm,(hgd 116).symm]
  have hmastersM : ∀ r ∈ replicaFactoryHeaderCopies, (M.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u band
        Fs.length windows.origins.length L w r.1 := by
    intro r hr
    by_cases h116 : r.1 = 116
    · simp [M,pairedLocalHaloClassBank,h116,replicaFactoryHeaderValue,hB]
    · obtain ⟨h109,h113⟩ := headerSources_avoid_pages r hr
      rw [hM r.1 h109 h113 h116]
      exact hmasters r hr h116
  have hpage : M.R (plan.gather 113) = (List.range windows.origins.length).flatMap
      (fun j => binSyms V (lo j).val)++S.R (plan.gather 113) := by
    have hh := haloClassPublicationWindows_ambient_packets (A := A) (s := s) V t band origin (origin+span) L hL
    dsimp only [haloClassPublicationWindows] at hh
    rw [←hwindow] at hh
    rw [hh]
    simp [M,pairedLocalHaloClassBank,plan.gather_injective.eq_iff]
  obtain ⟨v₂,F,n₂,replicas,ha,hnrep,hvalid,hrange,hu₂,hn₂,he₂,hgather,hd₂,htail,hi₂,ho₂,
      hlow,hcache,hsolverFresh,herror,hpreserve⟩ :=
    repeatableGatheredReplicaClass_exec_within (body := body) plan dst hgd hsd hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad V origin span windows Fs ambientRows hne hspan hwV hcoords hunits
      v₁ M tail borrowed (S.R (plan.gather 109)) (S.R (plan.gather 113)) packedBorrowed outputTail
      R K hpushR hpushK depth hC I x hx hint hcell hmax
      (by rw [hsolver]; exact hbank) hmastersM hwidth hpage
      (by intro k hk; rw [hs]; exact hcacheFresh k hk)
      (by rw [hM 115 (by decide) (by decide) (by decide)]; exact hV)
      (by rw [hM 94 (by decide) (by decide) (by decide)]; exact h94)
      (by rw [hM 102 (by decide) (by decide) (by decide)]; exact h102)
      (by simp [M,pairedLocalHaloClassBank,plan.gather_injective.eq_iff,hwindow,band])
      (by simp [M,pairedLocalHaloClassBank,hB])
      (by rw [hM 121 (by decide) (by decide) (by decide)]; exact h121)
      (by rw [hM 123 (by decide) (by decide) (by decide)]; exact hvolume)
      (by rw [hM 124 (by decide) (by decide) (by decide)]; exact hsource)
      (by
        intro k hk
        rw [hM k (by intro he; subst k; norm_num at hk) (by intro he; subst k; norm_num at hk)
          (by intro he; subst k; norm_num at hk)]
        exact hblank k (by omega))
      (by
        intro k hk
        have h109 : k ≠ 109 := by simp_all only [List.mem_cons,List.not_mem_nil,or_false]; omega
        have h113 : k ≠ 113 := by simp_all only [List.mem_cons,List.not_mem_nil,or_false]; omega
        have h116 : k ≠ 116 := by simp_all only [List.mem_cons,List.not_mem_nil,or_false]; omega
        rw [hM k h109 h113 h116]
        exact hfresh k (by simp_all))
      hNambient hambient hambientRange (hd.trans hdst)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseGatheredOriginPages_exec_within (body := body) plan
    V s t band origin (origin+span) L v₂ F S hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp)) hgather depth
  let G := releasedGatheredOriginPagesBank plan F S
  have hOut : G.R dst = F.R dst := by
    simp [G,releasedGatheredOriginPagesBank,(hgd 113).symm,(hgd 109).symm,(hgd 116).symm]
  have hGsolver : embStk plan.solver G = embStk plan.solver F := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [G,releasedGatheredOriginPagesBank,embStk,(plan.disjoint 113 k).symm,
      (plan.disjoint 109 k).symm,(plan.disjoint 116 k).symm]
  have hGs (k : Fin 121) : G.R (plan.solver k) = F.R (plan.solver k) :=
    congrFun (congrArg Stacks.R hGsolver) k
  refine ⟨v₃,G,n₁+(n₂+n₃),replicas,ha,hnrep,hvalid,hrange,hu₃.trans (hu₂.trans hu₁),?_,?_,
    releasedGatheredOriginPagesBank_gather plan F S V s t band origin (origin+span) L
      (hfresh 116 (by simp)) hgather,hOut.trans hd₂,?_,hi₂,ho₂,?_,?_,?_,?_,?_⟩
  · simpa only [generatedHaloReplicaClassCost,hB,band] using Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hn₃)
  · simpa only [generatedHaloReplicaClass,generatedHaloReplicaClassWorkspace,hB,band] using
      mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
  · rw [hGs]; exact htail
  · rw [hGsolver]; exact hlow
  · rw [hGs,hcache,hs]
  · intro k hk; rw [hGs]; exact hsolverFresh k hk
  · simpa only [hOut] using herror
  · simpa only [hOut,hd] using hpreserve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
