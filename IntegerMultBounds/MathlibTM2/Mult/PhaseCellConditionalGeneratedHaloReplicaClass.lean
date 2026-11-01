module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHaloReplicaClass
public import IntegerMultBounds.MathlibTM2.Host.WhenRightNonempty
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Generate class pages once, inspect their actual count, skip numerical work
for empty candidates, and retire the pages through the same suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def conditionalGeneratedHaloReplicaClass (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (placedPairedLocalHaloClass plan)
    (.seq (whenRightNonempty (plan.gather 116) (repeatableGatheredReplicaClass plan dst hR hQ))
      (releaseGatheredOriginPages plan))

def conditionalGeneratedHaloReplicaClassCost (p l N V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    ((if B = 0 then 3 else repeatableGatheredReplicaClassCost p l N B V span L s t u target rhsExp+2)+
      releasePairedOriginPagesCost B V)

noncomputable def conditionalGeneratedHaloReplicaClassWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  3*preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    ((if B = 0 then 0 else repeatableGatheredReplicaClassWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp)+
      2*releasePairedOriginPagesCost B V)

theorem repeatableGatheredReplicaClass_firstAction (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    FirstAction (peekR (plan.gather 114))
      (repeatableGatheredReplicaClass (P := P) (A := A) (U := U) plan dst hR hQ) := by
  repeat apply FirstAction.seq
  exact FirstAction.act

/-- Reuse the nonempty numerical trace and its exact endpoint. The prefix's
counter fact is supplied by the already proved page-generation contract. -/
theorem conditionalGeneratedHaloReplicaClass_of_nonempty_trace (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)} {n depth bound : ℕ}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (generatedHaloReplicaClass plan dst hR hQ) z n z')
    (hcount : ∀ m state, Exec body (placedPairedLocalHaloClass plan) z m state → state.stk (.rt (plan.gather 116)) ≠ []) :
    ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (conditionalGeneratedHaloReplicaClass plan dst hR hQ) z (n+2) z' := by
  exact guard_middle_exec_within (plan.gather 116) (plan.gather 114)
    (placedPairedLocalHaloClass plan) (repeatableGatheredReplicaClass plan dst hR hQ)
    (releaseGatheredOriginPages plan) (repeatableGatheredReplicaClass_firstAction plan dst hR hQ)
    he (fun state m h => hcount m state h)

/-- The concrete generated-page endpoint discharges the guard premise by
execution uniqueness; the numerical trace and all of its postconditions survive. -/
theorem conditionalGeneratedHaloReplicaClass_of_generated_pages (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (V s t band a b L : ℕ) (S : Stacks T A) (v v₁ : HS T Q A U)
    {z' : Store (HΓ (T := T) A) (HS T Q A U)} {m n depth bound : ℕ}
    (hpages : Exec body (placedPairedLocalHaloClass plan) (mk v S) m
      (mk v₁ (pairedLocalHaloClassBank plan S V s t band a b L)))
    (hne : haloLengthGroup s t band a b L ≠ [])
    (he : ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (generatedHaloReplicaClass plan dst hR hQ) (mk v S) n z') :
    ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (conditionalGeneratedHaloReplicaClass plan dst hR hQ) (mk v S) (n+2) z' := by
  apply conditionalGeneratedHaloReplicaClass_of_nonempty_trace plan dst hR hQ he
  intro steps state hstate
  have hsame := (hpages.unique hstate).2
  rw [← hsame]
  simpa [pairedLocalHaloClassBank] using hne

theorem conditionalGeneratedHaloReplicaClassCost_empty
    (p l N V origin span L s t u target rhsExp : ℕ)
    (hB : haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L = []) :
    conditionalGeneratedHaloReplicaClassCost p l N V origin span L s t u target rhsExp =
      preparedPairedLocalHaloClassCost V s t (PhaseCellBand.width p u) origin (origin+span) L+23 := by
  simp [conditionalGeneratedHaloReplicaClassCost,hB,releasePairedOriginPagesCost]

theorem conditionalGeneratedHaloReplicaClassWorkspace_empty (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ)
    (hB : haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L = []) :
    conditionalGeneratedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp =
      3*preparedPairedLocalHaloClassCost V s t (PhaseCellBand.width p u) origin (origin+span) L+40 := by
  simp [conditionalGeneratedHaloReplicaClassWorkspace,hB,releasePairedOriginPagesCost]

theorem conditionalGeneratedHaloReplicaClassCost_nonempty
    (p l N V origin span L s t u target rhsExp : ℕ)
    (hB : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≠ 0) :
    conditionalGeneratedHaloReplicaClassCost p l N V origin span L s t u target rhsExp =
      generatedHaloReplicaClassCost p l N V origin span L s t u target rhsExp+2 := by
  simp only [conditionalGeneratedHaloReplicaClassCost,generatedHaloReplicaClassCost,hB,ite_false]
  omega

theorem conditionalGeneratedHaloReplicaClassWorkspace_nonempty (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ)
    (hB : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≠ 0) :
    conditionalGeneratedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp =
      generatedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp := by
  simp only [conditionalGeneratedHaloReplicaClassWorkspace,generatedHaloReplicaClassWorkspace,hB,ite_false]

/-- A candidate with no cells performs only shared control work and restores
all tapes, with no numerical-bank, RHS, accuracy or coefficient assumptions. -/
theorem conditionalGeneratedHaloReplicaClass_empty_exec_within (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (V s t band a b L : ℕ) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s)
    (hL : 0 < L) (hLwidth : L < 2^V) (hA : 4 ≤ A)
    (hempty : haloLengthGroup s t band a b L = []) (v : HS T Q A U) (S : Stacks T A)
    (hsSrc : (S.R (plan.gather 97)).length = s) (htSrc : (S.R (plan.gather 98)).length = t)
    (hbSrc : (S.R (plan.gather 100)).length = band) (haSrc : (S.R (plan.gather 111)).length = a)
    (hbEndSrc : (S.R (plan.gather 113)).length = b) (hLSrc : (S.R (plan.gather 102)).length = L)
    (hV : (S.R (plan.gather 115)).length = V)
    (hfresh : ∀ k ∈ [(104 : Fin 126),105,106,116], S.R (plan.gather k) = [])
    (hblank : ∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedPairedLocalHaloClassCost V s t band a b L+23 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*preparedPairedLocalHaloClassCost V s t band a b L+40)) depth
        (conditionalGeneratedHaloReplicaClass plan dst hR hQ) (mk v S) n (mk v' S) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedPairedLocalHaloClass_exec_width (body := body) plan V s t band a b L
    hwide hs hst hband hab hbs hL hLwidth hA v S hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp)) hblank depth
  have hcount : S.R (plan.gather 116) = [] := hfresh _ (by simp)
  have hM : pairedLocalHaloClassBank plan S V s t band a b L = S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = plan.gather 116
    · subst k
      simp [pairedLocalHaloClassBank,hempty,hcount]
    · simp [pairedLocalHaloClassBank,haloOriginPackets,haloPackedOffsets,haloOrigins,
        hempty,hk]
  rw [hM] at he₁
  let v₂ := {v₁ with flag := false}
  have he₂ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
      (whenRightNonempty (plan.gather 116) (repeatableGatheredReplicaClass plan dst hR hQ))
      (mk v₁ S) 3 (mk v₂ S) :=
    whenRightNonempty_empty_within (plan.gather 116) _ (mk v₁ S) depth _ (by rfl) hcount
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseGatheredOriginPages_exec_within (body := body) plan V s t band a b L
    v₂ S S hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp))
    (by rw [hM]) depth
  have hrestore : releasedGatheredOriginPagesBank plan (pairedLocalHaloClassBank plan S V s t band a b L) S = S :=
    pairedLocalHaloClassBank_restore plan S V s t band a b L hcount
  rw [hM] at hrestore
  rw [hrestore] at he₃
  have hn₃' : n₃ ≤ 20 := by simpa [hempty,releasePairedOriginPagesCost] using hn₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+40) depth
      (releaseGatheredOriginPages plan) (mk v₂ S) n₃ (mk v₃ S) := by
    simpa [hempty,releasePairedOriginPagesCost,mnSize] using he₃
  refine ⟨v₃,n₁+(3+n₃),hu₃.trans hu₁,by omega,?_⟩
  refine .seq (he₁.mono ?_) (.seq (he₂.mono ?_) (he₃'.mono ?_))
  all_goals intro d z hz; omega

theorem conditionalGeneratedHaloReplicaClass_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
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
      n ≤ conditionalGeneratedHaloReplicaClassCost p l Fs.length V origin span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        conditionalGeneratedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l Fs.length
          V origin span L s t u target rhsExp) depth
        (conditionalGeneratedHaloReplicaClass plan dst hR hQ) (mk v S) n (mk v' F) ∧
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
  have hgroup : haloLengthGroup s t band origin (origin+span) L ≠ [] := by
    have hn := List.length_pos_iff_ne_nil.mpr hne
    intro hz
    rw [hz] at hB
    simp only [List.length_nil] at hB
    omega
  obtain ⟨v₂,F,n₂,replicas,ha,hnrep,hvalid,hrange,hu₂,hn₂,he₂,hgather,hd,htail,hi,ho,
      hbankF,hcache,hfreshF,herror,hpreserve⟩ :=
    generatedHaloReplicaClass_exec_within (body := body) plan dst hgd hsd hR hQ hA hp hst hband hu hαu hθ hgap hbudget
      hL hLs hpad V origin span windows hwindow Fs ambientRows hne hspan hwV hcoords hunits
      v S tail borrowed packedBorrowed outputTail R K hpushR hpushK depth
      hC I x hx hint hcell hmax hbank hmasters hwidth hOrigin hEnd hcacheFresh hV
      hvolume hsource hblank hfresh hNambient hambient hambientRange hdst
  have he := conditionalGeneratedHaloReplicaClass_of_generated_pages plan dst hR hQ
    V s t band origin (origin+span) L S v v₁ he₁.toExec hgroup he₂
  have hBne : (haloLengthGroup s t band origin (origin+span) L).length ≠ 0 := by
    exact Nat.ne_of_gt (List.length_pos_iff_ne_nil.mpr hgroup)
  refine ⟨v₂,F,n₂+2,replicas,ha,hnrep,hvalid,hrange,hu₂,?_,?_,hgather,hd,htail,hi,ho,
    hbankF,hcache,hfreshF,herror,hpreserve⟩
  · rw [conditionalGeneratedHaloReplicaClassCost_nonempty _ _ _ _ _ _ _ _ _ _ _ _ hBne]
    omega
  · rw [conditionalGeneratedHaloReplicaClassWorkspace_nonempty hQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBne]
    exact he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
