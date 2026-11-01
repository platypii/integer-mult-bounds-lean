module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalGeneratedHaloReplicaClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeUnaryKey
public import IntegerMultBounds.MathlibTM2.Host.CountedLoopStock

/-! Consume one actual binary length key, execute its generated replica class,
then release the unary length header. The remaining key queue survives exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaLengthKeyParser (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  takeUnaryKey (plan.gather 115) (plan.gather 87) (plan.gather 102)
    (plan.gather 0) (plan.gather 1) (plan.gather 2) (plan.gather 3)

noncomputable def processGeneratedHaloReplicaKey (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (replicaLengthKeyParser plan)
    (.seq (conditionalGeneratedHaloReplicaClass plan dst hR hQ) (uclear (plan.gather 102)))

noncomputable def generatedHaloReplicaKeyStep (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  countedStep (plan.gather 119) (processGeneratedHaloReplicaKey plan dst hR hQ)

noncomputable def generatedHaloReplicaKeyLoop (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .loop (·.flag) (generatedHaloReplicaKeyStep plan dst hR hQ)

def replicaLengthKeyParserCost (V L : ℕ) := 6*L+19*V+14

def processGeneratedHaloReplicaKeyCost (p l N V origin span L s t u target rhsExp : ℕ) :=
  replicaLengthKeyParserCost V L+(conditionalGeneratedHaloReplicaClassCost p l N V origin span L s t u target rhsExp+(2*L+2))

noncomputable def processGeneratedHaloReplicaKeyWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ) :=
  2*replicaLengthKeyParserCost V L+
    conditionalGeneratedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp

theorem replicaLengthKeyParser_native (plan : ReplicaInteriorPlacement T) :
    mnNativePushBound 2 (replicaLengthKeyParser (P := P) (Q := Q) (A := A) (U := U) plan) := by
  simp [replicaLengthKeyParser,takeUnaryKey,takeBinaryUnaryKey,takePrefix,transfer,transferAct,
    toUnary,hornerIter,udbl,eachSym,uclear,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,scanR,whileR,peekR,mnNativePushBound,mnActPush]

private theorem headerSources_avoid_key (r : Fin 126 × Fin 117) (hr : r ∈ replicaFactoryHeaderCopies) : r.1 ≠ 87 := by
  have hf : replicaFactoryHeaderCopies.all (fun r => decide (r.1 ≠ 87)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hf r hr)

theorem processGeneratedHaloReplicaKey_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
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
    (tail borrowed packedBorrowed outputTail keyTail : List (Fin (A+4)))
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
    (∀ r ∈ replicaFactoryHeaderCopies, r.1 ≠ 102 → r.1 ≠ 116 → (S.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
        Fs.length 0 0 w r.1) →
    V = weightWorkspaceWidth (2^15*p) q w t u →
    (S.R (plan.gather 111)).length = origin →
    (S.R (plan.gather 113)).length = origin+span →
    (∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = []) →
    (S.R (plan.gather 115)).length = V → L < 2^V →
    S.R (plan.gather 87) = binSyms V L++keyTail →
    (S.R (plan.gather 123)).length = span*w →
    S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++packedBorrowed →
    (∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) →
    (∀ k ∈ [(88 : Fin 126),89,90,91,92,102,103,104,105,106,107,116,120,122,125], S.R (plan.gather k) = []) →
    ambientRows.length = Fs.length →
    (∀ row ∈ ambientRows, row.length = span*w) →
    (∀ row ∈ ambientRows, EncodedRange A w q (interiorOutputExponent p l target rhsExp) row) →
    S.R dst = ambientRows.flatten++outputTail →
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.length = Fs.length ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧
      EncodedRange A w q (interiorOutputExponent p l target rhsExp)
        (replicas.flatMap (PublicationReplica.output windows w)) ∧ v'.user = v.user ∧
      n ≤ processGeneratedHaloReplicaKeyCost p l Fs.length V origin span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        processGeneratedHaloReplicaKeyWorkspace (A := A) (U := U) hQ R K p l Fs.length
          V origin span L s t u target rhsExp) depth
        (processGeneratedHaloReplicaKey plan dst hR hQ) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = {embStk plan.gather S with R :=
        (Function.update (embStk plan.gather S).R 87 keyTail)} ∧
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
  intro hC I x hx hint hcell hmax hbank hmasters hwidth hOrigin hEnd hcacheFresh hV hkey hkeys
    hvolume hsource hblank hfresh hNambient hambient hambientRange hdst
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (plan.gather 87) keyTail)
    (plan.gather 102) (List.replicate L tick))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeUnaryKey_exec (body := body)
    (List.Nodup.map plan.gather_injective (show [(115 : Fin 126),87,102,0,1,2,3].Nodup by decide))
    V L hkey keyTail v S hV hkeys
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact hfresh _ (by simp)
      all_goals exact hblank _ (by decide))
  have he₁' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      2*replicaLengthKeyParserCost V L) depth (replicaLengthKeyParser plan) (mk v S) n₁ (mk v₁ M) :=
    mn_native_exec_within he₁ 2 (replicaLengthKeyParser_native plan) depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn₁) _)
  have hM (k : Fin 126) (h87 : k ≠ 87) (h102 : k ≠ 102) : M.R (plan.gather k) = S.R (plan.gather k) := by
    simp [M,plan.gather_injective.eq_iff,h87,h102]
  have hsolver : embStk plan.solver M = embStk plan.solver S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [M,embStk,(plan.disjoint 87 k).symm,(plan.disjoint 102 k).symm]
  have hs (k : Fin 121) : M.R (plan.solver k) = S.R (plan.solver k) := congrFun (congrArg Stacks.R hsolver) k
  have hd : M.R dst = S.R dst := by simp [M,(hgd 87).symm,(hgd 102).symm]
  have hmastersM : ∀ r ∈ replicaFactoryHeaderCopies, r.1 ≠ 116 → (M.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u
        (PhaseCellBand.width p u) Fs.length windows.origins.length L w r.1 := by
    intro r hr h116
    by_cases h102 : r.1 = 102
    · simp [M,h102,replicaFactoryHeaderValue]
    · rw [hM r.1 (headerSources_avoid_key r hr) h102]
      have hv102 : r.1.val ≠ 102 := fun he => h102 (Fin.ext he)
      have hv116 : r.1.val ≠ 116 := fun he => h116 (Fin.ext he)
      simpa only [replicaFactoryHeaderValue,hv102,hv116,ite_false] using hmasters r hr h102 h116
  obtain ⟨v₂,F,n₂,replicas,ha,hnrep,hvalid,hrange,hu₂,hn₂,he₂,hgather,hd₂,htail,hi₂,ho₂,
      hlow,hcache,hsolverFresh,herror,hpreserve⟩ :=
    conditionalGeneratedHaloReplicaClass_exec_within (body := body) plan dst hgd hsd hR hQ hA hp hst hband hu hαu hθ hgap hbudget
      hL hLs hpad V origin span windows hwindow Fs ambientRows hne hspan hwV hcoords hunits
      v₁ M tail borrowed packedBorrowed outputTail R K hpushR hpushK depth
      hC I x hx hint hcell hmax (by rw [hsolver]; exact hbank) hmastersM hwidth
      (by rw [hM 111 (by decide) (by decide)]; exact hOrigin)
      (by rw [hM 113 (by decide) (by decide)]; exact hEnd)
      (by intro k hk; rw [hs]; exact hcacheFresh k hk)
      (by rw [hM 115 (by decide) (by decide)]; exact hV)
      (by rw [hM 123 (by decide) (by decide)]; exact hvolume)
      (by rw [hM 124 (by decide) (by decide)]; exact hsource)
      (by
        intro k hk
        rw [hM k (by intro he; subst k; norm_num at hk) (by intro he; subst k; norm_num at hk)]
        exact hblank k hk)
      (by
        intro k hk
        have h87 : k ≠ 87 := by intro he; subst k; norm_num at hk
        have h102 : k ≠ 102 := by intro he; subst k; norm_num at hk
        rw [hM k h87 h102]
        have hsub : [(88 : Fin 126),89,90,91,92,103,104,105,106,107,116,120,122,125].Sublist
            [88,89,90,91,92,102,103,104,105,106,107,116,120,122,125] := by decide +kernel
        exact hfresh k (hsub.subset hk))
      hNambient hambient hambientRange (hd.trans hdst)
  have h102 : (F.R (plan.gather 102)).length = L := by
    have hh := congrFun (congrArg Stacks.R hgather) 102
    simpa [embStk,M] using congrArg List.length hh
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (plan.gather 102) v₂ F
  let G : Stacks T A := {F with R := Function.update F.R (plan.gather 102) []}
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ F)+depth+0) depth
      (uclear (plan.gather 102)) (mk v₂ F) (2*L+2) (mk v₃ G) := by
    rw [h102] at he₃
    exact mn_native_exec_within he₃ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
      depth _ (by omega)
  have hOut : G.R dst = F.R dst := by simp [G,(hgd 102).symm]
  have hGsolver : embStk plan.solver G = embStk plan.solver F := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [G,embStk,(plan.disjoint 102 k).symm]
  have hGs (k : Fin 121) : G.R (plan.solver k) = F.R (plan.solver k) := congrFun (congrArg Stacks.R hGsolver) k
  have hgatherG : embStk plan.gather G = {embStk plan.gather S with R := Function.update (embStk plan.gather S).R 87 keyTail} := by
    rw [embStk_updateR plan.gather_injective,hgather]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 102
    · subst k; simp [embStk,hfresh 102 (by simp)]
    · simp [M,embStk,Function.update_apply,plan.gather_injective.eq_iff,hk]
  refine ⟨v₃,G,n₁+(n₂+(2*L+2)),replicas,ha,hnrep,hvalid,hrange,hu₃.trans (hu₂.trans hu₁),?_,?_,
    hgatherG,hOut.trans hd₂,?_,hi₂,ho₂,?_,?_,?_,?_,?_⟩
  · exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · have hsize₁ := he₁'.final
    have hsize₂ := he₂.final
    change ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      (2*replicaLengthKeyParserCost V L+
        conditionalGeneratedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l Fs.length V origin span L s t u target rhsExp))
      depth (.seq (replicaLengthKeyParser plan) (.seq (conditionalGeneratedHaloReplicaClass plan dst hR hQ)
        (uclear (plan.gather 102)))) (mk v S) (n₁+(n₂+(2*L+2))) (mk v₃ G)
    refine .seq (he₁'.mono ?_) (.seq (he₂.mono ?_) (he₃'.mono ?_))
    all_goals intro d z hz; omega
  · rw [hGs]; exact htail
  · rw [hGsolver]; exact hlow
  · rw [hGs,hcache,hs]
  · intro k hk; rw [hGs]; exact hsolverFresh k hk
  · simpa only [hOut] using herror
  · simpa only [hOut,hd] using hpreserve

/-- Empty candidates consume their actual binary key and restore every other
stack. No numerical input or solver hypotheses are needed on this path. -/
theorem processGeneratedHaloReplicaKey_empty_exec_within (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (V s t band a b L : ℕ) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s)
    (hL : 0 < L) (hkey : L < 2^V) (hA : 4 ≤ A)
    (hempty : haloLengthGroup s t band a b L = []) (v : HS T Q A U) (S : Stacks T A)
    (keyTail : List (Fin (A+4)))
    (hsSrc : (S.R (plan.gather 97)).length = s) (htSrc : (S.R (plan.gather 98)).length = t)
    (hbSrc : (S.R (plan.gather 100)).length = band) (haSrc : (S.R (plan.gather 111)).length = a)
    (hbEndSrc : (S.R (plan.gather 113)).length = b) (hV : (S.R (plan.gather 115)).length = V)
    (hkeys : S.R (plan.gather 87) = binSyms V L++keyTail)
    (hfresh : ∀ k ∈ [(102 : Fin 126),104,105,106,116], S.R (plan.gather k) = [])
    (hblank : ∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ replicaLengthKeyParserCost V L+(preparedPairedLocalHaloClassCost V s t band a b L+23+(2*L+2)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*replicaLengthKeyParserCost V L+3*preparedPairedLocalHaloClassCost V s t band a b L+40)) depth
        (processGeneratedHaloReplicaKey plan dst hR hQ) (mk v S) n
        (mk v' {S with R := Function.update S.R (plan.gather 87) keyTail}) := by
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (plan.gather 87) keyTail)
    (plan.gather 102) (List.replicate L tick))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeUnaryKey_exec (body := body)
    (List.Nodup.map plan.gather_injective (show [(115 : Fin 126),87,102,0,1,2,3].Nodup by decide))
    V L hkey keyTail v S hV hkeys
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact hfresh _ (by simp)
      all_goals exact hblank _ (by decide))
  have he₁' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      2*replicaLengthKeyParserCost V L) depth (replicaLengthKeyParser plan) (mk v S) n₁ (mk v₁ M) :=
    mn_native_exec_within he₁ 2 (replicaLengthKeyParser_native plan) depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn₁) _)
  have hM (k : Fin 126) (h87 : k ≠ 87) (h102 : k ≠ 102) : M.R (plan.gather k) = S.R (plan.gather k) := by
    simp [M,plan.gather_injective.eq_iff,h87,h102]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := conditionalGeneratedHaloReplicaClass_empty_exec_within (body := body)
    plan dst hR hQ V s t band a b L hwide hs hst hband hab hbs hL hkey hA hempty v₁ M
    (by rw [hM 97 (by decide) (by decide)]; exact hsSrc)
    (by rw [hM 98 (by decide) (by decide)]; exact htSrc)
    (by rw [hM 100 (by decide) (by decide)]; exact hbSrc)
    (by rw [hM 111 (by decide) (by decide)]; exact haSrc)
    (by rw [hM 113 (by decide) (by decide)]; exact hbEndSrc)
    (by simp [M])
    (by rw [hM 115 (by decide) (by decide)]; exact hV)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        (rw [hM _ (by decide) (by decide)]; exact hfresh _ (by simp)))
    (by
      intro k hk
      rw [hM k (by intro he; subst k; norm_num at hk) (by intro he; subst k; norm_num at hk)]
      exact hblank k hk) depth
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (plan.gather 102) v₂ M
  let G : Stacks T A := {S with R := Function.update S.R (plan.gather 87) keyTail}
  have hrestore : {M with R := Function.update M.R (plan.gather 102) []} = G := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = plan.gather 102
    · subst k
      simp [G,plan.gather_injective.eq_iff,hfresh 102 (by simp)]
    · simp [M,G,hk,Function.update_apply]
  have h102 : (M.R (plan.gather 102)).length = L := by simp [M]
  rw [h102,hrestore] at he₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ M)+depth+0) depth
      (uclear (plan.gather 102)) (mk v₂ M) (2*L+2) (mk v₃ G) :=
    mn_native_exec_within he₃ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
      depth _ (by omega)
  change n₁ ≤ replicaLengthKeyParserCost V L at hn₁
  refine ⟨v₃,n₁+(n₂+(2*L+2)),hu₃.trans (hu₂.trans hu₁),by omega,?_⟩
  have hsize₁ := he₁'.final
  change mnSize (mk v₂ M)+depth ≤ mnSize (mk v S)+depth+2*replicaLengthKeyParserCost V L at hsize₁
  refine .seq (he₁'.mono ?_) (.seq (he₂.mono ?_) (he₃'.mono ?_))
  · intro d z hz; omega
  · intro d z hz
    change mnSize z+d ≤ mnSize (mk v₂ M)+depth+(3*preparedPairedLocalHaloClassCost V s t band a b L+40) at hz
    omega
  · intro d z hz; omega

/-- Instantiate the structural counted loop with the real key-processing body.
The concrete replica accuracy/metadata invariant must discharge `hstep`. -/
theorem generatedHaloReplicaKeyLoop_of_invariant (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (Inv : List ℕ → Stacks T A → Prop) (cost workspace : ℕ → ℕ) (depth : ℕ)
    (hcount : ∀ keys S, Inv keys S → S.R (plan.gather 119) = List.replicate keys.length tick)
    (hstep : ∀ L keys (v : HS T Q A U) S, Inv (L::keys) S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost L ∧ Inv keys F ∧
        ExecWithin body (fun d z => mnSize z+d ≤
          mnSize (mk v {S with R := Function.update S.R (plan.gather 119) (List.replicate keys.length tick)})+
            depth+workspace L) depth (processGeneratedHaloReplicaKey plan dst hR hQ)
          (mk v {S with R := Function.update S.R (plan.gather 119) (List.replicate keys.length tick)}) n (mk v' F))
    (keys : List ℕ) (v : HS T Q A U) (S : Stacks T A) (hInv : Inv keys S)
    (hflag : v.flag = keys.head?.isSome) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (keys.map (fun L => cost L+3)).sum+1 ∧ Inv [] F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(keys.map workspace).sum)
        depth (generatedHaloReplicaKeyLoop plan dst hR hQ) (mk v S) n (mk v' F) :=
  countedLoop_body_exec_within (plan.gather 119) (processGeneratedHaloReplicaKey plan dst hR hQ)
    Inv cost workspace depth hcount hstep keys v S hInv hflag

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
