module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicFactorInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallMasterHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems

/-! Reuse the ten-master installer for cyclic factor seeds. No arithmetic
readiness or generated boundary page is supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicFactorMasterValues (p l s t u target a n : ℕ) [NeZero s] : Fin 10 → ℕ :=
  let stage := initialSchurTarget p u (boundaryTableBits p target 2
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2
  masterHeaderValues (2^15*p) (executionStagePrecision p l stage 2+1)
    (executionPrecision p l stage 2) l s t u (PhaseCellBand.width p u) a n

/-- The actual joint-target left problem has exactly the factor's master
parameters; this alignment needs no numerical or resource hypothesis. -/
theorem RecoveryAxisBounds.cyclicLeftReplicaProblem_factorSeedValues
    {p l s t u : ℕ} [NeZero s] {α d : ℝ} (axis : RecoveryAxisBounds s t p u l α d)
    (target a n : ℕ) (ha : a < s) :
    let stage := initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value (executionPrecision p l stage 2) (F i)‖ ≤ (2 : ℝ)^2),
      let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF
      masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin n =
        cyclicFactorMasterValues p l s t u target a n := by
  dsimp only
  intro Fs hF
  rfl

/-- Nine words are retained cached headers; the interval span is ordinary
caller metadata because the cached archive stores its volume instead. -/
def cachedFactorSeedSource (gather : Fin 126 → Fin T) (span : Fin T) : Fin 10 → Fin T :=
  ![gather 114,gather 101,gather 112,gather 108,gather 97,gather 98,gather 99,gather 100,gather 111,span]

theorem ReplicaLoopHeaders.factorSeedSources {s : ℕ} {H : ReplicaHaloProblem s}
    {gather : Fin 126 → Fin T} {buffers : ReplicaLoopBuffers A} {S : Stacks T A}
    (h : ReplicaLoopHeaders H gather buffers S) (span : Fin T) (n : ℕ)
    (hspan : (S.R span).length = n) :
    ∀ i, (S.R (cachedFactorSeedSource gather span i)).length =
      masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin n i := by
  intro i
  fin_cases i
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (114,114) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (101,101) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (112,112) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (108,109) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (97,97) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (98,98) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (99,99) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues,replicaFactoryHeaderValue] using
      h.masters (100,100) (by decide) (by decide) (by decide)
  · simpa [cachedFactorSeedSource,masterHeaderValues] using h.origin
  · simpa [cachedFactorSeedSource,masterHeaderValues] using hspan

def installCyclicFactorSeeds (factor : Fin 234 → Fin T) (source : Fin 10 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  copyUnaryHeaders tmp (masterHeaderCopies (factor ∘ Fin.castLE (by decide : 224 ≤ 234)) source)

theorem installCyclicFactorSeeds_exec {p l s t u target a n : ℕ} [NeZero s]
    (factor : Fin 234 → Fin T) (hfactor : Function.Injective factor)
    (source : Fin 10 → Fin T) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ factor j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hfactorTmp : ∀ i, factor i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = cyclicFactorMasterValues p l s t u target a n i)
    (hblank : ∀ i, S.R (factor i) = []) (hleft : ∀ i, S.L (factor i) = []) (htmp : S.R tmp = []) :
    let rs := masterHeaderCopies (factor ∘ Fin.castLE (by decide : 224 ≤ 234)) source
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    ∃ v' G, v'.user = v.user ∧
      Exec body (installCyclicFactorSeeds factor source tmp) (mk v S) cost (mk v' G) ∧
      CyclicFactorSeedInput p l s t u target a n [] (embStk factor G) ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, (∀ i, factor i ≠ k) → G.R k = S.R k) := by
  dsimp only
  let e := Fin.castLE (by decide : 224 ≤ 234)
  let work := factor ∘ e
  let values := cyclicFactorMasterValues p l s t u target a n
  let rs := masterHeaderCopies work source
  let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
  dsimp only [cyclicFactorMasterValues] at hvalues
  obtain ⟨v',hu,hview,hready,hex⟩ := installMasterHeaderBank_exec (body := body) work
    (hfactor.comp (Fin.castLE_injective _)) source tmp (fun i j => hsourceOff i _)
    hsourceTmp (fun i => hfactorTmp _) _ _ _ l s t u (PhaseCellBand.width p u) a n v S
    hvalues (fun i => hblank _) (fun i => hleft _) htmp 0
  have hoff (k : Fin T) (hk : ∀ i, factor i ≠ k) : F.R k = S.R k := by
    apply unaryCopiesR_off
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact hk _
  have hheaders (i : Fin 10) : F.R (work (inverseMasterCorePort i)) = List.replicate (values i) tick := by
    exact (congrArg (fun B : Stacks 224 A => B.R (inverseMasterCorePort i)) hview).trans
      (masterHeaderBank_headers values [] i)
  have hcoreOff (k : Fin 234) (hk : k.val < 224)
      (hports : ∀ i, (inverseMasterCorePort i).val ≠ k.val) : F.R (factor k) = [] := by
    let j : Fin 224 := ⟨k.val,hk⟩
    have hh := congrArg (fun B : Stacks 224 A => B.R j) hview
    have hp : ∀ i, inverseMasterCorePort i ≠ j := fun i he => hports i (congrArg Fin.val he)
    exact hh.trans (by
      change (masterHeaderBank values []).R j = []
      rw [masterHeaderBank_off values [] j hp]
      split_ifs <;> rfl)
  have hhigh (k : Fin 234) (hk : 224 ≤ k.val) : F.R (factor k) = [] := by
    change unaryCopiesR (fun k => (S.R k).length) S.R rs (factor k) = []
    rw [unaryCopiesR_off _ _ _ _ ?_,hblank]
    intro r hr he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    have hv := congrArg Fin.val (hfactor he)
    change (inverseMasterCorePort i).val = k.val at hv
    have := (inverseMasterCorePort i).isLt
    omega
  refine ⟨v',F,hu,hex.toExec,?_,rfl,rfl,rfl,hoff⟩
  constructor
  · simpa [embStk_R,values,cyclicFactorMasterValues,masterHeaderValues,inverseMasterCorePort,work,e] using congrArg List.length (hheaders 4)
  · simpa [embStk_R,values,cyclicFactorMasterValues,masterHeaderValues,inverseMasterCorePort,work,e] using congrArg List.length (hheaders 5)
  · simpa [embStk_R,values,cyclicFactorMasterValues,masterHeaderValues,inverseMasterCorePort,work,e] using congrArg List.length (hheaders 7)
  · simpa [embStk_R,values,cyclicFactorMasterValues,masterHeaderValues,inverseMasterCorePort,work,e] using congrArg List.length (hheaders 8)
  · simpa [embStk_R,values,cyclicFactorMasterValues,masterHeaderValues,inverseMasterCorePort,work,e] using congrArg List.length (hheaders 9)
  · intro k hk
    apply hcoreOff k
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro i he
      have hh : ∀ i : Fin 10, (inverseMasterCorePort i).val ∉
          ([106,108,109,115,116,127,135,138,139,143,144,145,146,147,151,152,153] : List ℕ) := by decide +kernel
      apply hh i
      rw [he]
      simpa [Fin.ext_iff] using hk
  · intro k hk
    apply hcoreOff k (by omega)
    intro i he
    have hb : ∀ i : Fin 10, 117 ≤ (inverseMasterCorePort i).val := by decide +kernel
    have := hb i
    omega
  · intro k; exact hleft _
  · intro k hk
    by_cases h224 : k.val < 224
    · apply hcoreOff k h224
      intro i he
      have hb : ∀ i : Fin 10, (inverseMasterCorePort i).val < 154 := by decide +kernel
      have := hb i
      omega
    · exact hhigh k (by omega)
  · exact hready

/-- Retained cached masters physically produce the cyclic factor seeds.
Only parameter alignment and an ordinary span word remain to instantiate. -/
theorem installCyclicFactorSeeds_from_cached_exec {p l s t u target a n : ℕ} [NeZero s]
    (H : ReplicaHaloProblem s) (gather : Fin 126 → Fin T) (buffers : ReplicaLoopBuffers A)
    (factor : Fin 234 → Fin T) (hfactor : Function.Injective factor) (span tmp : Fin T)
    (hsourceOff : ∀ i j, cachedFactorSeedSource gather span i ≠ factor j)
    (hsourceTmp : ∀ i, cachedFactorSeedSource gather span i ≠ tmp)
    (hfactorTmp : ∀ i, factor i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H gather buffers S)
    (hprofile : masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin n =
      cyclicFactorMasterValues p l s t u target a n)
    (hspan : (S.R span).length = n)
    (hblank : ∀ i, S.R (factor i) = []) (hleft : ∀ i, S.L (factor i) = []) (htmp : S.R tmp = []) :
    let rs := masterHeaderCopies (factor ∘ Fin.castLE (by decide : 224 ≤ 234)) (cachedFactorSeedSource gather span)
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    ∃ v' G, v'.user = v.user ∧
      Exec body (installCyclicFactorSeeds factor (cachedFactorSeedSource gather span) tmp)
        (mk v S) cost (mk v' G) ∧
      CyclicFactorSeedInput p l s t u target a n [] (embStk factor G) ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, (∀ i, factor i ≠ k) → G.R k = S.R k) := by
  apply installCyclicFactorSeeds_exec factor hfactor (cachedFactorSeedSource gather span) tmp
    hsourceOff hsourceTmp hfactorTmp v S
  · intro i
    rw [headers.factorSeedSources span n hspan i]
    exact congrFun hprofile i
  · exact hblank
  · exact hleft
  · exact htmp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
