module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeReplicaCouplingRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaCouplingLoop

/-! Prepare shared geometry, coefficient page and counters once, then execute
all paired replica rows using those actual generated resources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def preparedReplicaCoupling {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (initializeReplicaCouplingRuntime placement)
    (initializedReplicaCouplingLoop placement volume output rhs dst saved tmp count hQ)

def preparedReplicaCouplingCost (H : ReplicaHaloProblem s) (V : ℕ) :=
  initializeReplicaCouplingRuntimeCost V (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    ((4*H.Fs.length+4)+H.Fs.length*(replicaCouplingTransitionCost H V+3)+2)

theorem preparedReplicaCoupling_exec (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hreg : [plan.gather 121,volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp,count].Nodup)
    (hports : ∀ i, ∀ k ∈ [volume,output,rhs,dst,saved,tmp,count], placement.bank i ≠ k) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hw5 : 5 ≤ H.wordWidth) (hqw : H.precision+4 ≤ H.wordWidth) (hsep : H.span+H.band ≤ s) (horigin : H.origin < s)
    (V : ℕ) (hwide : 8*(H.t+1)^2+4*H.band+8 < 2^V)
    (hfitV : H.origin+(H.span+2*H.band)+s < 2^V)
    (has : ∀ j < H.span, ∀ z ∈ couplingCoefficientWords (2^15*H.p) H.precision s H.t H.u H.band (H.origin+j), Fits H.wordWidth z ∧ z.im = 0)
    (outputTail rhsTail raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S) (hcountBlank : S.R count = []) (hmaster : (S.R (plan.gather 121)).length = H.Fs.length)
    (hready : CouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw
      (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hvolume : (S.R volume).length = H.span*H.wordWidth) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hV : (S.R (plan.gather 115)).length = V) (hsetupTmp : S.R (plan.gather 7) = [])
    (h107 : S.R (placement.bank 107) = [])
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167], S.R (placement.bank k) = []) :
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      m ≤ preparedReplicaCouplingCost H V ∧
      Exec body (preparedReplicaCoupling placement volume output rhs dst saved tmp count hQ) (mk v S) m (mk v' F) ∧
      F.R count = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw
        (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata V s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, placement.bank i ≠ k) → k ∉ [output,rhs,dst] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val]) ∧
      F.R (placement.bank 138) = cstream A H.wordWidth
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++S.R (placement.bank 138) ∧
      (F.R (placement.bank 139)).length =
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length ∧
      (F.R (placement.bank 140)).length = 2*H.band+1 ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], F.R (placement.bank k) = []) := by
  have hP : 13 ≤ 2^15*H.p := by have hp := H.p_pos; omega
  obtain ⟨v₁,J,n₁,hu₁,hn₁,he₁,hreadyJ,hmeta,hpage,hgather,hL₁,hi₁,ho₁,hcount,hrows,hoff,hfreshJ⟩ :=
    initializeReplicaCouplingRuntime_exec_within (body := body) placement (by omega : 4 ≤ A) hw5 hqw hP H.s_lt_t
      (Nat.le_add_right _ _) H.span_fit horigin hwide (by simpa using hfitV) raw v S hready hV hsetupTmp h107 hblank
      (by intro k hk; apply hfresh; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp) 0
  have hforeign (k : Fin T) (hk : k ∈ [volume,output,rhs,dst,saved,tmp,count]) : J.R k = S.R k :=
    hoff k (fun i => hports i k hk)
  obtain ⟨v₂,F,n₂,Ds,hu₂,hn₂,he₂,hcountF,hout,hrhsF,hbank,hL₂,hi₂,ho₂,hframe,hlen,harchive,hgood⟩ :=
    initializedReplicaCouplingLoop_exec (body := body) H placement volume output rhs dst saved tmp count hreg
      (fun i => hports i output (by simp)) (fun i => hports i rhs (by simp))
      (fun i => hports i dst (by simp)) (fun i => hports i count (by simp)) hQ hA hw5 hqw hsep V hwide hfitV has
      outputTail rhsTail (S.R (placement.bank 138)) raw v₁ J
      (ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail 0 S J h
        (hforeign output (by simp)) (hforeign rhs (by simp)))
      (by rw [hforeign count (by simp)]; exact hcountBlank)
      (by rw [hoff _ (fun i => placement.bank_gather_disjoint i 121)]; exact hmaster) hreadyJ
      (by rw [hforeign volume (by simp)]; exact hvolume)
      (by rw [hforeign saved (by simp)]; exact hsaved) (by rw [hforeign tmp (by simp)]; exact htmp)
      hrows (by simpa using hpage) (by simpa using hcount) (by simpa using hmeta)
      (by intro k hk; apply hfreshJ k hk; apply hfresh
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hbankR (k : Fin 168) : F.R (placement.bank k) = J.R (placement.bank k) := congrFun (congrArg Stacks.R hbank) k
  refine ⟨v₂,F,n₁+n₂,Ds,hu₂.trans hu₁,by unfold preparedReplicaCouplingCost; omega,
    .seq he₁.toExec he₂,hcountF,hout,hrhsF,?_,?_,hL₂.trans hL₁,hi₂.trans hi₁,ho₂.trans ho₁,?_,hlen,?_,hgood,?_,?_,?_,?_⟩
  · have hnative : embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver J) := by
      rw [← placement.native_view F,← placement.native_view J,hbank]
    rw [hnative]
    exact hreadyJ
  · rw [hbank]
    simpa using hmeta
  · intro k hk hports
    exact (hframe k hports).trans (hoff k hk)
  · rw [hforeign dst (by simp)] at harchive
    exact harchive

  · rw [hbankR 138]
    simpa using hpage
  · rw [hbankR 139]
    simpa using hcount
  · rw [hbankR 140]
    exact hrows
  · intro k hk
    rw [hbankR k]
    apply hfreshJ k hk
    apply hfresh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
