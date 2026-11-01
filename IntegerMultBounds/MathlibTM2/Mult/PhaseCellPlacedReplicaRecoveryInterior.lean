module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInteriorExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPeripheralReady
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Lift the shared second pass through its small bank. Retained assembly
data is spectator storage, so its complete frame and stock are automatic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def placedReplicaRecoveryInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  embProg replicaRecoveryInteriorCallerReg Empty.elim
    (replicaRecoveryInterior (P := Empty) replicaRecoverySmallInterior 248 247 hR hQ)

theorem placedReplicaRecoveryInterior_exec (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) (htarget)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1) (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (buffers : ReplicaLoopBuffers A) (borrowed : List (Fin (A+4))) (v : HS 392 Q A U) (S : Stacks 392 A)
    (hready : ReplicaRecoveryPeripheralReady H buffers S)
    (hsource : S.R 389 = B.inputs.reverse.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++borrowed)
    (hbank : embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicaRecoveryInteriorTime H (B.problem htarget) ∧
      RealReplicaHaloOutput (B.problem htarget) 247 buffers.accumulatorTail F ∧
      (∀ k : Fin 126, k ≠ 87 → k ≠ 119 → k ≠ 124 →
        F.R (replicaRecoveryBatchInterior.gather k) = S.R (replicaRecoveryBatchInterior.gather k)) ∧
      (∀ k : Fin 392, 248 ≤ k.val → k ≠ 389 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        replicaRecoveryInteriorWorkspace (A := A) (U := U) H (B.problem htarget) hQ R K) depth
        (placedReplicaRecoveryInterior hR hQ) (mk v S) n (mk v' F) := by
  let e := replicaRecoveryInteriorCallerReg
  let C := embStk e S
  have hs (k : Fin 121) : C.R (replicaRecoverySmallInterior.solver k) = S.R (replicaRecoveryBatchInterior.solver k) :=
    congrArg S.R (replicaRecoveryInteriorCallerReg_solver k)
  have hg (k : Fin 126) : C.R (replicaRecoverySmallInterior.gather k) = S.R (replicaRecoveryBatchInterior.gather k) :=
    congrArg S.R (replicaRecoveryInteriorCallerReg_gather k)
  have hsourceSep : ∀ k, replicaRecoverySmallInterior.gather k ≠ 248 := by
    intro k he
    have hv := congrArg (fun k : Fin 249 => k.val) he
    change k.val = 248 at hv
    have hk := k.isLt
    omega
  have hgd : ∀ k, replicaRecoverySmallInterior.gather k ≠ 247 := by
    intro k he
    have hv := congrArg (fun k : Fin 249 => k.val) he
    change k.val = 247 at hv
    have hk := k.isLt
    omega
  have hsd : ∀ k, replicaRecoverySmallInterior.solver k ≠ 247 := by
    intro k he
    have hv := congrArg (fun k : Fin 249 => k.val) he
    change 126+k.val = 247 at hv
    have hk := k.isLt
    omega
  obtain ⟨vi,G,n,hu,hn,hfields,hgframe,he⟩ := replicaRecoveryInterior_exec_within
    (body := fun z : Empty => nomatch z) H target X B htarget replicaRecoverySmallInterior 248 247
    hsourceSep hgd hsd hR hQ hA hp hwidth hpad R K hpushR hpushK buffers borrowed (embDn e v) C
    (hready.small_headers H buffers S) hsource
    (by rw [replicaRecoveryInteriorCaller_solver_view]; exact hbank)
    ((hs 117).trans hready.cache) (fun k hk => (hs k).trans (hready.solverFresh k hk))
    hready.input hready.output ((hg 87).trans hready.keys) hready.accumulator
    ((hg 86).trans hready.packets) ((hg 119).trans hready.count) depth
  obtain ⟨v',F,hv,hu',he',hproj,hoff⟩ := exec_emb_within_stock (body' := body) (e := e) (ι := Empty.elim)
    replicaRecoveryInteriorCallerReg_injective (fun z => nomatch z) he v rfl S rfl
  have hread (i : Fin 249) : F.R (e i) = G.R i := congrFun (congrArg Stacks.R hproj) i
  refine ⟨v',F,n,hu'.trans hu,hn,?_,?_,?_,he'⟩
  · obtain ⟨Ds,hlen,hencoded,hrows⟩ := hfields
    exact ⟨Ds,hlen,(show F.R 247 = G.R 247 from hread 247).trans hencoded,hrows⟩
  · intro k h87 h119 h124
    have hh := hread (replicaRecoverySmallInterior.gather k)
    dsimp only [e] at hh
    rw [replicaRecoveryInteriorCallerReg_gather] at hh
    exact hh.trans ((hgframe k h87 h119 h124).trans (hg k))
  · intro k hk h389
    exact hoff k (fun i => replicaRecoveryInteriorCallerReg_spectator i k hk h389)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
