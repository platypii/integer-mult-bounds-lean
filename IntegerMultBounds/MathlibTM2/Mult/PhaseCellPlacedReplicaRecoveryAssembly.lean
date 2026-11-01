module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryAssemblyLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaHaloOutput
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place assembly beside the standard caller's second-pass output (247),
boundary archive (257) and retained mask (386). New output storage is 391. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def replicaRecoveryAssemblyReg (i : Fin 12) : Fin 392 :=
  ([386,390,94,299,247,257,248,391,104,105,121,89] : List (Fin 392))[i.val]'(by simpa using i.isLt)

theorem replicaRecoveryAssemblyReg_injective : Function.Injective replicaRecoveryAssemblyReg := by decide +kernel

def placedReplicaRecoveryAssembly : Pr P 392 Q A U :=
  embProg replicaRecoveryAssemblyReg Empty.elim (replicaRecoveryAssemblyLoop (P := Empty))

theorem placedReplicaRecoveryAssembly_exec (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) (htarget) (hA : 4 ≤ A)
    (tailX tailY : List (Fin (A+4))) (v : HS 392 Q A U) (S : Stacks 392 A)
    (hfields : RealReplicaHaloOutput (B.problem htarget) 247 tailX S)
    (hboundary : S.R 257 = (List.ofFn B.boundary).flatMap
      (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++tailY)
    (hmask : S.R 386 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span)
    (hwidth : (S.R 94).length = H.wordWidth)
    (hfresh : ∀ k ∈ ([390,299,248,104,105,89] : List (Fin 392)), S.R k = [])
    (hcount : (S.R 121).length = H.Fs.length) (depth : ℕ) :
    ∃ Ds : List (ZMod s → GaussianInt), ∃ v' n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧
      n ≤ H.Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4 ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedPackedPublicationMergeCost H.span H.wordWidth) depth
        placedReplicaRecoveryAssembly (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 257 tailY)
          247 tailX) 391 (outputs.reverse.flatten++S.R 391))}) := by
  obtain ⟨Ds,hlen,hencoded,hrows⟩ := hfields
  obtain ⟨_,_,hw,_⟩ := B.problem_sizing htarget
  have hlen' : Ds.length = H.Fs.length := hlen.trans B.inputs_length
  rw [hw] at hencoded
  change S.R 247 = (Ds.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++tailX at hencoded
  have hDs (r : Fin H.Fs.length) : ReplicaHaloRowSpec (B.problem htarget) r.val (Ds.getD r.val (fun _ => 0)) := by
    have hr : r.val < Ds.length := by rw [hlen']; exact r.isLt
    rw [List.getD_eq_getElem _ _ hr]
    exact hrows ⟨r.val,hr⟩
  let e := replicaRecoveryAssemblyReg
  obtain ⟨vi,n,outputs,hu,hn,hcert,he⟩ := replicaRecoveryAssemblyLoop_exec
    (body := fun z : Empty => nomatch z) H target X B htarget Ds hlen' hDs hA tailX tailY
    (embDn e v) (embStk e S) hmask hwidth (by
      change S.R 247 = _
      simpa only [List.flatMap_def] using hencoded) hboundary
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by decide)) hcount depth
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr_within_stock (body' := body) (e := e) (ι := Empty.elim)
    replicaRecoveryAssemblyReg_injective (fun z => nomatch z) he v rfl S rfl
  have hstate : embOvr e {embStk e S with R := (Function.update
        (Function.update (Function.update (embStk e S).R 5 tailY) 4 tailX) 7
          (outputs.reverse.flatten++(embStk e S).R 7))}.get S =
      {S with R := (Function.update (Function.update (Function.update S.R 257 tailY)
        247 tailX) 391 (outputs.reverse.flatten++S.R 391))} := by
    let C := embStk e S
    let M : Stacks 12 A := {C with R := Function.update C.R 5 tailY}
    let K : Stacks 12 A := {M with R := Function.update M.R 4 tailX}
    change embOvr e {K with R := Function.update K.R 7 (outputs.reverse.flatten++C.R 7)}.get S = _
    rw [embOvr_updR (e := e) replicaRecoveryAssemblyReg_injective]
    dsimp only [K]
    rw [embOvr_updR (e := e) replicaRecoveryAssemblyReg_injective]
    dsimp only [M]
    rw [embOvr_updR (e := e) replicaRecoveryAssemblyReg_injective]
    dsimp only [C]
    rw [embOvr_stk]
    rfl
  rw [hstate] at he'
  exact ⟨Ds,v',n,outputs,hlen',hu'.trans hu,hn,hcert,he'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
