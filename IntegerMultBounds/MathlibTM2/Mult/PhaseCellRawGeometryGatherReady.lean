module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryGatherReady

/-! Construct routing readiness from raw retained geometry and a fresh bank.
Generated boundary readiness is derived, not supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {K : ℕ}

def geometryLivePorts : List (Fin tapeCount) :=
  [headerReg 32,headerReg 33,headerReg 34,headerReg 35,headerReg 37,headerReg 87,headerReg 115,replicaCount,extra 1]

def geometryGeneratedPorts : List (Fin tapeCount) :=
  [headerReg 97,headerReg 98,headerReg 102,realRows,packetWidth,headerReg 84,headerReg 85,capacityRows]

theorem geometryReady_of_raw (V s a width radius L w : ℕ) (S : Stacks tapeCount (prime+K))
    (hs : S.R (headerReg 32) = binSyms V s) (hw : S.R (headerReg 33) = binSyms V width)
    (hr : S.R (headerReg 34) = binSyms V radius) (hL : S.R (headerReg 35) = binSyms V L)
    (h37 : (S.R (headerReg 37)).length = V) (h115 : (S.R (headerReg 115)).length = V)
    (h87 : (S.R (headerReg 87)).length = w) (hrep : (S.R replicaCount).length = 2^a)
    (hblank : ∀ i, i ∉ geometryLivePorts → S.R i = []) (hleft : ∀ i, S.L i = []) :
    GeometryReady id V s a width radius L w S := by
  have hi := headerReg_injective
  have hreplica : replicaCount = headerReg 83 := rfl
  have hcore : realRows = headerReg 80 := rfl
  have hp : packetWidth = headerReg 82 := rfl
  have hcap : capacityRows = headerReg 81 := rfl
  have haway (j : Fin 117) : headerReg j ≠ extra 1 := base_extra _ 1
  have hfresh (j : Fin 117) (hj : j ∉ [(32 : Fin 117),33,34,35,37,87,115,83]) : S.R (headerReg j) = [] := by
    apply hblank
    simpa [geometryLivePorts,hreplica,hi.eq_iff,haway] using hj
  let G := generatedGatherState S V s a width radius L w
  have hframe (i : Fin tapeCount) (hi' : i ∉ geometryGeneratedPorts) : G.R i = S.R i := by
    simp only [geometryGeneratedPorts,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi'
    simp [G,generatedGatherState,gatherHeaderState,gatherDimensionState,gatherPacketState,gatherCoreState,
      Function.update_apply,hi'.1,hi'.2.1,hi'.2.2.1,hi'.2.2.2.1,hi'.2.2.2.2.1,
      hi'.2.2.2.2.2.1,hi'.2.2.2.2.2.2.1,hi'.2.2.2.2.2.2.2]
  have hGfresh (j : Fin 117)
      (hj : j ∉ [(32 : Fin 117),33,34,35,37,87,115,83,97,98,102,80,82,84,85,81]) : G.R (headerReg j) = [] := by
    rw [hframe _ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
      simpa [geometryGeneratedPorts,hcore,hp,hcap,hi.eq_iff] using hj.2.2.2.2.2.2.2.2)]
    apply hfresh
    intro hm
    exact hj (List.mem_append_left _ hm)
  have hworker (i : Fin FixedStreamedBank.tapeCount) : G.R (base (callerWorker i)) = [] := by
    have hoff (j : Fin 117) (hj : j ≠ 109) : base (callerWorker i) ≠ headerReg j := by
      exact fun he => (TransposeRegisterPlacement.generator_off_worker _ j hj i) (base_injective he).symm
    rw [hframe _ (by
      simp only [geometryGeneratedPorts,hcore,hp,hcap,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hoff 97 (by decide),hoff 98 (by decide),hoff 102 (by decide),hoff 80 (by decide),
        hoff 82 (by decide),hoff 84 (by decide),hoff 85 (by decide),hoff 81 (by decide)⟩)]
    apply hblank
    simp only [geometryLivePorts,hreplica,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hoff 32 (by decide),hoff 33 (by decide),hoff 34 (by decide),hoff 35 (by decide),
      hoff 37 (by decide),hoff 87 (by decide),hoff 115 (by decide),hoff 83 (by decide),base_extra _ 1⟩
  have hextraInj : Function.Injective extra := by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin tapeCount => k.val) he
    simp only [extra] at hv
    omega
  have hextra (j : Fin 7) (hj : j ≠ 1) : G.R (extra j) = [] := by
    rw [hframe _ (by simp [geometryGeneratedPorts,hcore,hp,hcap,headerReg,ne_comm,base_extra])]
    apply hblank
    simpa [geometryLivePorts,hreplica,headerReg,ne_comm,base_extra,hextraInj.eq_iff] using hj
  refine ⟨h37,hs,hw,hr,hL,?_,?_,?_,?_,?_,?_,?_,h87,h115,hrep,?_,?_⟩
  · exact hfresh 36 (by simp)
  · intro k hk
    apply hfresh
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
    omega
  · exact hfresh 104 (by simp)
  · exact hfresh 106 (by simp)
  · exact hfresh 116 (by simp)
  · exact hfresh 109 (by simp)
  · exact hfresh 80 (by simp)
  · intro j hj
    apply hfresh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · change GatherReady id s a (Nat.clog 2 (coreGatherIndices s width radius L).length) width radius L w V G
    have hrow : (G.R realRows).length = (coreGatherIndices s width radius L).length := by
      simp [G,generatedGatherState,gatherHeaderState,gatherDimensionState,gatherPacketState,gatherCoreState,
        hcore,hp,hcap,hi.eq_iff]
    have hcapacity : (G.R capacityRows).length = 2^Nat.clog 2 (coreGatherIndices s width radius L).length := by
      simp [G,generatedGatherState,gatherHeaderState,gatherDimensionState,hcap,hi.eq_iff]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,hrow,hcapacity,?_,?_,?_⟩
    · change G.R (headerReg 97) = _
      simp [G,generatedGatherState,gatherHeaderState,hi.eq_iff]
    · change G.R (headerReg 98) = _
      simp [G,generatedGatherState,gatherHeaderState,hi.eq_iff]
    · change G.R (headerReg 102) = _
      simp [G,generatedGatherState,gatherHeaderState]
    · exact hGfresh 106 (by simp)
    · change (G.R (headerReg 115)).length = V
      rw [hframe _ (by simp [geometryGeneratedPorts,hcore,hp,hcap,hi.eq_iff])]
      exact h115
    · intro r
      apply hGfresh
      have hb := originReg_range r
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
      omega
    · exact hGfresh 116 (by simp)
    · exact hleft
    · intro i _ _; exact hworker i
    · change (G.R packetWidth).length = L*w
      simp [G,generatedGatherState,gatherHeaderState,gatherDimensionState,gatherPacketState,hp,hcap,hi.eq_iff]
    · change (G.R replicaCount).length = 2^a
      rw [hframe _ (by simp [geometryGeneratedPorts,hcore,hp,hcap,hreplica,hi.eq_iff])]
      exact hrep
    · intro i hi'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hworker (workerReg (reg pay))
      · exact hextra 0 (by decide)
      · exact hextra 2 (by decide)
      · exact hextra 3 (by decide)
      · exact hextra 4 (by decide)
      · exact hextra 5 (by decide)
      · exact hextra 6 (by decide)

/-- The same raw-bank construction works over arbitrary ambient spectators. -/
theorem geometryReady_of_raw_placed {T : ℕ} (e : Fin tapeCount → Fin T)
    (V s a width radius L w : ℕ) (S : Stacks T (prime+K))
    (hs : S.R (e (headerReg 32)) = binSyms V s) (hw : S.R (e (headerReg 33)) = binSyms V width)
    (hr : S.R (e (headerReg 34)) = binSyms V radius) (hL : S.R (e (headerReg 35)) = binSyms V L)
    (h37 : (S.R (e (headerReg 37))).length = V) (h115 : (S.R (e (headerReg 115))).length = V)
    (h87 : (S.R (e (headerReg 87))).length = w) (hrep : (S.R (e replicaCount)).length = 2^a)
    (hblank : ∀ i, i ∉ geometryLivePorts → S.R (e i) = []) (hleft : ∀ i, S.L (e i) = []) :
    GeometryReady e V s a width radius L w S := by
  have h := geometryReady_of_raw V s a width radius L w (embStk e S)
    hs hw hr hL h37 h115 h87 hrep hblank hleft
  exact ⟨h.h37,h.hs,h.hw,h.hr,h.hL,h.hz,h.hblank,h.h104,h.h106,h.h116,h.h109,h.hrows,
    h.hword,h.hrouterWidth,h.hrep,h.hclean,h.hready⟩

/-- Execute the complete placed router from raw geometry and a fresh bank,
without a caller-supplied generated-boundary readiness proof. -/
theorem rawGeometryGather_exec_within {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q (prime+K) U) (e : Fin tapeCount → Fin T) (he : Function.Injective e)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (V s a width radius L w : ℕ)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hA : 4 ≤ prime+K) (hV : 0 < V) (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hs : S.R (e (headerReg 32)) = binSyms V s) (hw : S.R (e (headerReg 33)) = binSyms V width)
    (hr : S.R (e (headerReg 34)) = binSyms V radius) (hL : S.R (e (headerReg 35)) = binSyms V L)
    (h37 : (S.R (e (headerReg 37))).length = V) (h115 : (S.R (e (headerReg 115))).length = V)
    (h87 : (S.R (e (headerReg 87))).length = w) (hrep : (S.R (e replicaCount)).length = 2^a)
    (hblank : ∀ i, i ∉ geometryLivePorts → S.R (e i) = []) (hleft : ∀ i, S.L (e i) = [])
    (hsrc : S.R (e (extra 1)) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ geometryGatherTimeCost hstates V s a width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        geometryGatherStockAllowance hstates V s a width radius L w) depth
        (embProg e Empty.elim (geometryGatherProgram (P := Empty) hstates)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  exact (geometryReady_of_raw_placed e V s a width radius L w S hs hw hr hL h37 h115 h87 hrep hblank hleft).exec
    body he hstates hwidth hwide hLfit hA hV hpacket hbits hfit Fs hreplicas hsrc v depth

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
