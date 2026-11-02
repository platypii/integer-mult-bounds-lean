module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryGatherReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCoreGatherLoop

/-! Actual ambient exposure followed by complete geometry-driven routing.
All count, capacity, packet and binary metadata are generated and retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type}

theorem exposeGeometryGather_exec_within (body : P → Pr P T Q (prime+K) U)
    (e : Fin 168 → Fin T) (he : Function.Injective e) (count source archive saved tmp replicas savedReplicas : Fin T)
    (hreg : [count,source,archive,saved,tmp,replicas,savedReplicas].Nodup)
    (hsep : ∀ k ∈ [count,source,archive,saved,tmp,replicas,savedReplicas], ∀ i, k ≠ e i)
    (borrowed : List (Fin (prime+K+4))) {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ prime+K) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (Fs : List (ZMod s → GaussianInt)) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (h163 : (S.R (e 163)).length = V) (h115 : S.R (e 115) = []) (h103 : S.R (e 103) = []) (h105 : S.R (e 105) = [])
    (hs : S.R (e 145) = binSyms V s) (hw : S.R (e 150) = binSyms V width)
    (hr : S.R (e 152) = binSyms V radius) (hL : S.R (e 165) = binSyms V L) (hz : S.R (e 154) = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hsource : S.R source = Fs.flatMap (fun C => cstream (prime+K) w (chirpLine s C))++borrowed)
    (harchive : S.R archive = [])
    (hreplicas : (S.R replicas).length = Fs.length) (hsavedReplicas : S.R savedReplicas = [])
    (hlocal : S.R (e 110) = [])
    (hcount : (S.R count).length = s*w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hword : (S.R (e 94)).length = w) (hcontrol : S.R (e 91) = []) (horigin : S.R (e 109) = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (e k) = [])
    (route : Fin tapeCount → Fin T) (hroute : Function.Injective route)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a D : ℕ)
    (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < D)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^D)
    (hrouteWide : s+width+2*radius < 2^D) (hrouteLfit : L < 2^D) (hrouteV : 0 < D)
    (hreplicaPower : Fs.length = 2^a)
    (hrouteSrc : e 108 = route (extra 1)) (houtput : S.R (e 108) = [])
    (hready : GeometryReady route D s a width radius L w S) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ replicaCoreGatherLoopCost V s width radius L w Fs.length+
        geometryGatherTimeCost hstates D s a width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ((Fs.length*(coreGatherIndices s width radius L).length*L*w+
          3*(replicaCoreGatherStepCost V s width radius L w+2))+
          geometryGatherStockAllowance hstates D s a width radius L w)) depth
        (.seq (replicaCoreGatherLoop e count source archive saved tmp replicas savedReplicas)
          (embProg route Empty.elim (geometryGatherProgram (P := Empty) hstates))) (mk v S) n
        (mk v' {S with R := (Function.update S.R (route (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := replicaCoreGatherLoop_exec_within (body := body)
    e he count source archive saved tmp replicas savedReplicas hreg hsep borrowed
    hwidth hwide hLfit hwV hvol hA hVpos hgroup Fs v S
    h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116 hsource harchive
    hreplicas hsavedReplicas hlocal hcount hsaved htmp hword hcontrol horigin hclean hfresh depth
  rw [houtput,List.append_nil,hrouteSrc] at he₁
  let F : Stacks T (prime+K) := {S with R := (Function.update S.R (route (extra 1))
    (cstream (prime+K) w (coreGatherPayload width radius L Fs.reverse)))}
  have hreadyF : GeometryReady route D s a width radius L w F := hready.of_frame
    (fun i hi => Function.update_of_ne (hroute.ne hi) _ _) (fun _ => rfl)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hreadyF.exec body hroute hstates hwidth hrouteWide hrouteLfit hA hrouteV
    hpacket hbits hfit Fs.reverse (by simpa only [List.length_reverse] using hreplicaPower)
    (by simp [F]) v₁ depth
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [F,Function.update_idem] using mn_seq_within_add he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
