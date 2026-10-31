module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposeRouteGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireRoutedGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCoreGatherLoop

/-! One restoring ambient exposure produces exactly the real supplier stream,
including generated padding and dummy-prefix retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace ArchiveTilePlan
variable {t₀ T Q c d W K : ℕ}

theorem expose_real_gather_exec_within {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (body : P → Pr P T Q (prime+K) U) (hW : 0 < W) (e : Fin 168 → Fin T) (he : Function.Injective e) (count source archive saved tmp replicas savedReplicas : Fin T)
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
    (realRows capacityRows blockWidth rowSymbols padSymbols missing acc padSaved padTmp : Fin T)
    (hrouteRegs : [realRows,capacityRows,blockWidth,rowSymbols,padSymbols,missing,plan.src,acc,padSaved,padTmp,replicas,savedReplicas].Nodup)
    (hrouteSrc : e 108 = plan.src) (houtput : S.R plan.src = [])
    (hready : plan.BankReady S) (hpacket : W = L*w)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c)
    (hreplicaPower : Fs.length = 2^d)
    (hrows : (S.R realRows).length = (coreGatherIndices s width radius L).length)
    (hcapacityRows : (S.R capacityRows).length = (2^d)^c) (hblockWidth : (S.R blockWidth).length = L*w)
    (hrowSymbols : S.R rowSymbols = []) (hpadSymbols : S.R padSymbols = []) (hmissing : S.R missing = [])
    (hacc : S.R acc = []) (hpadSaved : S.R padSaved = []) (hpadTmp : S.R padTmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (replicaCoreGatherLoopCost V s width radius L w Fs.length +
          ((gatherCounterSetupCost (coreGatherIndices s width radius L).length ((2^d)^c) (L*w) +
            (Fs.length*(6*((2^d)^c*L*w)+13)+6) + (2*((2^d)^c*L*w)+4))+plan.inverseCost S)) +
        retireDummyBatchesCost (coreGatherIndices s width radius L).length ((2^d)^c) (2^d) (L*w) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (((Fs.length*(coreGatherIndices s width radius L).length*L*w+
            3*(replicaCoreGatherStepCost V s width radius L w+2)) +
            ((2*gatherCounterSetupCost (coreGatherIndices s width radius L).length ((2^d)^c) (L*w) +
              (Fs.length*(((2^d)^c-(coreGatherIndices s width radius L).length)*L*w)+
                2*(4*((2^d)^c*L*w)+10)))+plan.inverseStockAllowance)) +
          2*retireDummyBatchesCost (coreGatherIndices s width radius L).length ((2^d)^c) (2^d) (L*w))) depth
        (.seq (.seq (replicaCoreGatherLoop e count source archive saved tmp replicas savedReplicas)
          (.seq (generatedPrefixPadRows realRows capacityRows blockWidth rowSymbols padSymbols missing plan.src
            acc padSaved padTmp replicas savedReplicas (pairSym (prime+K) false false)) plan.inverseProgram))
          (retireDummyBatches realRows capacityRows replicas blockWidth rowSymbols padSymbols missing padSaved padTmp plan.src))
        (Host.mk v S) n (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
          ((List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
            cstream (prime+K) w (Fs.reverse.map (packedInterval
              (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten).flatten))}) := by
  obtain ⟨rows,hlen,hbatches,v₁,n₁,hu₁,hn₁,he₁⟩ := plan.expose_route_gather_exec_within body hW e he count source archive saved tmp
    replicas savedReplicas hreg hsep borrowed hwidth hwide hLfit hwV hvol hA hVpos hgroup Fs v S
    h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116 hsource harchive hreplicas hsavedReplicas
    hlocal hcount hsaved htmp hword hcontrol horigin hclean hfresh
    realRows capacityRows blockWidth rowSymbols padSymbols missing acc padSaved padTmp hrouteRegs hrouteSrc houtput
    hready hpacket hcapacity hreplicaPower hrows hcapacityRows hblockWidth hrowSymbols hpadSymbols hmissing hacc hpadSaved hpadTmp depth
  let F : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update S.R plan.src
    ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))}
  change ExecWithin _ _ _ _ _ _ (Host.mk v₁ F) at he₁
  have hroutes := hrouteRegs
  regs_ne hroutes
  have hbase (k : Fin T) (hk : k ≠ plan.src) : F.R k = S.R k := by simp [F,hk]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireRoutedGather_exec_within (body := body)
    realRows capacityRows replicas blockWidth rowSymbols padSymbols missing padSaved padTmp plan.src
    (by regs_nodup) width radius L w hcapacity Fs.reverse rows hlen hbatches v₁ F
    (by rw [hbase _ ‹realRows ≠ plan.src›]; exact hrows)
    (by rw [hbase _ ‹capacityRows ≠ plan.src›]; exact hcapacityRows)
    (by rw [hbase _ ‹plan.src ≠ replicas›.symm,hreplicas,hreplicaPower])
    (by rw [hbase _ ‹blockWidth ≠ plan.src›]; exact hblockWidth)
    (by rw [hbase _ ‹rowSymbols ≠ plan.src›]; exact hrowSymbols)
    (by rw [hbase _ ‹padSymbols ≠ plan.src›]; exact hpadSymbols)
    (by rw [hbase _ ‹missing ≠ plan.src›]; exact hmissing)
    (by rw [hbase _ ‹plan.src ≠ padSaved›.symm]; exact hpadSaved)
    (by rw [hbase _ ‹plan.src ≠ padTmp›.symm]; exact hpadTmp) (by simp [F]) depth
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [F,Function.update_idem] using mn_seq_within_add he₁ he₂

end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
