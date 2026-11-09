module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicSeedSources

/-! Generate both fitting cyclic seed banks by one restored ordinary inverse
master execution. The empty piece only changes its endpoint wiring. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generateFittingCyclicSeeds_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (source : Fin 8 → Fin T) (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i) (word saved tmp queue carry zero : Fin T)
    (hregs : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup) (hqueueOff : ∀ r, rg r ≠ queue)
    (hzeroOff : ∀ i, ports i ≠ zero)
    {B p u l target t a n : ℕ} {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hfit : a+n ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target
      (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card (PhaseCellBand.width p u) < 2^B)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,a+n] i < 2^B) :
    let stage := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value (executionPrecision p l stage 2) (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem stage 2 a n (by omega) Fs hF
    ∀ (precision packet replicas : Fin T) (W N : ℕ),
    (∀ i, ports i ∉ [precision,packet,replicas]) →
    ∀ (wl : List (Fin (A+4))), wl.length = B → ∀ (v : HS T Q A U) (S : Stacks T A),
    (S.R precision).length = p → (S.R packet).length = W → (S.R replicas).length = N →
    (∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,a+n] i) →
    S.R (rg .wr) = wl → (∀ k : TblR 25, k ≠ .wr → S.R (rg k) = []) →
    (∀ i, S.R (ports i) = []) → (∀ i ∈ [word,saved,tmp,queue], S.R i = []) → S.R zero = [] →
    ∀ depth, ∃ v' G steps, v'.user = v.user ∧
      steps ≤ generateInverseMastersCost B p u l target s t a (a+n)+(50*B+51) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((392*B+396)+3*(inverseScalarAtoms p s t u a (a+n)*tblC B 0+
          inverseMasterCopyCost B (inverseMasterValues p u l target s t a (a+n))))) depth
        (restoredSupplierMasters rg source ports word saved tmp queue carry) (Host.mk v S) steps (Host.mk v' G) ∧
      (∀ k ∈ recoverySeedHeaderPorts,
        (G.R (recoverySeedSources ports precision packet replicas k)).length = recoverySeedHeader H W N k) ∧
      (∀ k ∈ recoverySeedHeaderPorts,
        (G.R (recoverySeedSources (zeroEndpointSources ports zero) precision packet replicas k)).length =
          recoverySeedHeader K W N k) ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, (∀ i, ports i ≠ k) → G.R k = S.R k) := by
  dsimp only
  intro Fs hF precision packet replicas W N hseedOff wl hwl v S hp hW hN hvalues hwidth hblank hmasters hscratch hzero depth
  obtain ⟨v',G,steps,hu,hn,he,hleft,hI,hO,hL,hframe⟩ := generateRecoverySeedSources_exec
    (body := body) rg hrg source ports hports hsep word saved tmp queue carry hregs hqueueOff
    axis.hst ha.le (by omega) axis.hband hbandRoom hgeometryRoom hprecisionRoom hvaluesFit
    _ (axis.fittingCyclicLeftMasterValues target a n ha hfit Fs hF)
    precision packet replicas W N hseedOff wl hwl v S hp hW hN hvalues hwidth hblank hmasters hscratch depth
  have hmasterValues (i : Fin 10) : (G.R (ports i)).length =
      recoveryMasterValues (axis.cyclicLeftReplicaProblem _ 2 a n ha Fs hF) i := by
    have hm : recoveryMasterPort i ∈ recoverySeedHeaderPorts := recoverySeedHeaderPorts_perm.mem_iff.mpr
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    simpa only [recoverySeedSources_master,recoverySeedHeader_master] using hleft _ hm
  have hseedNe (i : Fin 10) : ports i ≠ precision ∧ ports i ≠ packet ∧ ports i ≠ replicas := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hseedOff i
  refine ⟨v',G,steps,hu,hn,he,hleft,?_,hI,hO,hL,hframe⟩
  apply zeroEndpointSeedSources_ready _ _ ports zero precision packet replicas W N G hmasterValues
    (fun i => axis.fittingCyclicRightMasterValues _ a n ha (by omega) hfit Fs hF i)
    ((hframe zero hzeroOff).trans hzero)
  · exact (congrArg List.length (hframe precision (fun i => (hseedNe i).1))).trans hp
  · exact (congrArg List.length (hframe packet (fun i => (hseedNe i).2.1))).trans hW
  · exact (congrArg List.length (hframe replicas (fun i => (hseedNe i).2.2))).trans hN

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
