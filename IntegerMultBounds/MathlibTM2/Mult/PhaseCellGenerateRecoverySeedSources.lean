module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredInverseMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySeedSources

/-! Execute inverse master generation and establish every seed-header source.
Scalar workspace restores; only the ten exported master words are installed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generateRecoverySeedSources_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (source : Fin 8 → Fin T) (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i) (word saved tmp queue carry : Fin T)
    (hregs : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup) (hqueueOff : ∀ r, rg r ≠ queue)
    {B p u l target t a b : ℕ}
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^B)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (H : ReplicaHaloProblem s)
    (hmastersEq : recoveryMasterValues H = inverseMasterValues p u l target s t a b)
    (precision packet replicas : Fin T) (W N : ℕ)
    (hseedOff : ∀ i, ports i ∉ [precision,packet,replicas])
    (wl : List (Fin (A+4))) (hwl : wl.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hp : (S.R precision).length = H.p) (hW : (S.R packet).length = W)
    (hN : (S.R replicas).length = N)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ k : TblR 25, k ≠ .wr → S.R (rg k) = [])
    (hmasters : ∀ i, S.R (ports i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ generateInverseMastersCost B p u l target s t a b+(50*B+51) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        ((392*B+396)+3*(inverseScalarAtoms p s t u a b*tblC B 0+
          inverseMasterCopyCost B (inverseMasterValues p u l target s t a b)))) depth
        (restoredSupplierMasters rg source ports word saved tmp queue carry) (Host.mk v S) n (Host.mk v' F) ∧
      (∀ k ∈ recoverySeedHeaderPorts,
        (F.R (recoverySeedSources ports precision packet replicas k)).length = recoverySeedHeader H W N k) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, ports i ≠ k) → F.R k = S.R k := by
  obtain ⟨v',F,n,hu,hn,he,hheads,hI,hO,hL,hframe⟩ := restoredInverseMasters_exec (body := body)
    rg hrg source ports hports hsep word saved tmp queue carry hregs hqueueOff
    hst has hbs hband hbandRoom hgeometryRoom hprecisionRoom hvaluesFit wl hwl v S
    hvalues hwidth hblank hmasters hscratch depth
  have hseedNe (i : Fin 10) : ports i ≠ precision ∧ ports i ≠ packet ∧ ports i ≠ replicas := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hseedOff i
  have hmasterLengths (i : Fin 10) : (F.R (ports i)).length = recoveryMasterValues H i := by
    rw [hheads,List.length_replicate]
    exact (congrFun hmastersEq i).symm
  refine ⟨v',F,n,hu,hn,he,?_,hI,hO,hL,hframe⟩
  apply recoverySeedSources_ready H W N ports precision packet replicas F hmasterLengths
  · rw [hframe precision (fun i => (hseedNe i).1)]
    exact hp
  · rw [hframe packet (fun i => (hseedNe i).2.1)]
    exact hW
  · rw [hframe replicas (fun i => (hseedNe i).2.2)]
    exact hN

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
