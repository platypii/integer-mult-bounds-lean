module

public import IntegerMultBounds.MathlibTM2.Routing.HaloArchiveFiber
public import IntegerMultBounds.MathlibTM2.Routing.FiberScanStock

/-! Ordered prefix scan of the actual expose/halo/return body. The archive is
private and all retained dimensions are reused across complete prefix fibers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloPrefixScan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main HaloPassContext
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def scan : Pr P 117 Q A U := FiberScan.scanFibers 61 39 62 HaloArchiveFiber.emitFiber

theorem scan_exec (p : Parameters) (fibers : List (List (List (List GaussianInt))))
    (hshape : ∀ matrices ∈ fibers, Shape p matrices) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hh : Holds p S) (hf : Fresh S) (hvolume : (S.R 60).length = outputVolume p)
    (htmp : S.R 63 = []) (harchive : S.R 62 = []) (hclock : (S.R 61).length = fibers.length)
    (hsrc : S.R 39 = fibers.flatMap (input A p)++tail) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ fibers.length*(HaloArchiveFiber.cost p+3)+2*(fibers.length*outputVolume p)+4 ∧
      Exec body scan (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R 39
        (fibers.flatMap (output A p)++tail)) 61 [])}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*(fibers.length*outputVolume p)+HaloArchiveFiber.reserve p+2)) depth scan (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 39 (fibers.flatMap (output A p)++tail)) 61 [])})) := by
  have hvol : (fibers.flatMap (output A p)).length = fibers.length*outputVolume p :=
    HaloRecordLayout.length_flatMap (output A p) (outputVolume p) fibers
      (fun matrices hm => output_length A p matrices (hshape matrices hm))
  obtain ⟨vf,n,hu,hn,he,hs⟩ := FiberScanStock.scanFibers_exec_within (body := body) 61 39 62 (by decide)
    HaloArchiveFiber.emitFiber fibers (input A p) (output A p) (HaloArchiveFiber.cost p) (HaloArchiveFiber.reserve p)
    tail v S (by
      intro matrices hm vi F rest hframe hsrcF
      obtain ⟨vf,n,hu,hn,_,hs⟩ := HaloArchiveFiber.emitFiber_exec (body := body) p matrices (hshape matrices hm)
        hA rest vi F (hh.frame (by intro i hs ha hc _; exact hframe i hs ha hc))
        (hf.frame (by intro i hs ha hc _; exact hframe i hs ha hc))
        (by rw [hframe 60 (by decide) (by decide) (by decide)]; exact hvolume)
        (by rw [hframe 63 (by decide) (by decide) (by decide)]; exact htmp) hsrcF
      exact ⟨vf,n,hu,hn,hs⟩) hclock hsrc harchive
  refine ⟨vf,n,hu,?_,?_,?_⟩
  · simpa only [hvol] using hn
  · exact he
  · intro depth
    simpa only [scan,hvol] using hs depth

end IntegerMultBounds.MathlibTM2.Routing.HaloPrefixScan
