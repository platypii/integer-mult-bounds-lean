module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposeGeometryGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealGatherExposureData

/-! Ordinary data for actual ambient exposure and complete geometry-driven
routing. The execution method invokes both physical programs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open PackedTranspose
variable {T Q K : ℕ}

structure GeometryRealGatherData (V s width radius L w a D : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks T (prime+K)) extends RealGatherExposureData V s width radius L w Fs borrowed S where
  route : Fin PackedTranspose.tapeCount → Fin T
  hroute : Function.Injective route
  hstates : FixedStreamedBank.stateCount ≤ Q
  hpacket : 0 < L*w
  hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < D
  hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^D
  hrouteWide : s+width+2*radius < 2^D
  hrouteLfit : L < 2^D
  hrouteV : 0 < D
  hreplicaPower : Fs.length = 2^a
  hrouteSrc : e 108 = route (extra 1)
  houtput : S.R (route (extra 1)) = []
  hready : GeometryReady route D s a width radius L w S

namespace GeometryRealGatherData
variable {V s width radius L w a D : ℕ} {Fs : List (ZMod s → GaussianInt)}
  {borrowed : List (Fin (prime+K+4))} {S : Stacks T (prime+K)}
noncomputable section

def program {P U : Type} (g : GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed S) : Pr P T Q (prime+K) U :=
  .seq (replicaCoreGatherLoop g.e g.count g.source g.archive g.saved g.tmp g.replicas g.savedReplicas)
    (embProg g.route Empty.elim (geometryGatherProgram (P := Empty) g.hstates))

def timeCost (g : GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed S) : ℕ :=
  replicaCoreGatherLoopCost V s width radius L w Fs.length+geometryGatherTimeCost g.hstates D s a width radius L w

def stockAllowance (g : GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed S) : ℕ :=
  (Fs.length*(coreGatherIndices s width radius L).length*L*w+
    3*(replicaCoreGatherStepCost V s width radius L w+2))+geometryGatherStockAllowance g.hstates D s a width radius L w

theorem exec {P U : Type} (g : GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed S)
    (body : P → Pr P T Q (prime+K) U) (v : HS T Q (prime+K) U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ g.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+g.stockAllowance) depth g.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (g.route (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  exact exposeGeometryGather_exec_within body g.e g.he g.count g.source g.archive g.saved g.tmp g.replicas
    g.savedReplicas g.hreg g.hsep borrowed g.hwidth g.hwide g.hLfit g.hwV g.hvol g.hA g.hVpos g.hgroup Fs v S
    g.h163 g.h115 g.h103 g.h105 g.hs g.hw g.hr g.hL g.hz g.hblank g.h104 g.h106 g.h116 g.hsource g.harchive
    g.hreplicas g.hsavedReplicas g.hlocal g.hcount g.hsaved g.htmp g.hword g.hcontrol g.horigin g.hclean g.hfresh
    g.route g.hroute g.hstates a D g.hpacket g.hbits g.hfit g.hrouteWide g.hrouteLfit g.hrouteV g.hreplicaPower
    g.hrouteSrc (by rw [g.hrouteSrc]; exact g.houtput) g.hready depth

end
end GeometryRealGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
