module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedRestoringGather

/-! Ordinary caller data for the complete restoring preparation. Its execution
method runs the actual exposure and routing programs after numerical initialization. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ}

structure RestoringGatherData (bank : ComputedClassBank → Fin T) (V s width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K)) where
  exposeSrc : Fin 8 → Fin T
  input : Fin T
  routeSrc : Fin 7 → Fin T
  hstates : FixedStreamedBank.stateCount ≤ Q
  D : ℕ
  a : ℕ
  hExposeOff : ∀ i k, exposeSrc i ≠ bank k
  hInputOff : ∀ k, input ≠ bank k
  hRouteOff : ∀ i k, routeSrc i ≠ bank k
  hwidth : 0 < width
  hwide : s+width+2*radius < 2^V
  hLfit : L < 2^V
  hwV : w < 2^V
  hvol : s*w < 2^V
  hA : 4 ≤ prime+K
  hVpos : 0 < V
  hgroup : 0 < (coreGatherIndices s width radius L).length
  hs : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 0)) = binSyms V s
  hw : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 1)) = binSyms V width
  hr : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 2)) = binSyms V radius
  hL : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 3)) = binSyms V L
  hV : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 4))).length = V
  hword : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 5))).length = w
  hcount : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 6))).length = s*w
  hreplicas : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 7))).length = Fs.length
  hsource : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream (prime+K) w (chirpLine s C))++borrowed
  hblank : ∀ i, (embStk (exposureIntoRouting T) S).R (Fin.natAdd T i) = []
  houtput : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (bank (.control .source))) = []
  hDwide : s+width+2*radius < 2^D
  hDLfit : L < 2^D
  hDpos : 0 < D
  hpacket : 0 < L*w
  hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < D
  hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^D
  hpower : Fs.length = 2^a
  hRs : S.R (classCallerRegister (routeSrc 0)) = binSyms D s
  hRw : S.R (classCallerRegister (routeSrc 1)) = binSyms D width
  hRr : S.R (classCallerRegister (routeSrc 2)) = binSyms D radius
  hRL : S.R (classCallerRegister (routeSrc 3)) = binSyms D L
  hRV : (S.R (classCallerRegister (routeSrc 4))).length = D
  hRword : (S.R (classCallerRegister (routeSrc 5))).length = w
  hRrep : (S.R (classCallerRegister (routeSrc 6))).length = 2^a
  hRblank : ∀ i, S.R (Fin.natAdd (T+175) i) = []
  hRleft : ∀ i, S.L (Fin.natAdd (T+175) i) = []
  hsourceLeft : S.L (control (fullExposedClassBank bank) .source) = []

namespace RestoringGatherData
variable {bank : ComputedClassBank → Fin T} {V s width radius L w : ℕ}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K)}
noncomputable section

def program {P U : Type} (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S) :
    Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U :=
  .seq (embProg (exposureIntoRouting T) Empty.elim
    (restoringAllocatedExposure (P := Empty) g.exposeSrc g.input (bank (.control .source))))
    (restoringAllocatedGather (exposedClassBank bank) (fun i => Fin.castAdd 175 (g.routeSrc i)) g.hstates)

def timeCost (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S) : ℕ :=
  ((6*exposureMetadataVolume g.exposeSrc (embStk (exposureIntoRouting T) S)+49)+
    (replicaCoreGatherLoopCost V s width radius L w Fs.length+
      (2*exposureMetadataVolume g.exposeSrc (embStk (exposureIntoRouting T) S)+17)))+
    ((6*gatherMetadataVolume (fun i => Fin.castAdd 175 (g.routeSrc i)) S+49)+
      (geometryGatherTimeCost g.hstates g.D s g.a width radius L w+
        (2*gatherMetadataVolume (fun i => Fin.castAdd 175 (g.routeSrc i)) S+17)))

def stockAllowance (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S) : ℕ :=
  (2*(6*exposureMetadataVolume g.exposeSrc (embStk (exposureIntoRouting T) S)+49)+
    (Fs.length*(coreGatherIndices s width radius L).length*L*w+
      3*(replicaCoreGatherStepCost V s width radius L w+2)))+
    (2*(6*gatherMetadataVolume (fun i => Fin.castAdd 175 (g.routeSrc i)) S+49)+
      geometryGatherStockAllowance g.hstates g.D s g.a width radius L w)

theorem exec {P U : Type}
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (hinj : Function.Injective bank) (initSrc : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U)
    (v : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) (depth : ℕ) :
    let M := loadedClassGeometry (fullExposedClassBank bank) initSrc S
    ∃ v' n, v'.user = v.user ∧ n ≤ g.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v M)+depth+g.stockAllowance)
        depth g.program (Host.mk v M) n
        (Host.mk v' {M with R := (Function.update M.R (control (fullExposedClassBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  exact initializedRestoringGather_exec_within body bank hinj g.exposeSrc g.hExposeOff g.input g.hInputOff
    V s width radius L w Fs borrowed S initSrc g.hwidth g.hwide g.hLfit g.hwV g.hvol g.hA g.hVpos g.hgroup
    g.hs g.hw g.hr g.hL g.hV g.hword g.hcount g.hreplicas g.hsource g.hblank g.houtput
    g.routeSrc g.hRouteOff g.hstates g.D g.a g.hDwide g.hDLfit g.hDpos g.hpacket g.hbits g.hfit g.hpower
    g.hRs g.hRw g.hRr g.hRL g.hRV g.hRword g.hRrep g.hRblank g.hRleft g.hsourceLeft v depth

end
end RestoringGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
