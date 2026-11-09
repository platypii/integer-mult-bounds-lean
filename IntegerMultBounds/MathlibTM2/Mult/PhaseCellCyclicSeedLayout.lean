module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateFittingCyclicSeeds

/-! Fixed scalar wiring and ordinary input headers for per-origin cyclic
master generation. No numerical readiness or resource supplier is an input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure CyclicSeedLayout (T : ℕ) where
  rg : TblR 25 → Fin T
  rgInjective : Function.Injective rg
  source : Fin 8 → Fin T
  masters : Fin 10 → Fin T
  mastersInjective : Function.Injective masters
  word : Fin T
  saved : Fin T
  tmp : Fin T
  queue : Fin T
  carry : Fin T
  zero : Fin T
  precision : Fin T
  packet : Fin T
  replicas : Fin T
  separated : ∀ i r, rg r ≠ masters i
  registers : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup
  queueOff : ∀ r, rg r ≠ queue
  zeroOff : ∀ i, masters i ≠ zero
  seedOff : ∀ i, masters i ∉ [precision,packet,replicas]

namespace CyclicSeedLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def left (g : CyclicSeedLayout T) : Fin 392 → Fin T :=
  recoverySeedSources g.masters g.precision g.packet g.replicas

def right (g : CyclicSeedLayout T) : Fin 392 → Fin T :=
  recoverySeedSources (zeroEndpointSources g.masters g.zero) g.precision g.packet g.replicas

def program (g : CyclicSeedLayout T) : Pr P T Q A U :=
  restoredSupplierMasters g.rg g.source g.masters g.word g.saved g.tmp g.queue g.carry

structure Ready (g : CyclicSeedLayout T) (B p u l target s t a n W N : ℕ) (S : Stacks T A) : Prop where
  precision : (S.R g.precision).length = p
  packet : (S.R g.packet).length = W
  replicas : (S.R g.replicas).length = N
  values : ∀ i, (S.R (g.source i)).length = ![p,u,l,target,s,t,a,a+n] i
  width : (S.R (g.rg .wr)).length = B
  workspace : ∀ k : TblR 25, k ≠ .wr → S.R (g.rg k) = []
  masters : ∀ i, S.R (g.masters i) = []
  scratch : ∀ i ∈ [g.word,g.saved,g.tmp,g.queue], S.R i = []
  zero : S.R g.zero = []

noncomputable def timeCost (B p u l target s t a n : ℕ) [NeZero s] : ℕ :=
  generateInverseMastersCost B p u l target s t a (a+n)+(50*B+51)

noncomputable def workspace (B p u l target s t a n : ℕ) [NeZero s] : ℕ :=
  (392*B+396)+3*(inverseScalarAtoms p s t u a (a+n)*tblC B 0+
    inverseMasterCopyCost B (inverseMasterValues p u l target s t a (a+n)))

theorem program_exec (g : CyclicSeedLayout T) {B p u l target s t a n : ℕ} [NeZero s] {α d : ℝ}
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
    ∀ (W N : ℕ) (v : HS T Q A U) (S : Stacks T A), g.Ready B p u l target s t a n W N S →
    ∃ v' G steps, v'.user = v.user ∧ steps ≤ timeCost B p u l target s t a n ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+workspace B p u l target s t a n) 0
        g.program (Host.mk v S) steps (Host.mk v' G) ∧
      (∀ k ∈ recoverySeedHeaderPorts, (G.R (g.left k)).length = recoverySeedHeader H W N k) ∧
      (∀ k ∈ recoverySeedHeaderPorts, (G.R (g.right k)).length = recoverySeedHeader K W N k) ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, (∀ i, g.masters i ≠ k) → G.R k = S.R k) := by
  dsimp only
  intro Fs hF W N v S ready
  exact generateFittingCyclicSeeds_exec (body := body) g.rg g.rgInjective g.source g.masters g.mastersInjective
    g.separated g.word g.saved g.tmp g.queue g.carry g.zero g.registers g.queueOff g.zeroOff axis ha hfit
    hbandRoom hgeometryRoom hprecisionRoom hvaluesFit Fs hF g.precision g.packet g.replicas W N g.seedOff
    (S.R (g.rg .wr)) ready.width v S ready.precision ready.packet ready.replicas ready.values rfl
    ready.workspace ready.masters ready.scratch ready.zero 0

end CyclicSeedLayout
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
