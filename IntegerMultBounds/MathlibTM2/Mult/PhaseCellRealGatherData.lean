module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposeRealGather

/-! Ordinary data for one real ambient gather. The execution method invokes
its existing physical implementation, preserving the exact returned frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W K : ℕ}

structure RealGatherData (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (prime+K+4))) (S : Stacks T (prime+K)) where
  hW : 0 < W
  e : Fin 168 → Fin T
  he : Function.Injective e
  count : Fin T
  source : Fin T
  archive : Fin T
  saved : Fin T
  tmp : Fin T
  replicas : Fin T
  savedReplicas : Fin T
  hreg : [count,source,archive,saved,tmp,replicas,savedReplicas].Nodup
  hsep : ∀ k ∈ [count,source,archive,saved,tmp,replicas,savedReplicas], ∀ i, k ≠ e i
  hwidth : 0 < width
  hwide : s+width+2*radius < 2^V
  hLfit : L < 2^V
  hwV : w < 2^V
  hvol : s*w < 2^V
  hA : 4 ≤ prime+K
  hVpos : 0 < V
  hgroup : 0 < (coreGatherIndices s width radius L).length
  h163 : (S.R (e 163)).length = V
  h115 : S.R (e 115) = []
  h103 : S.R (e 103) = []
  h105 : S.R (e 105) = []
  hs : S.R (e 145) = binSyms V s
  hw : S.R (e 150) = binSyms V width
  hr : S.R (e 152) = binSyms V radius
  hL : S.R (e 165) = binSyms V L
  hz : S.R (e 154) = []
  hblank : ∀ k : Fin 168, k.val < 31 → S.R (e k) = []
  h104 : S.R (e 104) = []
  h106 : S.R (e 106) = []
  h116 : S.R (e 116) = []
  hsource : S.R source = Fs.flatMap (fun C => cstream (prime+K) w (chirpLine s C))++borrowed
  harchive : S.R archive = []
  hreplicas : (S.R replicas).length = Fs.length
  hsavedReplicas : S.R savedReplicas = []
  hlocal : S.R (e 110) = []
  hcount : (S.R count).length = s*w
  hsaved : S.R saved = []
  htmp : S.R tmp = []
  hword : (S.R (e 94)).length = w
  hcontrol : S.R (e 91) = []
  horigin : S.R (e 109) = []
  hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (e k) = []
  hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (e k) = []
  realRows : Fin T
  capacityRows : Fin T
  blockWidth : Fin T
  rowSymbols : Fin T
  padSymbols : Fin T
  missing : Fin T
  acc : Fin T
  padSaved : Fin T
  padTmp : Fin T
  hrouteRegs : [realRows,capacityRows,blockWidth,rowSymbols,padSymbols,missing,plan.src,acc,padSaved,padTmp,replicas,savedReplicas].Nodup
  hrouteSrc : e 108 = plan.src
  houtput : S.R plan.src = []
  hready : plan.BankReady S
  hpacket : W = L*w
  hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c
  hreplicaPower : Fs.length = 2^d
  hrows : (S.R realRows).length = (coreGatherIndices s width radius L).length
  hcapacityRows : (S.R capacityRows).length = (2^d)^c
  hblockWidth : (S.R blockWidth).length = L*w
  hrowSymbols : S.R rowSymbols = []
  hpadSymbols : S.R padSymbols = []
  hmissing : S.R missing = []
  hacc : S.R acc = []
  hpadSaved : S.R padSaved = []
  hpadTmp : S.R padTmp = []

namespace RealGatherData
variable {plan : ArchiveTilePlan t₀ T Q c d W} {V s width radius L w : ℕ}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))} {S : Stacks T (prime+K)}

theorem exec {P U : Type} (g : RealGatherData plan V s width radius L w Fs borrowed S)
    (body : P → Pr P T Q (prime+K) U) (v : HS T Q (prime+K) U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ plan.realGatherTimeCost V s width radius L w Fs.length S ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        plan.realGatherStockAllowance V s width radius L w Fs.length) depth
        (plan.realGatherProgram g.e g.count g.source g.archive g.saved g.tmp g.replicas g.savedReplicas g.realRows g.capacityRows g.blockWidth g.rowSymbols g.padSymbols g.missing g.acc g.padSaved g.padTmp)
        (Host.mk v S) n (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  exact expose_real_gather_exec_within plan body g.hW g.e g.he g.count g.source g.archive g.saved g.tmp g.replicas g.savedReplicas g.hreg g.hsep borrowed g.hwidth g.hwide g.hLfit g.hwV g.hvol g.hA g.hVpos g.hgroup Fs v S g.h163 g.h115 g.h103 g.h105 g.hs g.hw g.hr g.hL g.hz g.hblank g.h104 g.h106 g.h116 g.hsource g.harchive g.hreplicas g.hsavedReplicas g.hlocal g.hcount g.hsaved g.htmp g.hword g.hcontrol g.horigin g.hclean g.hfresh g.realRows g.capacityRows g.blockWidth g.rowSymbols g.padSymbols g.missing g.acc g.padSaved g.padTmp g.hrouteRegs g.hrouteSrc g.houtput g.hready g.hpacket g.hcapacity g.hreplicaPower g.hrows g.hcapacityRows g.hblockWidth g.hrowSymbols g.hpadSymbols g.hmissing g.hacc g.hpadSaved g.hpadTmp depth

end RealGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
