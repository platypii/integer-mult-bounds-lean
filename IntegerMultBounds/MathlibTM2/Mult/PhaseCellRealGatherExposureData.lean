module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCoreGatherLoop

/-! Ordinary ambient-exposure data shared by retained-header and fresh-bank
routing callers. The execution method runs the restoring replica scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ}

structure RealGatherExposureData (V s width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (borrowed : List (Fin (A+4)))
    (S : Stacks T A) where
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
  hA : 4 ≤ A
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
  hsource : S.R source = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed
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

namespace RealGatherExposureData
variable {V s width radius L w : ℕ} {Fs : List (ZMod s → GaussianInt)}
  {borrowed : List (Fin (A+4))} {S : Stacks T A}
noncomputable section

def program {P U : Type} (g : RealGatherExposureData V s width radius L w Fs borrowed S) : Pr P T Q A U :=
  replicaCoreGatherLoop g.e g.count g.source g.archive g.saved g.tmp g.replicas g.savedReplicas

def timeCost (g : RealGatherExposureData V s width radius L w Fs borrowed S) : ℕ :=
  replicaCoreGatherLoopCost V s width radius L w Fs.length

def stockAllowance (g : RealGatherExposureData V s width radius L w Fs borrowed S) : ℕ :=
  Fs.length*(coreGatherIndices s width radius L).length*L*w+
    3*(replicaCoreGatherStepCost V s width radius L w+2)

theorem exec {P U : Type} (g : RealGatherExposureData V s width radius L w Fs borrowed S)
    (body : P → Pr P T Q A U) (v : HS T Q A U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ g.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+g.stockAllowance)
        depth g.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (g.e 108)
          (cstream A w (coreGatherPayload width radius L Fs.reverse)++S.R (g.e 108)))}) := by
  exact replicaCoreGatherLoop_exec_within (body := body) g.e g.he g.count g.source g.archive
    g.saved g.tmp g.replicas g.savedReplicas g.hreg g.hsep borrowed g.hwidth g.hwide g.hLfit
    g.hwV g.hvol g.hA g.hVpos g.hgroup Fs v S g.h163 g.h115 g.h103 g.h105 g.hs g.hw g.hr g.hL
    g.hz g.hblank g.h104 g.h106 g.h116 g.hsource g.harchive g.hreplicas g.hsavedReplicas
    g.hlocal g.hcount g.hsaved g.htmp g.hword g.hcontrol g.horigin g.hclean g.hfresh depth

end
end RealGatherExposureData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
