module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveRowsChunkTile

/-! Reusable wiring and ordinary bank readiness for the existing archive
transpose. The plan contains no execution witness or numerical certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure ArchiveTilePlan (t₀ T Q c d W : ℕ) where
  hd : Fin 5 → Fin t₀
  re : Fin t₀
  im : Fin t₀
  hi : Function.Injective hd
  hne : re ≠ im
  hreHead : ∀ k, hd k ≠ re
  himHead : ∀ k, hd k ≠ im
  hQre : swapStates hd re hi ≤ Q
  hQim : swapStates hd im hi ≤ Q
  ι : Fin (swapT t₀) → Fin T
  hι : Function.Injective ι
  hT : swapT t₀ ≤ T
  src : Fin T
  tmp : Fin T
  saved : Fin T
  count : Fin T
  reRev : Fin T
  imRev : Fin T
  base : Fin T
  one : Fin T
  width : Fin T
  exponent : Fin T
  powTmp : Fin T
  powSaved : Fin T
  a : Fin T
  half : Fin T
  par : Fin T
  bits : Fin T
  cnt : Fin T
  work : Fin T
  ps : List (Fin T)
  bs : List (Fin T)
  prefixes : Fin c → Fin T
  suffixes : Fin c → Fin T
  hreg : [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev].Nodup
  hpadReg : [exponent,width,src,a,count,tmp,saved].Nodup
  hsourceOff : ∀ j, ι j ≠ src
  hsourceControls : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work], i ≠ src
  hp : ([base,powTmp,powSaved,one]++ps).Nodup
  hb : ([base,powTmp,powSaved,width]++bs).Nodup
  hsep : ∀ p ∈ one::ps, ∀ b ∈ width::bs, p ≠ b
  hbankOff : ∀ i ∈ ps++bs, ∀ j, i ≠ ι j
  hsourceBank : src ∉ ps++bs
  hprotected : ∀ i ∈ [a,half,par,bits,cnt,work,exponent], i ∉ ps++bs
  hprefixes : List.ofFn prefixes = one::ps
  hsuffixes : List.ofFn suffixes = width::bs
  hgen : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
    ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup
  hdisjoint : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
    ∀ k j, ι (reg (hd k)) ≠ r.dims j
  hmaster : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
    ∀ k, r.dims k ≠ ι (reg re) ∧ r.dims k ≠ ι (reg im)
  hcontrols : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work],
    i ≠ ι (reg re) ∧ i ≠ ι (reg im)
  hcountOff : ∀ j, ι j ≠ count
  hcountControls : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work], i ≠ count
  hcountBank : count ∉ ps++bs

namespace ArchiveTilePlan
variable {t₀ T Q c d W K N : ℕ}

structure Ready (plan : ArchiveTilePlan t₀ T Q c d W) (w : ℕ)
    (rows : Fin N → Fin (2^d) → List GaussianInt) (S : Stacks T (prime+K)) : Prop where
  hbase : (S.R plan.base).length = 2^d
  hone : (S.R plan.one).length = 1
  hwidth : (S.R plan.width).length = W
  hexponent : (S.R plan.exponent).length = d
  hblank : ∀ i ∈ plan.ps++plan.bs, S.R i = []
  htmp : S.R plan.powTmp = []
  hsaved : S.R plan.powSaved = []
  hL : ∀ i, S.L i = []
  hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (plan.ι j) = []
  hhdr : ∀ k, S.R (plan.ι (reg (plan.hd k))) = []
  hgenBlank : ∀ i ∈ [plan.a,plan.half,plan.par,plan.bits,plan.cnt,plan.work], S.R i = []
  hsrc : S.R plan.src = (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten
  hcount : S.R plan.count = []
  hcodecBlank : ∀ i ∈ [plan.ι (reg plan.re),plan.ι (reg plan.im),plan.tmp,plan.saved,plan.reRev,plan.imRev], S.R i = []
  hother : ∀ i, i ≠ plan.re → i ≠ plan.im → (∀ k, plan.hd k ≠ i) →
    ∀ s ∈ S.R (plan.ι (reg i)), s ≠ blank ∧ s.val < prime+4

noncomputable def program {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W) : Pr P T Q (prime+K) U :=
  paddedCountedChunkTile c plan.hd plan.re plan.im plan.hi plan.hQre plan.hQim plan.ι plan.hι plan.hT
    plan.src plan.tmp plan.saved plan.count plan.reRev plan.imRev
    plan.base plan.one plan.width plan.exponent plan.powTmp plan.powSaved plan.a plan.half plan.par plan.bits plan.cnt plan.work
    plan.ps plan.bs (wiredChunkStages (2^d) W plan.one plan.exponent plan.prefixes plan.suffixes)

noncomputable def cost (plan : ArchiveTilePlan t₀ T Q c d W) (S : Stacks T (prime+K)) :=
  paddedCountedChunkTileCost T t₀ d W c (∑ j, (S.R (plan.ι j)).length) plan.ps plan.bs
    (wiredChunkStages (2^d) W plan.one plan.exponent plan.prefixes plan.suffixes)

theorem exec {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K) (hW : 0 < W)
    (L w : ℕ) (hpacket : W = L*w) (hN : N ≤ (2^d)^c)
    (rows : Fin N → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.Ready w rows S) :
    ∃ padded : Fin ((2^d)^c) → Fin (2^d) → List GaussianInt,
      (∀ i j, (padded i j).length = L) ∧
      (∀ i j, padded (paddedCoreIndex hN i) j = rows i j) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan.cost S ∧
        Exec body plan.program (Host.mk v S) n (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => padded i j).flatten).flatten))}) := by
  exact paddedArchiveRowsChunkTile_exec body hA plan.hd plan.re plan.im plan.hi plan.hne plan.hreHead plan.himHead
    plan.hQre plan.hQim plan.ι plan.hι plan.hT plan.src plan.tmp plan.saved plan.count plan.reRev plan.imRev plan.hreg
    plan.base plan.one plan.width plan.exponent plan.powTmp plan.powSaved plan.a plan.half plan.par plan.bits plan.cnt plan.work
    plan.hpadReg plan.hsourceOff plan.hsourceControls plan.ps plan.bs plan.hp plan.hb plan.hsep plan.hbankOff plan.hsourceBank
    plan.hprotected plan.prefixes plan.suffixes plan.hprefixes plan.hsuffixes d W hW hN plan.hgen plan.hdisjoint plan.hmaster plan.hcontrols
    L w hpacket rows hlen v S hready.hbase hready.hone hready.hwidth hready.hexponent hready.hblank hready.htmp hready.hsaved
    hready.hL hready.hpriv hready.hhdr hready.hgenBlank hready.hsrc hready.hcount hready.hcodecBlank plan.hcountOff
    plan.hcountControls plan.hcountBank hready.hother

end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
