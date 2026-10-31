module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveRowsChunkTileStock

/-! Ordinary archive readiness now supplies a complete bounded execution trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace ArchiveTilePlan
variable {t₀ T Q c d W K N : ℕ}

noncomputable def stockAllowance (plan : ArchiveTilePlan t₀ T Q c d W) : ℕ :=
  paddedChunkStockAllowance T d W c plan.ps plan.bs
    (wiredChunkStages (2^d) W plan.one plan.exponent plan.prefixes plan.suffixes)

theorem exec_within {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K) (hW : 0 < W)
    (L w : ℕ) (hpacket : W = L*w) (hN : N ≤ (2^d)^c)
    (rows : Fin N → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.Ready w rows S) (depth : ℕ) :
    ∃ padded : Fin ((2^d)^c) → Fin (2^d) → List GaussianInt,
      (∀ i j, (padded i j).length = L) ∧
      (∀ i j, padded (paddedCoreIndex hN i) j = rows i j) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan.cost S ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+plan.stockAllowance)
          depth plan.program (Host.mk v S) n (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => padded i j).flatten).flatten))}) := by
  exact paddedArchiveRowsChunkTile_exec_within body hA plan.hd plan.re plan.im plan.hi plan.hne plan.hreHead plan.himHead
    plan.hQre plan.hQim plan.ι plan.hι plan.hT plan.src plan.tmp plan.saved plan.count plan.reRev plan.imRev plan.hreg
    plan.base plan.one plan.width plan.exponent plan.powTmp plan.powSaved plan.a plan.half plan.par plan.bits plan.cnt plan.work
    plan.hpadReg plan.hsourceOff plan.hsourceControls plan.ps plan.bs plan.hp plan.hb plan.hsep plan.hbankOff plan.hsourceBank
    plan.hprotected plan.prefixes plan.suffixes plan.hprefixes plan.hsuffixes d W hW hN plan.hgen plan.hdisjoint plan.hmaster plan.hcontrols
    L w hpacket rows hlen v S hready.hbase hready.hone hready.hwidth hready.hexponent hready.hblank hready.htmp hready.hsaved
    hready.hL hready.hpriv hready.hhdr hready.hgenBlank hready.hsrc hready.hcount hready.hcodecBlank plan.hcountOff
    plan.hcountControls plan.hcountBank hready.hother depth


end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
