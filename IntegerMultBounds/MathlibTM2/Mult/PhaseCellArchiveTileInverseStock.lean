module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileInverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientInverseChunkTileStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPayloadStock

/-! Reuse the inverse chunk route for replica-major row archives. The actual
payload generates its counter; all routing and codec storage is retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace ArchiveTilePlan
variable {t₀ T Q c d W K : ℕ}

noncomputable def inverseStockAllowance (plan : ArchiveTilePlan t₀ T Q c d W) : ℕ :=
  let V := (2^d)^c*(2^d*W)
  2*(4*V+4)+packedChunkStockAllowance T d W c plan.ps plan.bs
    (wiredChunkStages (2^d) W plan.one plan.exponent plan.prefixes plan.suffixes).reverse

theorem inverse_exec_within {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K) (hW : 0 < W)
    (L w : ℕ) (hpacket : W = L*w)
    (rows : Fin ((2^d)^c) → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.BankReady S)
    (hsrc : S.R plan.src = (List.ofFn fun j =>
      cstream (prime+K) w (List.ofFn fun i => rows i j).flatten).flatten) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ plan.inverseCost S ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        plan.inverseStockAllowance) depth plan.inverseProgram (Host.mk v S) n
        (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
          ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))}) := by
  let f := fun i j (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt)
  have hinput := routedArchiveRows_cstream (A := prime+K) w rows hlen
  have houtput := archiveRows_cstream (A := prime+K) w rows hlen
  have hsource : S.R plan.src = cstream (prime+K) w (keyReplicaWords f) := hsrc.trans hinput.symm
  let V := (2^d)^c*(2^d*W)
  let M := payloadCountedState S plan.count V
  have hr := plan.hreg
  regs_ne hr
  have hframe (i : Fin T) (hi : i ≠ plan.count) : M.R i = S.R i := Function.update_of_ne hi _ _
  have hcontrol (i : Fin T) (hi : i ∈ [plan.base,plan.one,plan.width,plan.exponent,plan.powTmp,plan.powSaved,
      plan.a,plan.half,plan.par,plan.bits,plan.cnt,plan.work]) : M.R i = S.R i :=
    hframe i (plan.hcountControls i hi)
  have hbank (j : Fin (swapT t₀)) : M.R (plan.ι j) = S.R (plan.ι j) := hframe _ (plan.hcountOff j)
  have hvolume : (∑ j, (M.R (plan.ι j)).length) = ∑ j, (S.R (plan.ι j)).length := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hbank]
  have hsourceLength : (S.R plan.src).length = V := by
    rw [hsource,length_cstream]
    simp [keyReplicaWords,replicaKeyWords,V,hpacket,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  let rs := wiredChunkStages (2^d) W plan.one plan.exponent plan.prefixes plan.suffixes
  let run : Pr P T Q (prime+K) U := packedGeneratedChunkTile plan.hd plan.re plan.im plan.hi
    plan.hQre plan.hQim plan.ι plan.hι plan.hT plan.src plan.tmp plan.saved plan.count plan.reRev plan.imRev
    plan.base plan.one plan.width plan.powTmp plan.powSaved plan.a plan.half plan.par plan.bits plan.cnt plan.work
    plan.ps plan.bs rs.reverse
  let runCost := packedGeneratedChunkTileCost T t₀ d W c (∑ j, (S.R (plan.ι j)).length) plan.ps plan.bs rs
  let stock := packedChunkStockAllowance T d W c plan.ps plan.bs rs.reverse
  have hrun : ∀ u : HS T Q (prime+K) U, ∃ u' n, u'.user = u.user ∧ n ≤ runCost ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk u M)+depth+stock) depth
        run (Host.mk u M) n (Host.mk u' {M with L := fun _ => [], R := (Function.update
          (Function.update M.R plan.src
            ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten)) plan.count [])}) := by
    intro u
    obtain ⟨v',n,hu,hn,he⟩ := coefficientInverseChunkTile_exec_within body hA plan.hd plan.re plan.im plan.hi
      plan.hne plan.hreHead plan.himHead plan.hQre plan.hQim plan.ι plan.hι plan.hT
      plan.src plan.tmp plan.saved plan.count plan.reRev plan.imRev plan.hreg
      plan.base plan.one plan.width plan.exponent plan.powTmp plan.powSaved plan.a plan.half plan.par plan.bits plan.cnt plan.work
      plan.ps plan.bs plan.hp plan.hb plan.hsep plan.hbankOff plan.hprotected plan.prefixes plan.suffixes
      plan.hprefixes plan.hsuffixes d W hW plan.hgen plan.hdisjoint plan.hmaster plan.hcontrols L w hpacket f u M
      (by rw [hcontrol plan.base (by simp)]; exact hready.hbase)
      (by rw [hcontrol plan.one (by simp)]; exact hready.hone)
      (by rw [hcontrol plan.width (by simp)]; exact hready.hwidth)
      (by rw [hcontrol plan.exponent (by simp)]; exact hready.hexponent)
      (by intro i hi; rw [hframe i (by intro h; subst i; exact plan.hcountBank hi)]; exact hready.hblank i hi)
      (by rw [hcontrol plan.powTmp (by simp)]; exact hready.htmp)
      (by rw [hcontrol plan.powSaved (by simp)]; exact hready.hsaved)
      hready.hL (by intro j hj; rw [hbank]; exact hready.hpriv j hj)
      (by intro k; rw [hbank]; exact hready.hhdr k)
      (by intro i hi; rw [hcontrol i (List.mem_append_right [plan.base,plan.one,plan.width,plan.exponent,plan.powTmp,plan.powSaved] hi)];
          exact hready.hgenBlank i hi)
      (by rw [hframe plan.src ‹plan.src ≠ plan.count›]; exact hsource)
      (by simp [M,payloadCountedState,V])
      (by
        intro i hi
        have hic : i ≠ plan.count := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | assumption | (apply Ne.symm; assumption)
        rw [hframe i hic]
        exact hready.hcodecBlank i hi)
      (by intro i hire hiim hheads x hx; rw [hbank] at hx; exact hready.hother i hire hiim hheads x hx) depth
    rw [hvolume] at hn
    refine ⟨v',n,hu,hn,?_⟩
    simpa only [f,houtput] using he
  simpa only [inverseProgram,countedPackedGeneratedChunkTile,inverseCost,countedPackedGeneratedChunkTileCost,
    inverseStockAllowance,rs,V,run,runCost,stock,Nat.add_assoc] using
    withPayloadCounter_exec_within (body := body) plan.src plan.count plan.saved (by regs_nodup)
      V _ run runCost stock depth v S hsourceLength hready.hcount
      (hready.hcodecBlank plan.saved (by simp)) hrun

end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
