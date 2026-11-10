module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveWidthSetup
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Generate a triple-product byte ruler and retire the shared intermediate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def cleanArchiveWidthSetup (replicas rows word packet count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (archiveWidthSetup replicas rows word packet count saved tmp) (clearWords [packet])

theorem cleanArchiveWidthSetup_exec (body : P → Pr P T Q A U)
    (replicas rows word packet count saved tmp : Fin T)
    (hreg : [replicas,rows,word,packet,count,saved,tmp].Nodup) (N L W depth : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R replicas).length = N) (hL : (S.R rows).length = L) (hW : (S.R word).length = W)
    (hblank : ∀ i ∈ [packet,count,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ archiveWidthSetupCost N L W+2*(L*W)+3 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*archiveWidthSetupCost N L W) depth (cleanArchiveWidthSetup replicas rows word packet count saved tmp)
        (mk v S) n (mk v' {S with R := Function.update S.R count (List.replicate (N*(L*W)) tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨vi,m,hui,hm,hsetup⟩ := archiveWidthSetup_exec_within body
    replicas rows word packet count saved tmp hreg N L W depth v S hN hL hW hblank
  let E := archiveWidthState packet count N L W S
  obtain ⟨vf,huf,he⟩ := clearWords_exec (body := body) [packet] (by simp) vi E
  have hend : ({E with R := fun i => if i ∈ [packet] then [] else E.R i} : Stacks T A) =
      {S with R := Function.update S.R count (List.replicate (N*(L*W)) tick)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = packet
    · subst i; simp [‹packet ≠ count›,hblank packet (by simp)]
    · simp only [E,archiveWidthState,List.mem_singleton,hi,ite_false,Function.update_apply]
  have he' : Exec body (clearWords [packet]) (mk vi E) (2*(L*W)+3)
      (mk vf {S with R := Function.update S.R count (List.replicate (N*(L*W)) tick)}) := by
    rw [hend] at he
    simpa [E,archiveWidthState,‹packet ≠ count›,Nat.add_assoc] using he
  have hclear := mn_native_exec_within he' 0 (clearWords_native _) depth
    (mnSize (mk vi E)+depth+0) (by simp)
  have hwhole := mn_seq_within_add hsetup hclear
  refine ⟨vf,m+(2*(L*W)+3),huf.trans hui,by omega,?_⟩
  simpa only [cleanArchiveWidthSetup,E,Nat.add_zero] using hwhole

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
