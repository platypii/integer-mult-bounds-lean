module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Borrow an ordinary ruler's length for a local stage, then retire its copy. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def withPrivateRuler (source ruler tmp : Fin T) (run : Pr P T Q A U) : Pr P T Q A U :=
  .seq (ucopy source ruler tmp) (.seq run (uclear ruler))

theorem withPrivateRuler_exec (source ruler tmp : Fin T) (hreg : [source,ruler,tmp].Nodup)
    (run : Pr P T Q A U) (B cost reserve : ℕ)
    (Post : Stacks T A → Prop)
    (hretire : ∀ F, Post F → Post {F with R := Function.update F.R ruler []}) (v : HS T Q A U) (S : Stacks T A)
    (hB : (S.R source).length = B) (hprivate : S.R ruler = []) (htmp : S.R tmp = [])
    (hrun : ∀ v₁ : HS T Q A U,
      let M : Stacks T A := {S with R := Function.update S.R ruler (List.replicate B tick)}
      ∃ v₂ F steps, v₂.user = v₁.user ∧ steps ≤ cost ∧ F.R ruler = List.replicate B tick ∧ Post F ∧
        ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v₁ M)+depth+reserve)
          depth run (Host.mk v₁ M) steps (Host.mk v₂ F)) :
    ∃ v' F steps, v'.user = v.user ∧ steps ≤ (4*B+4)+cost+(2*B+2) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(4*B+4)+reserve)) depth (withPrivateRuler source ruler tmp run)
        (Host.mk v S) steps (Host.mk v' F)) ∧ Post F ∧ F.R ruler = [] := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹source ≠ ruler› ‹source ≠ tmp› ‹ruler ≠ tmp› v S htmp
  let M : Stacks T A := {S with R := Function.update S.R ruler (List.replicate B tick)}
  have he₁' : Exec body (ucopy source ruler tmp) (Host.mk v S) (4*B+4) (Host.mk v₁ M) := by
    simpa only [hB,hprivate,List.append_nil,M] using he₁
  obtain ⟨v₂,F,steps₂,hu₂,hn₂,hcopy,hpost,htrace₂⟩ := hrun v₁
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) ruler v₂ F
  have hlen : (F.R ruler).length = B := by rw [hcopy,List.length_replicate]
  rw [hlen] at he₃
  refine ⟨v₃,{F with R := Function.update F.R ruler []},(4*B+4)+(steps₂+(2*B+2)),
    hu₃.trans (hu₂.trans hu₁),by omega,?_,hretire F hpost,Function.update_self ..⟩
  intro depth
  have hc : mnNativePushBound 2 (ucopy (P := P) (Q := Q) (A := A) (U := U) source ruler tmp) := by
    simp [ucopy,umulSym,scanR,drainR,keepIn,pushN,moveR,moveStep,whileR,popDo,peekR,mnNativePushBound,mnActPush]
  have hz : mnNativePushBound 0 (uclear (P := P) (Q := Q) (A := A) (U := U) ruler) := by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁' 2 hc depth (mnSize (Host.mk v S)+depth+2*(4*B+4)) (by omega)
  have ht₃ : ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v₂ F)+depth+0) depth
      (uclear ruler) (Host.mk v₂ F) (2*B+2) (Host.mk v₃ {F with R := Function.update F.R ruler []}) :=
    mn_native_exec_within he₃ 0 hz depth _ (by omega)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add (htrace₂ depth) ht₃)
  simpa only [withPrivateRuler,Nat.add_zero] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
