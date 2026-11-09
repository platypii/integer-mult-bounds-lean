module

public import IntegerMultBounds.MathlibTM2.Fast.TableFrameStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush

/-! One shared instruction reserve for compiled table arithmetic and tests. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A n W w : ℕ} {P U : Type}
  {body : P → Pr P T Q A U} {rg : TblR n → Fin T}

/-- A table instruction needs one atomic reserve, independently of its operands. -/
theorem tbl_ins_runs_within (hrg : Function.Injective rg)
    (wl nl : List (Fin (A+4))) (st : TblSt n A)
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (hst : ∀ i, st.val i < 2^W) (i : TblIns n)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ tblC W w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*tblC W w)
        depth (tblInsProg rg i) (mk v S) m (mk v' F)) ∧
      tblHolds rg F (tblRho W wl nl (i.run A W w st)) ∧ tblFr rg S F := by
  obtain ⟨v', F, m, hu, hm, he, hF, hf⟩ :=
    tbl_ins_runs (body := body) hrg wl nl st hwl hnl hw hst i v S hS
  refine ⟨v', F, m, hu, hm, ?_, hF, hf⟩
  intro depth
  exact mn_native_exec_within he 3 (tblInsProg_native rg i) depth _ (by omega)

/-- Tests preserve the canonical bank and use the same reserve as arithmetic. -/
theorem tbl_test_exec_within (hrg : Function.Injective rg)
    (wl nl : List (Fin (A+4))) (st : TblSt n A)
    (hst : ∀ i, st.val i < 2^W) (a b : Fin n)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' F m, v'.user = v.user ∧ tblTst rg v' = decide (st.val a < st.val b) ∧
      m ≤ 24*W+24 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*tblC W w)
        depth (tblTest rg a b) (mk v S) m (mk v' F)) ∧
      tblHolds rg F (tblRho W wl nl st) ∧ tblFr rg S F := by
  obtain ⟨v', F, m, hu, ht, hm, he, hF, hf⟩ :=
    tbl_test_exec (body := body) hrg wl nl st hst a b v S hS
  refine ⟨v', F, m, hu, ht, hm, ?_, hF, hf⟩
  have hc : 24*W+24 ≤ tblC W w := by unfold tblC; nlinarith
  intro depth
  exact mn_native_exec_within he 3 (tblTest_native rg a b) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Fast.TableVM
