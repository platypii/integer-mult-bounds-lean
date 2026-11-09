module

public import IntegerMultBounds.MathlibTM2.Fast.TableAtomStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Compiled table loops share one arithmetic reserve across all emitted rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A n W w : ℕ} {P U : Type}
  {body : P → Pr P T Q A U} {rg : TblR n → Fin T}

/-- A table trace with its complete emitted volume and one shared atomic reserve. -/
def tblStockRuns (wl nl : List (Fin (A+4))) (st st' : TblSt n A)
    (p : Pr P T Q A U) : Prop :=
  ∀ (v : HS T Q A U) S, tblHolds rg S (tblRho W wl nl st) →
    ∀ depth B, mnSize (mk v S)+depth+st'.acc.length+3*tblC W w ≤ B+st.acc.length →
    ∃ v' F m, v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ B) depth p (mk v S) m (mk v' F) ∧
      tblHolds rg F (tblRho W wl nl st') ∧ tblFr rg S F

private theorem tblStockRuns.seq {wl nl : List (Fin (A+4))}
    {st st₁ st₂ : TblSt n A} {p q : Pr P T Q A U}
    (hp : tblStockRuns (W := W) (w := w) (body := body) (rg := rg) wl nl st st₁ p)
    (hq : tblStockRuns (W := W) (w := w) (body := body) (rg := rg) wl nl st₁ st₂ q)
    (hacc : st₁.acc.length ≤ st₂.acc.length) :
    tblStockRuns (W := W) (w := w) (body := body) (rg := rg) wl nl st st₂ (.seq p q) := by
  intro v S hS depth B hB
  obtain ⟨v₁,F₁,m₁,hu₁,he₁,hF₁,hf₁⟩ := hp v S hS depth B (by omega)
  have hs := hS.stock_balance v v₁ hF₁ hf₁
  obtain ⟨v₂,F₂,m₂,hu₂,he₂,hF₂,hf₂⟩ := hq v₁ F₁ hF₁ depth B (by omega)
  exact ⟨v₂,F₂,m₁+m₂,hu₂.trans hu₁,.seq he₁ he₂,hF₂,hf₁.trans hf₂⟩

private theorem tbl_test_stock (hrg : Function.Injective rg)
    (wl nl : List (Fin (A+4))) (st : TblSt n A)
    (hst : ∀ i, st.val i < 2^W) (a b : Fin n)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (depth B : ℕ) (hB : mnSize (mk v S)+depth+3*tblC W w ≤ B) :
    ∃ v' F m, v'.user = v.user ∧ tblTst rg v' = decide (st.val a < st.val b) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ B) depth (tblTest rg a b)
        (mk v S) m (mk v' F) ∧ tblHolds rg F (tblRho W wl nl st) ∧ tblFr rg S F := by
  obtain ⟨v',F,m,hu,ht,_,he,hF,hf⟩ := tbl_test_exec_within (body := body)
    (w := w) hrg wl nl st hst a b v S hS
  exact ⟨v',F,m,hu,ht,(he depth).mono (by intro d z hz; omega),hF,hf⟩

/-- The auxiliary tail starts with the already evaluated loop test. -/
private theorem tblCompile_stock_aux (hrg : Function.Injective rg)
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    {c : TblCode n} {st st' : TblSt n A} {k : ℕ} (h : TblBig A W w c st st' k) :
    (∀ j, st.val j < 2^W) →
    tblStockRuns (W := W) (w := w) (body := body) (rg := rg) wl nl st st' (tblCompile rg c) ∧
    (∀ a b d, c = .loop a b d → ∀ (v : HS T Q A U) S,
      tblHolds rg S (tblRho W wl nl st) → tblTst rg v = decide (st.val a < st.val b) →
      ∀ depth B, mnSize (mk v S)+depth+st'.acc.length+3*tblC W w ≤ B+st.acc.length →
      ∃ v' F m, v'.user = v.user ∧
        ExecWithin body (fun d z => mnSize z+d ≤ B) depth
          (.loop (tblTst rg) (.seq (tblCompile rg d) (tblTest rg a b)))
          (mk v S) m (mk v' F) ∧ tblHolds rg F (tblRho W wl nl st') ∧ tblFr rg S F) := by
  induction h with
  | ins i st =>
    intro hst
    refine ⟨?_, fun a b d h => by cases h⟩
    intro v S hS depth B hB
    obtain ⟨v',F,m,hu,_,he,hF,hf⟩ := tbl_ins_runs_within (body := body)
      hrg wl nl st hwl hnl hw hst i v S hS
    have ha := i.acc_length_le (A := A) (W := W) (w := w) st
    exact ⟨v',F,m,hu,(he depth).mono (by intro d z hz; omega),hF,hf⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    intro hst
    exact ⟨((ih₁ hst).1).seq ((ih₂ (h₁.lt hst)).1) h₂.acc_length_le,
      fun a b d h => by cases h⟩
  | @iteT a b c d st st' k hlt h ih =>
    intro hst
    refine ⟨?_, fun a b d h => by cases h⟩
    intro v S hS depth B hB
    have ha := h.acc_length_le
    obtain ⟨v₁,F₁,m₁,hu₁,ht₁,he₁,hF₁,hf₁⟩ := tbl_test_stock (body := body) (w := w)
      hrg wl nl st hst a b v S hS depth B (by omega)
    have hs := hS.stock_balance v v₁ hF₁ hf₁
    obtain ⟨v₂,F₂,m₂,hu₂,he₂,hF₂,hf₂⟩ := (ih hst).1 v₁ F₁ hF₁ depth B (by omega)
    exact ⟨v₂,F₂,m₁+(m₂+1),hu₂.trans hu₁,
      .seq he₁ (.cond_true (by simpa [hlt] using ht₁) he₂),hF₂,hf₁.trans hf₂⟩
  | @iteF a b c d st st' k hlt h ih =>
    intro hst
    refine ⟨?_, fun a b d h => by cases h⟩
    intro v S hS depth B hB
    have ha := h.acc_length_le
    obtain ⟨v₁,F₁,m₁,hu₁,ht₁,he₁,hF₁,hf₁⟩ := tbl_test_stock (body := body) (w := w)
      hrg wl nl st hst a b v S hS depth B (by omega)
    have hs := hS.stock_balance v v₁ hF₁ hf₁
    obtain ⟨v₂,F₂,m₂,hu₂,he₂,hF₂,hf₂⟩ := (ih hst).1 v₁ F₁ hF₁ depth B (by omega)
    exact ⟨v₂,F₂,m₁+(m₂+1),hu₂.trans hu₁,
      .seq he₁ (.cond_false (by simpa [hlt] using ht₁) he₂),hF₂,hf₁.trans hf₂⟩
  | @loopF a b c st hlt =>
    intro hst
    refine ⟨?_, ?_⟩
    · intro v S hS depth B hB
      obtain ⟨v₁,F₁,m₁,hu₁,ht₁,he₁,hF₁,hf₁⟩ := tbl_test_stock (body := body) (w := w)
        hrg wl nl st hst a b v S hS depth B (by omega)
      exact ⟨v₁,F₁,m₁+1,hu₁,.seq he₁
        (.loop_false (by simpa [hlt] using ht₁) he₁.final),hF₁,hf₁⟩
    · intro a' b' d' heq v S hS ht depth B hB
      cases heq
      exact ⟨v,S,1,rfl,.loop_false (by simpa [hlt] using ht) (by omega),hS,tblFr.refl S⟩
  | @loopT a b c st st₁ st₂ k₁ k₂ hlt hc hl ihc ihl =>
    intro hst
    have hst₁ := hc.lt hst
    have ha := hl.acc_length_le
    have hb := hc.acc_length_le.trans ha
    have key : ∀ (v : HS T Q A U) S, tblHolds rg S (tblRho W wl nl st) →
        tblTst rg v = decide (st.val a < st.val b) → ∀ depth B,
        mnSize (mk v S)+depth+st₂.acc.length+3*tblC W w ≤ B+st.acc.length →
        ∃ v' F m, v'.user = v.user ∧
          ExecWithin body (fun d z => mnSize z+d ≤ B) depth
            (.loop (tblTst rg) (.seq (tblCompile rg c) (tblTest rg a b)))
            (mk v S) m (mk v' F) ∧ tblHolds rg F (tblRho W wl nl st₂) ∧ tblFr rg S F := by
      intro v S hS ht depth B hB
      obtain ⟨v₁,F₁,m₁,hu₁,he₁,hF₁,hf₁⟩ := (ihc hst).1 v S hS depth B (by omega)
      have hs₁ := hS.stock_balance v v₁ hF₁ hf₁
      obtain ⟨v₂,F₂,m₂,hu₂,ht₂,he₂,hF₂,hf₂⟩ := tbl_test_stock (body := body) (w := w)
        hrg wl nl st₁ hst₁ a b v₁ F₁ hF₁ depth B (by omega)
      have hs₂ := hF₁.stock_balance v₁ v₂ hF₂ hf₂
      obtain ⟨v₃,F₃,m₃,hu₃,he₃,hF₃,hf₃⟩ :=
        (ihl hst₁).2 a b c rfl v₂ F₂ hF₂ ht₂ depth B (by omega)
      exact ⟨v₃,F₃,m₁+m₂+m₃+1,hu₃.trans (hu₂.trans hu₁),
        .loop_true (by simpa [hlt] using ht) (.seq he₁ he₂) he₃,hF₃,hf₁.trans (hf₂.trans hf₃)⟩
    refine ⟨?_, ?_⟩
    · intro v S hS depth B hB
      obtain ⟨v₁,F₁,m₁,hu₁,ht₁,he₁,hF₁,hf₁⟩ := tbl_test_stock (body := body) (w := w)
        hrg wl nl st hst a b v S hS depth B (by omega)
      have hs := hS.stock_balance v v₁ hF₁ hf₁
      obtain ⟨v₂,F₂,m₂,hu₂,he₂,hF₂,hf₂⟩ := key v₁ F₁ hF₁ ht₁ depth B (by omega)
      exact ⟨v₂,F₂,m₁+m₂,hu₂.trans hu₁,.seq he₁ he₂,hF₂,hf₁.trans hf₂⟩
    · intro a' b' d' heq
      cases heq
      exact key

/-- The complete table execution retains output growth plus one instruction reserve. -/
theorem tblCompile_stock_runs (hrg : Function.Injective rg)
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    {c : TblCode n} {st st' : TblSt n A} {k : ℕ}
    (h : TblBig A W w c st st' k) (hst : ∀ j, st.val j < 2^W) :
    tblStockRuns (W := W) (w := w) (body := body) (rg := rg) wl nl st st' (tblCompile rg c) :=
  (tblCompile_stock_aux hrg wl nl hwl hnl hw h hst).1

/-- Runtime and space bounds for the same execution, with no atom-count multiplier
on transient workspace. -/
theorem tblCompile_runs_within (hrg : Function.Injective rg)
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    {c : TblCode n} {st st' : TblSt n A} {k : ℕ}
    (h : TblBig A W w c st st' k) (hst : ∀ j, st.val j < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ k*tblC W w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (st'.acc.length-st.acc.length)+3*tblC W w)
        depth (tblCompile rg c) (mk v S) m (mk v' F)) ∧
      tblHolds rg F (tblRho W wl nl st') ∧ tblFr rg S F := by
  obtain ⟨v',F,m,hu,hm,he,hF,hf⟩ :=
    tblCompile_runs (body := body) hrg wl nl hwl hnl hw h hst v S hS
  refine ⟨v',F,m,hu,hm,?_,hF,hf⟩
  intro depth
  have ha := h.acc_length_le
  obtain ⟨v₁,F₁,m₁,_,he₁,_,_⟩ :=
    tblCompile_stock_runs (body := body) hrg wl nl hwl hnl hw h hst v S hS depth
      (mnSize (mk v S)+depth+(st'.acc.length-st.acc.length)+3*tblC W w) (by omega)
  obtain ⟨hm₁,hend⟩ := he₁.toExec.unique he
  exact he₁.cast hm₁ hend

end IntegerMultBounds.MathlibTM2.Fast.TableVM
