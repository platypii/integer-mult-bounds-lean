module

public import IntegerMultBounds.MathlibTM2.Fast.TableCompileStock
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Table stream publication retains output plus one shared arithmetic reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T}

theorem tblHost_runs_within (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) {c : TblCode n} {st : TblSt n A} {Post : TblSt n A → Prop} {K : ℕ}
    (h : TblDo A W w c st Post K) (hst : ∀ j, st.val j < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m st', Post st' ∧ v'.user = v.user ∧ m ≤ K * tblC W w + 2 * st'.acc.length + 2 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          3*st'.acc.length+3*tblC W w+2)
        depth (tblHost rg c out) (mk v S) m (mk v' S')) ∧
      S'.R out = st'.acc.reverse ++ S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧ ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ :=
    tblCompile_runs_within (body := body) hrg wl nl hwl hnl hw hb hst v S hS
  have hm₁ := hm₁.trans (Nat.mul_le_mul_right (tblC W w) hk)
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg .acc) out (hout .acc) id v₁ S₁
  have hacc₁ : S₁.R (rg .acc) = st'.acc := hS₁ .acc
  refine ⟨v₂, {S₁ with R := movedR S₁.R (rg .acc) out id (S₁.R (rg .acc))},
    m₁+(2*(S₁.R (rg .acc)).length+2), st', hp, hu₂.trans hu₁, ?_, ?_, ?_, ?_, hf₁.1, hf₁.2.1,
    hf₁.2.2.1, fun k hk1 hk2 => ?_⟩
  · rw [hacc₁]; omega
  · intro depth
    have hs := hS.stock_balance v v₁ hS₁ hf₁
    have hmove : mnNativePushBound 1 (moveR (P := P) (Q := Q) (A := A) (U := U)
        (rg .acc) out id) := by
      simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
    refine .seq ((he₁ depth).mono (by intro d z hz; omega)) ?_
    apply mn_native_exec_within he₂ 1 hmove depth
    rw [hacc₁]
    omega
  · simp only [movedR, List.map_id, Function.update_self, hacc₁]
    rw [hf₁.2.2.2 out hout]
  · intro r
    simp only [movedR, List.map_id]
    rw [Function.update_of_ne (hout r)]
    by_cases hr : r = .acc
    · subst hr; simp [tblRho]
    · rw [Function.update_of_ne (hrg.ne hr), hS₁ r]
      cases r <;> simp_all [tblRho]
  · simp only [movedR, List.map_id]
    rw [Function.update_of_ne hk1, Function.update_of_ne (Ne.symm (hk2 .acc)), hf₁.2.2.2 k hk2]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
