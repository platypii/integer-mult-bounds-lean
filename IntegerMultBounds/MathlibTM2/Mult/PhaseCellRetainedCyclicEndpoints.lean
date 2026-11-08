module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSplitRulers
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankRoleCode

/-! Turn ordinary start/span rulers into the retained cyclic solver endpoints. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def cyclicEndpointBase (r : TblR 7) : Fin 154 := ⟨(ForwardBankPlacement.code r).val,by
  have := (ForwardBankPlacement.code r).isLt; omega⟩
def cyclicEndpointReg (r : TblR 7) : Fin 154 := Equiv.swap 7 115 (cyclicEndpointBase r)

theorem cyclicEndpointReg_injective : Function.Injective cyclicEndpointReg := by
  apply (Equiv.injective (Equiv.swap _ _)).comp
  intro r t h
  apply ForwardBankPlacement.code_injective
  exact Fin.ext (congrArg (fun k : Fin 154 => k.val) h)

theorem cyclicEndpointReg_low (r : TblR 7) (hr : r ≠ .wr) : (cyclicEndpointReg r).val < 22 := by
  have hbound : (cyclicEndpointBase r).val < 22 := (ForwardBankPlacement.code r).isLt
  have h7 : cyclicEndpointBase r ≠ 7 := by
    intro h
    apply hr
    apply ForwardBankPlacement.code_injective
    exact Fin.ext (congrArg (fun k : Fin 154 => k.val) h)
  have h115 : cyclicEndpointBase r ≠ 115 := by intro h; have := congrArg Fin.val h; omega
  simpa [cyclicEndpointReg,Equiv.swap_apply_def,h7,h115] using hbound

theorem cyclicEndpointReg_off (k : Fin 154) (hk : 22 ≤ k.val) (h115 : k ≠ 115) :
    ∀ r, cyclicEndpointReg r ≠ k := by
  intro r h
  by_cases hr : r = .wr
  · subst r; exact h115 h.symm
  · have hh := cyclicEndpointReg_low r hr
    rw [h] at hh
    omega

def retainedCyclicEndpoints : Pr P 154 Q A U :=
  .seq (ucopy 141 144 135)
    (.seq (cyclicSplitRulers cyclicEndpointReg 22 23 24 25 26 121 141 142 145 146) (clearWords [141,142]))

def retainedCyclicEndpointsCost (R : Regs 154 A) (V a n : ℕ) : ℕ :=
  (4*a+4)+(cyclicSplitRulersCost R V a n 121 141 142+(2*(a+n)+5))

theorem retainedCyclicEndpoints_exec (V s a n : ℕ) (ha : a ≤ s) (hn : n ≤ s) (hwide : s < 2^V)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hs : (S.R 121).length = s) (haSrc : (S.R 141).length = a) (hnSrc : (S.R 142).length = n)
    (hwidth : (S.R 115).length = V)
    (hfresh : ∀ k ∈ [(135 : Fin 154),144,145,146], S.R k = [])
    (hlow : ∀ k : Fin 154, k.val < 27 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedCyclicEndpointsCost S.R V a n ∧
      Exec body retainedCyclicEndpoints (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R 141 []) 142 []) 144 (List.replicate a tick))
            145 (List.replicate (a+min n (s-a)) tick)) 146 (List.replicate (n-min n (s-a)) tick))}) := by
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec body (a := 141) (b := 144) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let F : Stacks 154 A := {S with R := Function.update S.R 144 (List.replicate a tick)}
  have he₁' : Exec body (ucopy 141 144 135) (mk v S) (4*a+4) (mk v₁ F) := by
    simpa [F,haSrc,hfresh 144 (by simp)] using he₁
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := cyclicSplitRulers_exec (body := body)
    cyclicEndpointReg cyclicEndpointReg_injective 22 23 24 25 26 121 141 142
    (cyclicEndpointReg_off 22 (by decide) (by decide)) (by decide)
    145 146 (by intro r; exact ⟨cyclicEndpointReg_off 145 (by decide) (by decide) r,
      cyclicEndpointReg_off 146 (by decide) (by decide) r⟩)
    V s a n ha hn hwide (S.R 115) hwidth v₁ F
    (by simpa [F] using hs) (by simpa [F] using haSrc) (by simpa [F] using hnSrc)
    (by simp [F,cyclicEndpointReg,cyclicEndpointBase,ForwardBankPlacement.code])
    (by intro r hr; have hh := cyclicEndpointReg_low r hr
        simpa [F,show cyclicEndpointReg r ≠ 144 by intro h; rw [h] at hh; omega] using hlow _ (by omega))
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simpa [F] using hlow _ (by decide))
  let G : Stacks 154 A := {F with R := cyclicEndpointR s a n 145 146 F.R}
  obtain ⟨v₃,hv₃,he₃⟩ := clearWords_exec (body := body) [(141 : Fin 154),142] (by decide) v₂ G
  have hlen : ([(141 : Fin 154),142].map (fun k => (G.R k).length)).sum = a+n := by
    simp [G,F,cyclicEndpointR,cyclicEndpointCopies,unaryCopiesR,haSrc,hnSrc]
  have hcost : m₂ ≤ cyclicSplitRulersCost S.R V a n 121 141 142 := by
    simpa [F,cyclicSplitRulersCost,binaryHeaderQueueCost] using hm₂
  refine ⟨v₃,(4*a+4)+(m₂+(2*(a+n)+5)),hv₃.trans (hv₂.trans hv₁),
    Nat.add_le_add_left (Nat.add_le_add_right hcost _) _,
    (Exec.seq he₁' (Exec.seq (he₂ 0).toExec he₃)).cast (by rw [hlen]; rfl) ?_⟩
  apply congrArg (mk v₃)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    simp [G,F,cyclicEndpointR,cyclicEndpointCopies,unaryCopiesR,cyclicEndpointValues,
      hfresh 145 (by simp),hfresh 146 (by simp),Function.update_apply]
    split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
