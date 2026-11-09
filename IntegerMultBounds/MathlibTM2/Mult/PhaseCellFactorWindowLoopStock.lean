module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindowStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScanInvariantStock
public import IntegerMultBounds.MathlibTM2.Host.CursorOutputStock

/-! Window rows share one lookup reserve above the retained page output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem factorWindowLoop_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W start L : ℕ)
    (depth : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hrow : (S.R 108).length = start+L) (hcolumn : S.R 107 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = []) (hcount : (S.R 111).length = L)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = []) (h112 : S.R 112 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorWindowLoopCost q W B.card start L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+L*((2*W+1)*(2*q+8))+depth+
        factorRowWorkspace q W B.card 0 (start+L)) depth factorWindowLoop (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 108 ((S.R 108).drop L)) 140
          (cstream A (2*q+8) ((List.range' start L).flatMap (fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)))++S.R 140))}) := by
  let F := fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)
  let Ψ : ℕ → Regs 154 A := fun i => Function.update (Function.update S.R 108 ((S.R 108).drop i))
    140 (cstream A (2*q+8) ((List.range' (start+L-i) i).flatMap F)++S.R 140)
  let growth := (2*W+1)*(2*q+8)
  let boundary := fun i => mnSize (mk v S)+i*growth
  let bound := boundary L
  let reserve := factorRowWorkspace q W B.card 0 (start+L)
  have hboundary : ∀ i ≤ L, boundary i ≤ bound := by
    intro i hi
    exact Nat.add_le_add_left (Nat.mul_le_mul_right growth hi) _
  have hstep : InvariantBoundedStockSpec body factorWindowStep 111 112
      (fun i R => ∀ k, k ≠ 111 → k ≠ 112 → R k = Ψ i k) S.L
      (fun i => 1+factorRowCost q W B.card 0 (start+L-(i+1)))
      boundary L bound reserve depth := by
    intro i hi vi Si _ hSi hsize
    have hoff (k : Fin 154) (hk108 : k ≠ 108) (hk140 : k ≠ 140) (hk111 : k ≠ 111) (hk112 : k ≠ 112) :
        Si.R k = S.R k := by rw [hSi k hk111 hk112]; simp [Ψ,hk108,hk140]
    have hcursor : (Si.R 108).length = start+L-(i+1)+1 := by
      rw [hSi 108 (by decide) (by decide)]
      simp only [Ψ,Function.update_of_ne (show (108 : Fin 154) ≠ 140 by decide),Function.update_self,List.length_drop,hrow]
      omega
    obtain ⟨vi',steps,hu,hs,he⟩ := factorWindowStep_exec_within (body := body) B q W (start+L-(i+1)) columns hlen hformat hA
      tail vi Si (by rw [hoff 119 (by decide) (by decide) (by decide) (by decide)]; exact hq)
      (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact hW)
      (by rw [hoff 116 (by decide) (by decide) (by decide) (by decide)]; exact hN)
      (by rw [hoff 107 (by decide) (by decide) (by decide) (by decide)]; exact hcolumn) hcursor
      (by rw [hoff 105 (by decide) (by decide) (by decide) (by decide)]; exact h105)
      (by rw [hoff 106 (by decide) (by decide) (by decide) (by decide)]; exact h106)
      (by rw [hoff 132 (by decide) (by decide) (by decide) (by decide)]; exact hsource)
      (by rw [hoff 0 (by decide) (by decide) (by decide) (by decide)]; exact h0) (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hoff _ (by decide) (by decide) (by decide) (by decide)] <;> exact hfresh _ (by simp)) (by
        intro k hk1 hk7
        rw [hoff k (by omega) (by omega) (by omega) (by omega)]
        exact hblank k hk1 hk7) depth
    let R' := Function.update (Function.update Si.R 108 (Si.R 108).tail) 140
      (cstream A (2*q+8) (F (start+L-(i+1)))++Si.R 140)
    have hcap := factorRowWorkspace_mono q W B.card 0 0 (start+L-(i+1)) (start+L) le_rfl (Nat.sub_le _ _)
    have hbound := hsize.trans (hboundary i hi.le)
    have ht := he.mono (J := fun d z => mnSize z+d ≤ bound+depth+reserve)
      (by intro d z hz; dsimp only [reserve]; omega)
    refine ⟨vi',R',steps,hu,hs,ht,by simp [R'],by simp [R'],?_,?_⟩
    · intro k hk111 hk112
      by_cases hk108 : k = 108
      · subst k
        rw [show R' 108 = (Si.R 108).tail by simp [R'],hSi 108 (by decide) (by decide)]
        simp [Ψ,List.tail_drop]
      by_cases hk140 : k = 140
      · subst k
        rw [show R' 140 = cstream A (2*q+8) (F (start+L-(i+1)))++Si.R 140 by simp [R'],hSi 140 (by decide) (by decide)]
        have hnext : start+L-(i+1)+1 = start+L-i := by omega
        simp [Ψ,List.range'_succ,hnext,List.flatMap_cons,cstream_append,List.append_assoc]
      rw [show R' k = Si.R k by simp [R',hk108,hk140],hSi k hk111 hk112]
      simp [Ψ,hk108,hk140]
    · have hg := mn_tail_prepend_size_le (108 : Fin 154) 140 (by decide) vi vi' Si
        (cstream A (2*q+8) (F (start+L-(i+1))))
      have hpacket : (cstream A (2*q+8) (F (start+L-(i+1)))).length = growth := by simp [F,growth]
      rw [hpacket] at hg
      change mnSize (mk vi' {Si with R := R'}) ≤ boundary (i+1)
      change mnSize (mk vi' {Si with R := R'}) ≤ mnSize (mk vi Si)+growth at hg
      dsimp only [boundary] at hsize ⊢
      rw [Nat.add_mul,Nat.one_mul]
      omega
  obtain ⟨v',steps,hu,hs,he⟩ := factorWindowLoop_exec (body := body) B q W start L columns hlen hformat hA
    tail v S hq hW hN hrow hcolumn h105 h106 hcount hsource h0 h112 hfresh hblank
  refine ⟨v',steps,hu,hs,?_⟩
  apply scanInvariant_within_bounded_stock (by decide : (111 : Fin 154) ≠ 112)
    (Inv := fun i R => ∀ k, k ≠ 111 → k ≠ 112 → R k = Ψ i k)
    (by intro i R R' hframe hR k h111 h112; rw [hframe k h111 h112]; exact hR k h111 h112)
    hboundary hstep 0 v S (by simp [hcount]) rfl ?_ (by simp [boundary]) he
  intro k _ _
  by_cases hk108 : k = 108 <;> by_cases hk140 : k = 140 <;> simp [Ψ,hk108,hk140]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
