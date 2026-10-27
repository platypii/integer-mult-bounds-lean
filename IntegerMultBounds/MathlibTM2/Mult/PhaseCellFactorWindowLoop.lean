module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWindowStep

/-! Emit start-zero window rows in ascending order, retaining the outer scan controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorWindowLoop : Pr P 154 Q A U := scanP 111 112 factorWindowStep

def factorWindowLoopCost (q W N start L : ℕ) : ℕ :=
  (∑ i ∈ Finset.range L, (1+factorRowCost q W N 0 (start+L-(i+1))+3))+2*L+4

theorem factorWindowLoop_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W start L : ℕ)
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
      Exec body factorWindowLoop (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 108 ((S.R 108).drop L)) 140
          (cstream A (2*q+8) ((List.range' start L).flatMap (fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)))++S.R 140))}) := by
  let F := fun m => (List.range' 0 (2*W+1)).map (fun n => factorRankWord B W columns n m)
  let Ψ : ℕ → Regs 154 A := fun i => Function.update (Function.update S.R 108 ((S.R 108).drop i))
    140 (cstream A (2*q+8) ((List.range' (start+L-i) i).flatMap F)++S.R 140)
  have hstep : IterSpec body factorWindowStep 111 112 Ψ
      (fun i => 1+factorRowCost q W B.card 0 (start+L-(i+1))) L := by
    intro i hi vi Si hSi
    have hoff (k : Fin 154) (hk108 : k ≠ 108) (hk140 : k ≠ 140) (hk111 : k ≠ 111) (hk112 : k ≠ 112) :
        Si.R k = S.R k := by rw [hSi k hk111 hk112]; simp [Ψ,hk108,hk140]
    have hcursor : (Si.R 108).length = start+L-(i+1)+1 := by
      rw [hSi 108 (by decide) (by decide)]
      simp only [Ψ,Function.update_of_ne (show (108 : Fin 154) ≠ 140 by decide),Function.update_self,List.length_drop,hrow]
      omega
    obtain ⟨vi',steps,hu,hs,he⟩ := factorWindowStep_exec (body := body) B q W (start+L-(i+1)) columns hlen hformat hA
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
        exact hblank k hk1 hk7)
    let R' := Function.update (Function.update Si.R 108 (Si.R 108).tail) 140
      (cstream A (2*q+8) (F (start+L-(i+1)))++Si.R 140)
    refine ⟨vi',R',steps,hu,hs,he,by simp [R'],by simp [R'],?_⟩
    intro k hk111 hk112
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
  obtain ⟨v',R',steps,hu,hs,he,h111,h112',hrest⟩ := scanP_exec (body := body)
    (show (111 : Fin 154) ≠ 112 by decide) hstep 0 v S (by simp [hcount]) (by
      intro k _ _
      by_cases hk108 : k = 108 <;> by_cases hk140 : k = 140 <;> simp [Ψ,hk108,hk140])
  have hR : R' = Ψ L := by
    funext k
    by_cases hk111 : k = 111
    · subst k; simpa [Ψ,h112] using h111
    by_cases hk112 : k = 112
    · subst k; simpa [Ψ,h112] using h112'
    simpa [hcount] using hrest k hk111 hk112
  rw [hR] at he
  refine ⟨v',steps,hu,?_,?_⟩
  · simpa [factorWindowLoopCost,hcount,h112] using hs
  · simpa [factorWindowLoop,Ψ,F] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
