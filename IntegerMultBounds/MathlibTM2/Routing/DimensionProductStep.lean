module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadUnaryDimension
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup
public import IntegerMultBounds.MathlibTM2.NativePushBoundMono

/-! One fixed metadata-product step: read a dimension, multiply the retained
accumulator, and retire the factor and product work words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DimensionProductStep
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz FieldHeaderSetup
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

def run (r : Fin 11 → Fin T) : Pr J T Q A U :=
  .seq (readUnaryDimension (r 0) (r 1) (r 2) (r 6) (r 4) (r 7) (r 8) (r 9) (r 10))
    (.seq (resetProduct (r 3) (r 4) (r 5) (r 9) (r 10))
      (.seq (uclear (r 3)) (.seq (moveR (r 5) (r 3) id) (uclear (r 4)))))

def cost (V a x : ℕ) := 6*(a*x)+11*a+14*x+19*V+36

def result (r : Fin 11 → Fin T) (S : Stacks T A) (a x : ℕ) (tail : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate (a*x) tick))}

private theorem ports_nodup (r : Fin 11 → Fin T) (hr : Function.Injective r) :
    [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,r 9,r 10].Nodup := by
  simp [List.nodup_cons,hr.eq_iff]

theorem run_exec (r : Fin 11 → Fin T) (hr : Function.Injective r) (V a x : ℕ) (hfit : x < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R (r 0)).length = V) (hz : S.R (r 1) = [])
    (ha : (S.R (r 3)).length = a) (hq : S.R (r 2) = binSyms V x++tail)
    (hf : ∀ j ∈ [(4 : Fin 11),5,6,7,8,9,10], S.R (r j) = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost V a x ∧
      Exec body (run r) (mk v S) n (mk vf (result r S a x tail)) := by
  have hd := ports_nodup r hr
  regs_ne hd
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readUnaryDimension_exec (body := body)
    (r 0) (r 1) (r 2) (r 6) (r 4) (r 7) (r 8) (r 9) (r 10) (by regs_nodup)
    V x hfit tail v S hV hz hq (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hf _ (by simp))
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R (r 2) tail) (r 4) (List.replicate x tick))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) (r 3) (r 4) (r 5) (r 9) (r 10)
    (by regs_nodup) v₁ F (by simp [F,hr.eq_iff,hf]) (by simp [F,hr.eq_iff,hf])
  have hn₂' : n₂ ≤ a*(4*x+9)+6 := by simp [F,hr.eq_iff,ha,hf] at hn₂; omega
  let G : Stacks T A := {F with R := Function.update F.R (r 5) (List.replicate (a*x) tick)}
  have he₂' : Exec body (resetProduct (r 3) (r 4) (r 5) (r 9) (r 10)) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [F,hr.eq_iff,ha] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (r 3) v₂ G
  have hGa : (G.R (r 3)).length = a := by simp [G,F,hr.eq_iff,ha]
  rw [hGa] at he₃
  let H : Stacks T A := {G with R := Function.update G.R (r 3) []}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) (r 5) (r 3) (hr.ne (by decide)) id v₃ H
  let K : Stacks T A := {H with R := movedR H.R (r 5) (r 3) id (H.R (r 5))}
  have hprod : H.R (r 5) = List.replicate (a*x) tick := by simp [H,G,hr.eq_iff]
  have hxa : (K.R (r 4)).length = x := by simp [K,movedR,H,G,F,hr.eq_iff]
  obtain ⟨vf,hu₅,he₅⟩ := uclear_exec (body := body) (r 4) v₄ K
  rw [hxa] at he₅
  have hfinal : {K with R := Function.update K.R (r 4) []} = result r S a x tail := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases h4 : j = r 4
    · subst j; simp [result,hr.eq_iff,hf]
    by_cases h5 : j = r 5
    · subst j; simp [K,movedR,result,hr.eq_iff,hf]
    by_cases h3 : j = r 3
    · subst j; simp [K,movedR,H,G,result,hr.eq_iff]
    · simp [K,movedR,H,G,F,result,h3,h4,h5,Function.update_apply]
  refine ⟨vf,n₁+(n₂+((2*a+2)+((2*(a*x)+2)+(2*x+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
  · dsimp only [cost,readUnaryDimensionCost] at *
    nlinarith only [hn₁,hn₂']
  · have he₄' : Exec body (moveR (r 5) (r 3) id) (mk v₃ H) (2*(a*x)+2) (mk v₄ K) := by
      simpa [K,hprod] using he₄
    exact (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅)))).cast rfl (congrArg (mk vf) hfinal)

theorem run_native (r : Fin 11 → Fin T) : mnNativePushBound 3 (run (J := J) (Q := Q) (A := A) (U := U) r) := by
  refine ⟨readUnaryDimension_native _ _ _ _ _ _ _ _ _,
    mnNativePushBound_mono (by omega) (resetProduct_pushBound _ _ _ _ _),?_,?_,?_⟩ <;>
    simp [uclear,drainR,popDo,peekR,moveR,whileR,moveStep,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.DimensionProductStep
