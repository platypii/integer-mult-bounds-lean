module

public import IntegerMultBounds.MathlibTM2.Routing.DimensionProduct
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy

/-! Initialize a product header to one, copy the retained factor count to a
private clock, and consume the binary dimensions with the fixed product loop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DimensionProductPrepare
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main FieldHeaderCopy
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

def run (r : Fin 11 → Fin T) (count source : Fin T) : Pr J T Q A U :=
  .seq (.act (.push (.rt (r 3)) (fun _ => tick) .done))
    (.seq (resetCopy source count (r 9)) (DimensionProduct.run r count))

def cost (V : ℕ) (xs : List ℕ) := 4*xs.length+7+DimensionProduct.cost V 1 xs

theorem run_native (r : Fin 11 → Fin T) (count source : Fin T) :
    mnNativePushBound 3 (run (J := J) (Q := Q) (A := A) (U := U) r count source) := by
  exact ⟨by simp [mnNativePushBound,mnActPush],
    mnNativePushBound_mono (by omega) (resetCopy_pushBound _ _ _),DimensionProduct.run_native _ _⟩

theorem run_exec (r : Fin 11 → Fin T) (hr : Function.Injective r) (count source : Fin T)
    (hc : ∀ j, count ≠ r j) (hs : ∀ j, source ≠ r j) (hsc : source ≠ count)
    (V : ℕ) (xs : List ℕ) (hpos : ∀ x ∈ xs, 0 < x) (hfit : ∀ x ∈ xs, x < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R (r 0)).length = V) (hz : S.R (r 1) = [])
    (hsrc : (S.R source).length = xs.length) (hcount : S.R count = []) (hacc : S.R (r 3) = [])
    (hqueue : S.R (r 2) = xs.flatMap (binSyms V)++tail)
    (hf : ∀ j ∈ [(4 : Fin 11),5,6,7,8,9,10], S.R (r j) = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost V xs ∧
      Exec body (run r count source) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate xs.prod tick))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost V xs)
        depth (run r count source) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate xs.prod tick))})) := by
  let F : Stacks T A := {S with R := Function.update S.R (r 3) [tick]}
  have he₁ : Exec body (.act (.push (.rt (r 3)) (fun _ => tick) .done)) (mk v S) 1 (mk v F) := by
    simpa [F,Action.run,update_rt,hacc] using
      (Exec.act (body := body) (.push (.rt (r 3)) (fun _ => tick) .done) (mk v S))
  obtain ⟨v₁,hu₁,he₂⟩ := resetCopy_exec (body := body) source count (r 9)
    (by simp [List.nodup_cons,hsc,hs,hc]) v F (by simp [F,hr.eq_iff,hf])
  let G : Stacks T A := {F with R := Function.update F.R count (List.replicate xs.length tick)}
  have he₂' : Exec body (resetCopy source count (r 9)) (mk v F) (4*xs.length+6) (mk v₁ G) := by
    simpa [F,hs,hc,hsrc,hcount] using he₂
  obtain ⟨vf,n,hu₂,hn,he₃⟩ := DimensionProduct.run_exec (body := body) r hr count hc V 1 (by decide) xs hpos hfit
    tail v₁ G (by simp [G,F,(hc 0).symm,hr.eq_iff,hV])
    (by simp [G,F,(hc 1).symm,hr.eq_iff,hz]) (by simp [G,F,(hc 3).symm]) (by simp [G])
    (by simp [G,F,(hc 2).symm,hr.eq_iff,hqueue]) (by
      intro j hj
      have hj3 : j ≠ 3 := by intro he; subst j; simp at hj
      simpa [G,F,(hc j).symm,hr.ne hj3] using hf j hj)
  simp only [Nat.one_mul] at he₃
  have hfinal : {G with R := (Function.update (Function.update (Function.update G.R
      (r 2) tail) (r 3) (List.replicate xs.prod tick)) count [])} =
      {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate xs.prod tick))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j = count
    · subst j; simp [hc,hcount]
    by_cases hj2 : j = r 2
    · subst j; simp [hj,hr.eq_iff]
    by_cases hj3 : j = r 3
    · subst j; simp [hj]
    · simp [G,F,hj,hj2,hj3]
  have he := (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl (congrArg (mk vf) hfinal)
  refine ⟨vf,1+((4*xs.length+6)+n),hu₂.trans hu₁,by dsimp [cost]; omega,he,?_⟩
  intro depth
  exact mn_native_exec_within he 3 (run_native _ _ _) depth _ (by dsimp [cost]; omega)

end IntegerMultBounds.MathlibTM2.Routing.DimensionProductPrepare
