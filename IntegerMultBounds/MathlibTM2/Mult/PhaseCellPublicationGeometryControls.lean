module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCoreDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Derive the two remaining publication controls from retained binary geometry.
The radius is temporary; only core and ambient length remain after setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

namespace PublicationGeometryControls

def program (e : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (prepareCoreDimensions (e 1) (e 2) (e 5) (e 3) (e 6) (e 7) (e 8))
    (.seq (toUnary (e 0) (e 4) (e 6) (e 7) (e 8)) (uclear (e 5)))

def timeCost (V s L radius : ℕ) := prepareCoreDimensionsCost V L radius+(6*s+11*V+6)+(2*radius+2)

def loaded (e : Fin 9 → Fin T) (s L : ℕ) (S : Stacks T A) :=
  {S with R := (Function.update (Function.update S.R (e 3) (List.replicate L tick))
    (e 4) (List.replicate s tick))}

theorem loaded_off (e : Fin 9 → Fin T) (s L : ℕ) (S : Stacks T A) (k : Fin T)
    (h3 : k ≠ e 3) (h4 : k ≠ e 4) : (loaded e s L S).R k = S.R k := by
  simp only [loaded,Function.update_of_ne h3,Function.update_of_ne h4]

theorem loaded_update_off (e : Fin 9 → Fin T) (s L : ℕ) (S : Stacks T A) (k : Fin T)
    (xs : List (Fin (A+4))) (h3 : e 3 ≠ k) (h4 : e 4 ≠ k) :
    loaded e s L {S with R := Function.update S.R k xs} =
      {loaded e s L S with R := Function.update (loaded e s L S).R k xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  simp only [loaded]
  rw [Function.update_comm h3.symm,Function.update_comm h4.symm]

theorem native (e : Fin 9 → Fin T) : mnNativePushBound 3 (program (P := P) (Q := Q) (A := A) (U := U) e) := by
  simp [program,prepareCoreDimensions,toUnary,hornerIter,udbl,eachSym,discardPrefix,
    uclear,transfer,scanR,transferAct,drainR,popDo,pushN,moveR,moveStep,whileR,peekR,popPush,
    keepIn,mnNativePushBound,mnActPush]

theorem exec_within (body : P → Pr P T Q A U) (e : Fin 9 → Fin T) (he : Function.Injective e)
    (V s L radius : ℕ) (hsV : s < 2^V) (hrV : radius < 2^V) (hLV : L+2*radius < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R (e 0) = binSyms V s) (hr : S.R (e 1) = binSyms V radius)
    (hL : S.R (e 2) = binSyms V (L+2*radius))
    (hblank : ∀ j ∈ [(3 : Fin 9),4,5,6,7,8], S.R (e j) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ timeCost V s (L+2*radius) radius ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*timeCost V s (L+2*radius) radius)
        depth (program e) (mk v S) n (mk v' (loaded e s L S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareCoreDimensions_exec (body := body)
    (radiusWord := e 1) (lengthWord := e 2) (radius := e 5) (rows := e 3)
    (work := e 6) (saved := e 7) (tmp := e 8)
    (by simp [List.nodup_cons,he.eq_iff]) V L radius hrV hLV v S hr hL
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        all_goals exact hblank _ (by simp))
  let B : Stacks T A := {S with R := (Function.update (Function.update S.R (e 5)
    (List.replicate radius tick)) (e 3) (List.replicate L tick))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear (body := body)
    (a := e 0) (z := e 4) (w := e 6) (t := e 7) (t₂ := e 8)
    (by simp [List.nodup_cons,he.eq_iff]) hsV v₁ B
    (by simpa [B,he.eq_iff] using hs)
    (by simpa [B,he.eq_iff] using hblank 6 (by simp))
    (by simpa [B,he.eq_iff] using hblank 7 (by simp))
    (by simpa [B,he.eq_iff] using hblank 8 (by simp))
  let C : Stacks T A := {B with R := Function.update B.R (e 4) (List.replicate s tick)}
  have he₂' : Exec body (toUnary (e 0) (e 4) (e 6) (e 7) (e 8)) (mk v₁ B) n₂ (mk v₂ C) := by
    simpa [C,B,he.eq_iff,hblank 4 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (e 5) v₂ C
  have hlen : (C.R (e 5)).length = radius := by simp [C,B,he.eq_iff]
  rw [hlen] at he₃
  have hend : {C with R := Function.update C.R (e 5) []} = loaded e s L S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = e 5
    · subst k; simp [C,B,loaded,he.eq_iff,hblank 5 (by simp)]
    · simp [C,B,loaded,Function.update_apply,hk]
  rw [hend] at he₃
  have hx : Exec body (program e) (mk v S) (n₁+(n₂+(2*radius+2))) (mk v₃ (loaded e s L S)) :=
    Exec.seq he₁ (Exec.seq he₂' he₃)
  have hn : n₁+(n₂+(2*radius+2)) ≤ timeCost V s (L+2*radius) radius := by
    unfold timeCost
    omega
  exact ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hn,mn_native_exec_within hx 3 (native e) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn) _)⟩

theorem after_update_exec_within (body : P → Pr P T Q A U) (e : Fin 9 → Fin T) (he : Function.Injective e)
    (V s L radius : ℕ) (hsV : s < 2^V) (hrV : radius < 2^V) (hLV : L+2*radius < 2^V)
    (k : Fin T) (xs : List (Fin (A+4))) (hoff : ∀ j, e j ≠ k)
    (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R (e 0) = binSyms V s) (hr : S.R (e 1) = binSyms V radius)
    (hL : S.R (e 2) = binSyms V (L+2*radius))
    (hblank : ∀ j ∈ [(3 : Fin 9),4,5,6,7,8], S.R (e j) = []) (depth : ℕ) :
    let F := {S with R := Function.update S.R k xs}
    let D := loaded e s L S
    ∃ v' n, v'.user = v.user ∧ n ≤ timeCost V s (L+2*radius) radius ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+3*timeCost V s (L+2*radius) radius)
        depth (program e) (mk v F) n (mk v' {D with R := Function.update D.R k xs}) := by
  dsimp only
  let F := {S with R := Function.update S.R k xs}
  have hread (j) : F.R (e j) = S.R (e j) := Function.update_of_ne (hoff j) _ _
  obtain ⟨v',n,hu,hn,hx⟩ := exec_within body e he V s L radius hsV hrV hLV v F
    (by rw [hread]; exact hs) (by rw [hread]; exact hr) (by rw [hread]; exact hL)
    (by intro j hj; rw [hread]; exact hblank j hj) depth
  rw [loaded_update_off e s L S k xs (hoff 3) (hoff 4)] at hx
  exact ⟨v',n,hu,hn,hx⟩

theorem retire_exec_within (body : P → Pr P T Q A U) (e : Fin 9 → Fin T) (he : Function.Injective e)
    (s L : ℕ) (output : Fin T) (h3 : output ≠ e 3) (h4 : output ≠ e 4)
    (ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hblank3 : S.R (e 3) = []) (hblank4 : S.R (e 4) = []) (depth : ℕ) :
    let D := loaded e s L S
    let F := {D with R := Function.update D.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords [e 3,e 4]) (mk v F) (2*(L+s)+5)
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  let D := loaded e s L S
  let F := {D with R := Function.update D.R output ys}
  obtain ⟨v',hu,hx⟩ := clearWords_exec (body := body) [e 3,e 4] (by simp [he.eq_iff]) v F
  have hcost : 2*(([e 3,e 4].map (fun j => (F.R j).length)).sum)+2*[e 3,e 4].length+1 = 2*(L+s)+5 := by
    simp [F,D,loaded,h3.symm,h4.symm,he.eq_iff]
  rw [hcost] at hx
  have hend : {F with R := fun j => if j ∈ [e 3,e 4] then [] else F.R j} =
      {S with R := Function.update S.R output ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj3 : j = e 3
    · subst j; simp [h3.symm,hblank3]
    by_cases hj4 : j = e 4
    · subst j; simp [h4.symm,hblank4]
    · simp [F,D,loaded,hj3,hj4,Function.update_apply]
  rw [hend] at hx
  exact ⟨v',hu,mn_native_exec_within hx 0 (clearWords_native _) depth _ (by simp only [Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end PublicationGeometryControls
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
