module

public import IntegerMultBounds.MathlibTM2.Routing.DimensionProductPacket

/-! Three metadata packets produce the halo-prefix, full-move prefix and
spectator counts on their actual ports. One product workspace serves all three. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedCountHeaders
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def ports (dst : Fin 117) : Fin 11 → Fin 117 := ![115,116,72,dst,74,78,73,75,76,57,58]
def blank : List (Fin 117) := [64,70,71,73,74,75,76,78,79,80,57,58]

theorem ports_injective (dst : Fin 117) (hd : dst ∈ [(64 : Fin 117),70,71]) : Function.Injective (ports dst) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide +kernel

theorem count_disjoint (dst : Fin 117) (hd : dst ∈ [(64 : Fin 117),70,71]) :
    (∀ j, (79 : Fin 117) ≠ ports dst j) ∧ (∀ j, (80 : Fin 117) ≠ ports dst j) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide +kernel

def run : Pr J 117 Q A U := .seq (DimensionProductPacket.run (ports 64) 79 80)
  (.seq (DimensionProductPacket.run (ports 70) 79 80) (DimensionProductPacket.run (ports 71) 79 80))

def cost (V : ℕ) (xs ys zs : List ℕ) := DimensionProductPacket.cost V xs+
  DimensionProductPacket.cost V ys+DimensionProductPacket.cost V zs

def result (S : Stacks 117 A) (xs ys zs : List ℕ) (tail : List (Fin (A+4))) : Stacks 117 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    72 tail) 64 (List.replicate xs.prod tick)) 70 (List.replicate ys.prod tick)) 71 (List.replicate zs.prod tick))}

theorem run_native : mnNativePushBound 3 (run (J := J) (Q := Q) (A := A) (U := U)) :=
  ⟨DimensionProductPacket.run_native _ _ _,DimensionProductPacket.run_native _ _ _,DimensionProductPacket.run_native _ _ _⟩

theorem run_exec (V : ℕ) (xs ys zs : List ℕ)
    (hp : ∀ x ∈ xs++ys++zs, 0 < x) (hfit : ∀ x ∈ xs++ys++zs, x < 2^V)
    (hcount : ∀ ds ∈ [xs,ys,zs], ds.length < 2^V)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hz : S.R 116 = []) (hb : ∀ j ∈ blank, S.R j = [])
    (hq : S.R 72 = DimensionProductPacket.packet A V xs++DimensionProductPacket.packet A V ys++
      DimensionProductPacket.packet A V zs++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost V xs ys zs ∧
      Exec body run (mk v S) n (mk vf (result S xs ys zs tail)) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost V xs ys zs)
        depth run (mk v S) n (mk vf (result S xs ys zs tail))) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,_⟩ := DimensionProductPacket.run_exec (body := body) (ports 64)
    (ports_injective 64 (by simp)) 79 80 (count_disjoint 64 (by simp)).1 (count_disjoint 64 (by simp)).2 (by decide)
    V xs (fun x hx => hp x (by simp [hx])) (fun x hx => hfit x (by simp [hx]))
    (hcount xs (by simp)) (DimensionProductPacket.packet A V ys++DimensionProductPacket.packet A V zs++tail)
    v S (by simpa [ports] using hV) (by simpa [ports] using hz)
    (hb _ (by simp [blank])) (hb _ (by simp [blank])) (by simpa [ports] using hb 64 (by simp [blank]))
    (by simpa [ports,List.append_assoc] using hq) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ports] <;> exact hb _ (by simp [blank]))
  let F : Stacks 117 A := {S with R := (Function.update (Function.update S.R 72
    (DimensionProductPacket.packet A V ys++DimensionProductPacket.packet A V zs++tail)) 64 (List.replicate xs.prod tick))}
  have he₁' : Exec body (DimensionProductPacket.run (ports 64) 79 80) (mk v S) n₁ (mk v₁ F) := by
    simpa [ports,F,List.append_assoc] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,_⟩ := DimensionProductPacket.run_exec (body := body) (ports 70)
    (ports_injective 70 (by simp)) 79 80 (count_disjoint 70 (by simp)).1 (count_disjoint 70 (by simp)).2 (by decide)
    V ys (fun x hx => hp x (by simp [hx])) (fun x hx => hfit x (by simp [hx]))
    (hcount ys (by simp)) (DimensionProductPacket.packet A V zs++tail) v₁ F
    (by simpa [ports,F] using hV) (by simpa [ports,F] using hz)
    (by simpa [F] using hb 79 (by simp [blank])) (by simpa [F] using hb 80 (by simp [blank]))
    (by simpa [ports,F] using hb 70 (by simp [blank])) (by simp [ports,F,List.append_assoc]) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ports,F] <;> exact hb _ (by simp [blank]))
  let G : Stacks 117 A := {F with R := (Function.update (Function.update F.R 72
    (DimensionProductPacket.packet A V zs++tail)) 70 (List.replicate ys.prod tick))}
  have he₂' : Exec body (DimensionProductPacket.run (ports 70) 79 80) (mk v₁ F) n₂ (mk v₂ G) := by simpa [ports] using he₂
  obtain ⟨vf,n₃,hu₃,hn₃,he₃,_⟩ := DimensionProductPacket.run_exec (body := body) (ports 71)
    (ports_injective 71 (by simp)) 79 80 (count_disjoint 71 (by simp)).1 (count_disjoint 71 (by simp)).2 (by decide)
    V zs (fun x hx => hp x (by simp [hx])) (fun x hx => hfit x (by simp [hx]))
    (hcount zs (by simp)) tail v₂ G
    (by simpa [ports,G,F] using hV) (by simpa [ports,G,F] using hz)
    (by simpa [G,F] using hb 79 (by simp [blank])) (by simpa [G,F] using hb 80 (by simp [blank]))
    (by simpa [ports,G,F] using hb 71 (by simp [blank])) (by simp [ports,G]) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ports,G,F] <;> exact hb _ (by simp [blank]))
  have hfinal : {G with R := (Function.update (Function.update G.R 72 tail) 71 (List.replicate zs.prod tick))} =
      result S xs ys zs tail := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases h71 : j = 71
    · subst j; simp [result,G,F]
    by_cases h70 : j = 70
    · subst j; simp [result,G,F]
    by_cases h64 : j = 64
    · subst j; simp [result,G,F]
    by_cases h72 : j = 72
    · subst j; simp [result,G,F]
    · simp [result,G,F,h71,h70,h64,h72]
  have he₃' : Exec body (DimensionProductPacket.run (ports 71) 79 80) (mk v₂ G) n₃
      (mk vf (result S xs ys zs tail)) := by simpa [ports,hfinal] using he₃
  have he := Exec.seq he₁' (Exec.seq he₂' he₃')
  refine ⟨vf,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),by dsimp [cost]; omega,he,?_⟩
  intro depth
  exact mn_native_exec_within he 3 run_native depth _ (by dsimp [cost]; omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedCountHeaders
