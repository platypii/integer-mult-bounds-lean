module

public import IntegerMultBounds.MathlibTM2.Routing.DimensionProductPrepare

/-! A self-counted dimension packet generates one unary product header. Both
the factor-count master and clock are generated and retired within the call. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DimensionProductPacket
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

def packet (A V : ℕ) (xs : List ℕ) : List (Fin (A+4)) := binSyms V xs.length++xs.flatMap (binSyms V)

def run (r : Fin 11 → Fin T) (count source : Fin T) : Pr J T Q A U :=
  .seq (readUnaryDimension (r 0) (r 1) (r 2) (r 6) source (r 7) (r 8) (r 9) (r 10))
    (.seq (DimensionProductPrepare.run r count source) (uclear source))

def cost (V : ℕ) (xs : List ℕ) := readUnaryDimensionCost V xs.length+DimensionProductPrepare.cost V xs+2*xs.length+2

theorem run_native (r : Fin 11 → Fin T) (count source : Fin T) :
    mnNativePushBound 3 (run (J := J) (Q := Q) (A := A) (U := U) r count source) := by
  exact ⟨readUnaryDimension_native _ _ _ _ _ _ _ _ _,DimensionProductPrepare.run_native _ _ _,
    by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩

theorem run_exec (r : Fin 11 → Fin T) (hr : Function.Injective r) (count source : Fin T)
    (hc : ∀ j, count ≠ r j) (hs : ∀ j, source ≠ r j) (hsc : source ≠ count)
    (V : ℕ) (xs : List ℕ) (hpos : ∀ x ∈ xs, 0 < x) (hfit : ∀ x ∈ xs, x < 2^V)
    (hcountfit : xs.length < 2^V) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R (r 0)).length = V) (hz : S.R (r 1) = [])
    (hcount : S.R count = []) (hsource : S.R source = []) (hacc : S.R (r 3) = [])
    (hqueue : S.R (r 2) = packet A V xs++tail)
    (hf : ∀ j ∈ [(4 : Fin 11),5,6,7,8,9,10], S.R (r j) = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost V xs ∧
      Exec body (run r count source) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate xs.prod tick))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost V xs)
        depth (run r count source) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate xs.prod tick))})) := by
  have hd : [r 0,r 1,r 2,r 6,source,r 7,r 8,r 9,r 10].Nodup := by
    simp [List.nodup_cons,hr.eq_iff,hs,ne_comm]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readUnaryDimension_exec (body := body)
    (r 0) (r 1) (r 2) (r 6) source (r 7) (r 8) (r 9) (r 10) hd
    V xs.length hcountfit (xs.flatMap (binSyms V)++tail) v S hV hz
    (by simpa [packet,List.append_assoc] using hqueue) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hf _ (by simp)
      · exact hsource
      all_goals exact hf _ (by simp))
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R (r 2)
    (xs.flatMap (binSyms V)++tail)) source (List.replicate xs.length tick))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,_⟩ := DimensionProductPrepare.run_exec (body := body) r hr count source hc hs hsc
    V xs hpos hfit tail v₁ F
    (by simp [F,(hs 0).symm,hr.eq_iff,hV]) (by simp [F,(hs 1).symm,hr.eq_iff,hz])
    (by simp [F]) (by simp [F,hsc.symm,hc,hcount]) (by simp [F,(hs 3).symm,hr.eq_iff,hacc])
    (by simp [F,(hs 2).symm]) (by
      intro j hj
      have hj2 : j ≠ 2 := by intro he; subst j; simp at hj
      simpa [F,(hs j).symm,hr.ne hj2] using hf j hj)
  let G : Stacks T A := {F with R := (Function.update (Function.update F.R (r 2) tail)
    (r 3) (List.replicate xs.prod tick))}
  obtain ⟨vf,hu₃,he₃⟩ := uclear_exec (body := body) source v₂ G
  have hsourceG : (G.R source).length = xs.length := by simp [G,F,hs]
  rw [hsourceG] at he₃
  have hfinal : {G with R := Function.update G.R source []} =
      {S with R := (Function.update (Function.update S.R (r 2) tail) (r 3) (List.replicate xs.prod tick))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j = source
    · subst j; simp [hs,hsource]
    by_cases hj2 : j = r 2
    · subst j; simp [G,F,hj,hr.eq_iff]
    by_cases hj3 : j = r 3
    · subst j; simp [G,hj]
    · simp [G,F,hj,hj2,hj3]
  have he := (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk vf) hfinal)
  refine ⟨vf,n₁+(n₂+(2*xs.length+2)),hu₃.trans (hu₂.trans hu₁),by dsimp [cost]; omega,he,?_⟩
  intro depth
  exact mn_native_exec_within he 3 (run_native _ _ _) depth _ (by dsimp [cost]; omega)

end IntegerMultBounds.MathlibTM2.Routing.DimensionProductPacket
