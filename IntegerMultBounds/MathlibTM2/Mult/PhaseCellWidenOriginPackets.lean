module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenOriginPacket
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! A counted linear pass widens an ordered origin stream and restores its count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def widenOriginPackets : Pr P 117 Q A U :=
  .seq (eachSym 116 23 widenOriginPacket)
    (.seq (moveR 23 116 id) (moveR 22 109 id))

theorem widenOriginPackets_exec (V W : ℕ) (hVW : V ≤ W) (xs : List ℕ)
    (hfit : ∀ x ∈ xs, x < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hW : (S.R 19).length = W)
    (hcount : (S.R 116).length = xs.length)
    (hsrc : S.R 109 = xs.flatMap (binSyms V)++tail)
    (hfresh : ∀ k ∈ [(20 : Fin 117),21,22,23,25,26,27], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(10*W+10*V+23)+6 ∧
      Exec body widenOriginPackets (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (xs.flatMap (binSyms W)++tail)}) := by
  let Ψ := fun j => Function.update (Function.update S.R 109 ((xs.drop j).flatMap (binSyms V)++tail))
    22 (((xs.take j).flatMap (binSyms W)).reverse++S.R 22)
  have hp : SymSpec body widenOriginPacket 116 23 (S.R 116) Ψ (8*W+10*V+18) := by
    intro j hj v₀ S₀ hsym hS₀
    have hj' : j < xs.length := by omega
    have hsource : S₀.R 109 = binSyms V xs[j]++((xs.drop (j+1)).flatMap (binSyms V)++tail) := by
      rw [hS₀ 109 (by decide) (by decide)]
      simp only [Ψ,Function.update_of_ne (by decide : (109 : Fin 117) ≠ 22),Function.update_self]
      rw [List.drop_eq_getElem_cons hj']
      simp only [List.flatMap_cons,List.append_assoc]
    obtain ⟨v₁,hu₁,he₁⟩ := widenOriginPacket_exec (body := body) V W xs[j]
      (hfit xs[j] (List.getElem_mem hj')) hVW v₀ S₀
      ((xs.drop (j+1)).flatMap (binSyms V)++tail)
      (by rw [hS₀ 115 (by decide) (by decide)]; simpa [Ψ] using hV)
      (by rw [hS₀ 19 (by decide) (by decide)]; simpa [Ψ] using hW) hsource (by
        intro k hk
        have hk116 : k ≠ (116 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk23 : k ≠ (23 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk109 : k ≠ (109 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk22 : k ≠ (22 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hS₀ k hk116 hk23]
        simpa [Ψ,hk109,hk22] using hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
    refine ⟨v₁,_,8*W+10*V+18,hu₁,le_rfl,he₁,by simp,by simp,?_⟩
    intro k hk116 hk23
    by_cases hk109 : k = 109
    · subst k; simp [Ψ]
    by_cases hk22 : k = 22
    · subst k
      rw [hS₀ 22 (by decide) (by decide)]
      simp only [Ψ,Function.update_self]
      rw [List.take_succ_eq_append_getElem hj']
      simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.reverse_append,List.append_assoc]
    simp [Ψ,hk109,hk22,hS₀ k hk116 hk23]
  obtain ⟨v₁,R₁,n₁,hu₁,hn₁,he₁,h116,h68,hR₁⟩ := eachSym_exec (body := body)
    (by decide : (116 : Fin 117) ≠ 23) v S hp (by
      intro k hk116 hk23
      by_cases hk109 : k = 109
      · subst k; simpa [Ψ] using hsrc
      by_cases hk22 : k = 22
      · subst k; simp [Ψ,hfresh 22 (by simp)]
      simp [Ψ,hk109,hk22])
  have hR : R₁ = Function.update (Function.update (Function.update (Function.update S.R 109 tail)
      22 ((xs.flatMap (binSyms W)).reverse)) 116 []) 23 (S.R 116).reverse := by
    funext k
    by_cases hk116 : k = 116
    · subst k; simpa using h116
    by_cases hk23 : k = 23
    · subst k; simpa [hfresh 23 (by simp)] using h68
    rw [hR₁ k hk116 hk23,hcount]
    simp [Ψ,hk116,hk23,hfresh 22 (by simp)]
  subst R₁
  let S₁ : Stacks 117 A := {S with R := Function.update (Function.update (Function.update (Function.update S.R 109 tail)
    22 ((xs.flatMap (binSyms W)).reverse)) 116 []) 23 (S.R 116).reverse}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) 23 116 (by decide) id v₁ S₁
  let S₂ : Stacks 117 A := {S₁ with R := movedR S₁.R 23 116 id (S₁.R 23)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) 22 109 (by decide) id v₂ S₂
  refine ⟨v₃,n₁+((2*(S₁.R 23).length+2)+(2*(S₂.R 22).length+2)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hlen : (xs.flatMap (binSyms (A := A) W)).length = xs.length*W := by
      simp [List.length_flatMap]
    have h68len : (S₁.R 23).length = xs.length := by simp [S₁,hcount]
    have h67len : (S₂.R 22).length = xs.length*W := by simp [S₂,S₁,movedR,hlen]
    rw [hcount] at hn₁
    rw [h68len,h67len]
    nlinarith only [hn₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₂,S₁,movedR,Function.update_apply,List.map_id,List.reverse_reverse]
    split_ifs <;> simp_all [hfresh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
