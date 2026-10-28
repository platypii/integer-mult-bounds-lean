module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmitRunPacket
public import IntegerMultBounds.MathlibTM2.Host.StreamCost

/-! A fixed runtime scan consumes binary run counts and physical flag symbols. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def emitRunPackets (off on : Fin (A+4)) : Pr P 117 Q A U :=
  .seq (eachSym 108 23 (emitFlagRunPacket off on))
    (.seq (moveR 23 108 id) (moveR 22 109 id))

theorem emitRunPackets_pushBound (off on : Fin (A+4)) :
    Fast.Main.mnNativePushBound 2 (emitRunPackets (P := P) (Q := Q) (U := U) off on) := by
  simp [emitRunPackets,emitFlagRunPacket,emitRunPacket,emitRun,takePrefix,
    ShortConv.transfer,ShortConv.transferAct,scanR,keepIn,toUnary,eachSym,
    hornerIter,udbl,drainR,popDo,pushN,popPush,moveR,whileR,moveStep,peekR,
    uclear,Fast.Main.mnNativePushBound,Fast.Main.mnActPush]

/-- Certify every intermediate store of the same consuming execution. -/
theorem emitRunPackets_certify (off on : Fin (A+4)) {s t : Store (HΓ (T := 117) A) (HS 117 Q A U)}
    {steps depth B : ℕ} (he : Exec body (emitRunPackets off on) s steps t)
    (hB : Fast.Main.mnSize s+depth+2*steps ≤ B) :
    ExecWithin body (fun d z => Fast.Main.mnSize z+d ≤ B) depth
      (emitRunPackets off on) s steps t :=
  Fast.Main.mn_native_exec_within he 2 (emitRunPackets_pushBound off on) depth B hB

theorem emitRunPackets_exec (W : ℕ) (xs : List (Bool × ℕ))
    (off on : Fin (A+4)) (hfit : ∀ r ∈ xs, r.2 < 2^W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hW : (S.R 115).length = W)
    (hcount : S.R 108 = xs.map (fun r => bitSymbol r.1))
    (hsrc : S.R 109 = xs.flatMap (fun r => binSyms W r.2)++tail)
    (hfresh : ∀ k ∈ [(20 : Fin 117),21,22,23,25,26,27], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 10*(xs.map Prod.snd).sum+(19*W+22)*xs.length+6 ∧
      Exec body (emitRunPackets off on) (mk v S) n
        (mk v' {S with R := (Function.update S.R 109
          (xs.flatMap (fun r => List.replicate r.2 (if r.1 then on else off))++tail))}) := by
  let output := fun r : Bool × ℕ => List.replicate r.2 (if r.1 then on else off)
  let cost := fun j : ℕ => 8*(xs[j]?.getD (false,0)).2+19*W+17
  let Ψ := fun j => Function.update (Function.update S.R 109 ((xs.drop j).flatMap (fun r => binSyms W r.2)++tail))
    22 (((xs.take j).flatMap output).reverse++S.R 22)
  have hp : SymCostSpec body (emitFlagRunPacket off on) 108 23 (S.R 108) Ψ cost := by
    intro j hj v₀ S₀ hsym hS₀
    have hj' : j < xs.length := by simpa [hcount] using hj
    have hsource : S₀.R 109 = binSyms W xs[j].2++((xs.drop (j+1)).flatMap (fun r => binSyms W r.2)++tail) := by
      rw [hS₀ 109 (by decide) (by decide)]
      simp only [Ψ,Function.update_of_ne (by decide : (109 : Fin 117) ≠ 22),Function.update_self]
      rw [List.drop_eq_getElem_cons hj']
      simp only [List.flatMap_cons,List.append_assoc]
    obtain ⟨v₁,steps,hu₁,hn₁,he₁⟩ := emitFlagRunPacket_exec (body := body) W xs[j].2
      (hfit xs[j] (List.getElem_mem hj')) xs[j].1 off on v₀ S₀
      ((xs.drop (j+1)).flatMap (fun r => binSyms W r.2)++tail)
      (by simpa [hcount] using hsym)
      (by rw [hS₀ 115 (by decide) (by decide)]; simpa [Ψ] using hW)
      hsource (by
        intro k hk
        have hk108 : k ≠ (108 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk23 : k ≠ (23 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk109 : k ≠ (109 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        have hk22 : k ≠ (22 : Fin 117) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hS₀ k hk108 hk23]
        simpa [Ψ,hk109,hk22] using hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
    refine ⟨v₁,_,steps,hu₁,by simpa [cost,List.getElem?_eq_getElem hj'] using hn₁,he₁,by simp,by simp,?_⟩
    intro k hk108 hk23
    by_cases hk109 : k = 109
    · subst k; simp [Ψ]
    by_cases hk22 : k = 22
    · subst k
      rw [hS₀ 22 (by decide) (by decide)]
      simp only [Ψ,Function.update_self]
      rw [List.take_succ_eq_append_getElem hj']
      simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.reverse_append,List.append_assoc]
      simp [output]
    simp [Ψ,hk109,hk22,hS₀ k hk108 hk23]
  obtain ⟨v₁,R₁,n₁,hu₁,hn₁,he₁,h108,h68,hR₁⟩ := eachSym_cost_exec (body := body)
    (by decide : (108 : Fin 117) ≠ 23) v S hp (by
      intro k hk108 hk23
      by_cases hk109 : k = 109
      · subst k; simpa [Ψ] using hsrc
      by_cases hk22 : k = 22
      · subst k; simp [Ψ,hfresh 22 (by simp)]
      simp [Ψ,hk109,hk22])
  have hR : R₁ = Function.update (Function.update (Function.update (Function.update S.R 109 tail)
      22 ((xs.flatMap output).reverse)) 108 []) 23 (S.R 108).reverse := by
    funext k
    by_cases hk108 : k = 108
    · subst k; simpa using h108
    by_cases hk23 : k = 23
    · subst k; simpa [hfresh 23 (by simp)] using h68
    rw [hR₁ k hk108 hk23]
    simp only [hcount,List.length_map]
    simp [Ψ,hk108,hk23,hfresh 22 (by simp)]
  subst R₁
  let S₁ : Stacks 117 A := {S with R := Function.update (Function.update (Function.update (Function.update S.R 109 tail)
    22 ((xs.flatMap output).reverse)) 108 []) 23 (S.R 108).reverse}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) 23 108 (by decide) id v₁ S₁
  let S₂ : Stacks 117 A := {S₁ with R := movedR S₁.R 23 108 id (S₁.R 23)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) 22 109 (by decide) id v₂ S₂
  refine ⟨v₃,n₁+((2*(S₁.R 23).length+2)+(2*(S₂.R 22).length+2)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hlen : (xs.flatMap output).length = (xs.map Prod.snd).sum := by
      simp [List.length_flatMap,output]
    have hcountlen : (S.R 108).length = xs.length := by simp [hcount]
    have h68len : (S₁.R 23).length = xs.length := by simp [S₁,hcount]
    have h67len : (S₂.R 22).length = (xs.map Prod.snd).sum := by simp [S₂,S₁,movedR,hlen]
    have hc : symbolCost cost 0 xs.length =
        (xs.map (fun r => 8*r.2+19*W+17)).sum := by
      rw [← List.length_map (f := fun r : Bool × ℕ => 8*r.2+19*W+17)]
      apply symbolCost_eq_sum_list
      intro i hi
      simp only [List.length_map] at hi
      simp [cost,List.getElem?_eq_getElem hi]
    have sum_cost (ys : List (Bool × ℕ)) : (ys.map (fun r => 8*r.2+19*W+17)).sum =
        8*(ys.map Prod.snd).sum+(19*W+17)*ys.length := by
      induction ys with
      | nil => simp
      | cons r ys ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; rw [ih]; ring
    rw [hcountlen,hc,sum_cost] at hn₁
    rw [h68len,h67len]
    nlinarith only [hn₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₂,S₁,movedR,Function.update_apply,List.map_id]
    split_ifs <;> simp_all [output]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
