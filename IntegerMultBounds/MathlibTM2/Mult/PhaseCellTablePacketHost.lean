module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalOriginPackets
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Publish one computed natural address as binary data and release its table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def tablePacketHost (code : TblCode 16) : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg code)
    (.seq (moveR (originReg .acc) 109 (fun sym => bitSymbol (pairRe sym))) releaseOriginBank)

theorem tablePacketHost_list_exec {V K : ℕ} (xs : List ℕ) (code : TblCode 16) (st : TblSt 16 A)
    (hc : TblDo A V V code st (fun st' => st'.acc = (xs.flatMap (fun x => tblPairs A V x 0)).reverse) K)
    (hbound : ∀ r, st.val r < 2^V) (hx : ∀ x ∈ xs, x < 2^V) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ K*tblC V V+(2*xs.length+62)*V+65 ∧
      Exec body (tablePacketHost code) (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
          xs.flatMap (binSyms (A := A) V)++S.R 109 else S.R r)}) := by
  obtain ⟨st',⟨hp,_⟩,hrun⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl
    (hc.bounded hbound) hbound
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ := hrun v S hS
  have hoff (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun y he => by have hy := originReg_range y; have hv := congrArg Fin.val he; omega)
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body (originReg .acc) 109 (by decide)
    (fun sym => bitSymbol (pairRe sym)) v₁ S₁
  let S₂ : Stacks 117 A := {S₁ with R := movedR S₁.R (originReg .acc) 109 (fun sym => bitSymbol (pairRe sym)) (S₁.R (originReg .acc))}
  have hacc : S₁.R (originReg .acc) = (xs.flatMap (fun x => tblPairs A V x 0)).reverse := by simpa [tblRho,hp] using hh₁ .acc
  have hlen : (S₁.R (originReg .acc)).length = xs.length*V := by
    simp [hacc,List.length_flatMap,tblPairs,Nat.mul_comm]
  have hbits : (xs.flatMap (fun x => tblPairs A V x 0)).map (fun sym => bitSymbol (pairRe sym)) =
      xs.flatMap (binSyms (A := A) V) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro x hmem
    exact tblPairs_real_bits hA (hx x hmem)
  have hpacket : S₂.R 109 = xs.flatMap (binSyms (A := A) V)++S.R 109 := by
    simp [S₂,movedR,hacc,hoff 109 (by decide),List.map_reverse,hbits]
  have hh₂ : tblHolds originReg S₂ (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val,[]⟩) := by
    intro r
    have hne : originReg r ≠ 109 := by have hy := originReg_range r; intro he; rw [he] at hy; omega
    by_cases hr : r = .acc
    · subst r; simp [S₂,movedR,tblRho,originReg]
    · have hneq : originReg r ≠ originReg .acc := fun he => hr (originReg_injective he)
      have hval : S₂.R (originReg r) = S₁.R (originReg r) := by
        simp only [S₂,movedR,Function.update_apply,if_neg hne,if_neg hneq]
      rw [hval]
      have hh := hh₁ r
      cases r <;> first | exact (hr rfl).elim | simpa [tblRho] using hh
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseOriginBank_exec (body := body) V st'.val v₂ S₂ hh₂
  refine ⟨v₃,m₁+((2*(xs.length*V)+2)+m₃),hu₃.trans (hu₂.trans hu₁),by nlinarith only [hm₁,hm₃],
    (Exec.seq he₁ (Exec.seq (he₂.cast (by rw [hlen]) rfl) he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
  funext r
  by_cases hr : r.val < 31
  · simp [hr]
  · have hr' : 31 ≤ r.val := by omega
    by_cases h109 : r = 109
    · subst r; simpa using hpacket
    · have hacc' : r ≠ originReg .acc := by intro he; subst r; norm_num [originReg] at hr'
      simp [hr,S₂,movedR,h109,hacc',hoff r hr']

theorem tablePacketHost_exec {V K x : ℕ} (code : TblCode 16) (st : TblSt 16 A)
    (hc : TblDo A V V code st (fun st' => st'.acc = (tblPairs A V x 0).reverse) K)
    (hbound : ∀ r, st.val r < 2^V) (hx : x < 2^V) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ K*tblC V V+64*V+65 ∧
      Exec body (tablePacketHost code) (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
          binSyms V x++S.R 109 else S.R r)}) := by
  simpa using tablePacketHost_list_exec (body := body) [x] code st (by simpa using hc) hbound
    (by intro y hy; simpa using (List.mem_singleton.mp hy ▸ hx)) hA v S hS

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
