module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalOriginPackets
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! Publish computed metadata and a retained binary count, then release the table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def tableCountedPacketHost (count : Fin 16) (code : TblCode 16) : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg code)
    (.seq (tblUnaryCopies originReg [(count,116)])
      (.seq (moveR (originReg .acc) 109 (fun sym => bitSymbol (pairRe sym))) releaseOriginBank))

theorem tableCountedPacketHost_list_exec {V K N : ℕ} (count : Fin 16) (xs : List ℕ) (code : TblCode 16) (st : TblSt 16 A)
    (hc : TblDo A V V code st (fun st' => st'.acc = (xs.flatMap (fun x => tblPairs A V x 0)).reverse ∧ st'.val count = N) K)
    (hbound : ∀ r, st.val r < 2^V) (hx : ∀ x ∈ xs, x < 2^V) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ K*tblC V V+(2*xs.length+73)*V+6*N+72 ∧
      Exec body (tableCountedPacketHost count code) (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
          xs.flatMap (binSyms (A := A) V)++S.R 109 else if r = 116 then
          List.replicate N tick++S.R 116 else S.R r)}) := by
  obtain ⟨st',⟨⟨hp,hn⟩,hb⟩,hrun⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl
    (hc.bounded hbound) hbound
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ := hrun v S hS
  have hoff (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun y he => by have hy := originReg_range y; have hv := congrArg Fin.val he; omega)
  have hout : ∀ p ∈ ([(count,116)] : List (Fin 16 × Fin 117)), ∀ r, originReg r ≠ p.2 := by
    intro p hp r he
    have hp' : p = (count,116) := List.mem_singleton.mp hp
    subst p
    have hr := originReg_range r
    rw [he] at hr
    norm_num at hr
  obtain ⟨vc,mc,huc,hmc,hec⟩ := tblUnaryCopies_exec (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) st' hb [(count,116)] hout v₁ S₁ hh₁
  let Sc : Stacks 117 A := {S₁ with R := Function.update S₁.R 116 (List.replicate N tick++S₁.R 116)}
  have hec' : Exec body (tblUnaryCopies originReg [(count,116)]) (mk v₁ S₁) mc (mk vc Sc) := by
    simpa only [Sc,unaryCopiesR,hn] using hec
  have hmc' : mc ≤ 6*N+11*V+7 := by
    simpa [unaryCopiesCost,hn] using hmc
  have hbank (r) : Sc.R (originReg r) = S₁.R (originReg r) := by
    have hne : originReg r ≠ 116 := hout (count,116) (by simp) r
    simp only [Sc,Function.update_of_ne hne]
  have hhc : tblHolds originReg Sc (tblRho V (List.replicate V tick) (List.replicate V tick) st') :=
    fun r => (hbank r).trans (hh₁ r)
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body (originReg .acc) 109 (by decide)
    (fun sym => bitSymbol (pairRe sym)) vc Sc
  let S₂ : Stacks 117 A := {Sc with R := movedR Sc.R (originReg .acc) 109 (fun sym => bitSymbol (pairRe sym)) (Sc.R (originReg .acc))}
  have hacc : Sc.R (originReg .acc) = (xs.flatMap (fun x => tblPairs A V x 0)).reverse := by simpa [tblRho,hp] using hhc .acc
  have hlen : (Sc.R (originReg .acc)).length = xs.length*V := by
    simp [hacc,List.length_flatMap,tblPairs,Nat.mul_comm]
  have hbits : (xs.flatMap (fun x => tblPairs A V x 0)).map (fun sym => bitSymbol (pairRe sym)) =
      xs.flatMap (binSyms (A := A) V) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro x hmem
    exact tblPairs_real_bits hA (hx x hmem)
  have hpacket : S₂.R 109 = xs.flatMap (binSyms (A := A) V)++S.R 109 := by
    change ((Sc.R (originReg .acc)).map (fun sym => bitSymbol (pairRe sym))).reverse++Sc.R 109 = _
    rw [hacc]
    simp [List.map_reverse,hbits,Sc,hoff 109 (by decide)]
  have hh₂ : tblHolds originReg S₂ (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val,[]⟩) := by
    intro r
    have hne : originReg r ≠ 109 := by have hy := originReg_range r; intro he; rw [he] at hy; omega
    by_cases hr : r = .acc
    · subst r; simp [S₂,movedR,tblRho,originReg]
    · have hneq : originReg r ≠ originReg .acc := fun he => hr (originReg_injective he)
      have hval : S₂.R (originReg r) = Sc.R (originReg r) := by
        simp only [S₂,movedR,Function.update_apply,ite_eq_right hne,ite_eq_right hneq]
      rw [hval]
      have hh := hhc r
      cases r <;> first | exact (hr rfl).elim | simpa [tblRho] using hh
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseOriginBank_exec (body := body) V st'.val v₂ S₂ hh₂
  refine ⟨v₃,m₁+(mc+((2*(xs.length*V)+2)+m₃)),hu₃.trans (hu₂.trans (huc.trans hu₁)),by nlinarith only [hm₁,hmc',hm₃],
    (Exec.seq he₁ (Exec.seq hec' (Exec.seq (he₂.cast (by rw [hlen]) rfl) he₃))).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
  funext r
  by_cases hr : r.val < 31
  · simp [hr]
  · have hr' : 31 ≤ r.val := by omega
    by_cases h109 : r = 109
    · subst r; simpa using hpacket
    · have hacc' : r ≠ originReg .acc := by intro he; subst r; norm_num [originReg] at hr'
      by_cases h116 : r = 116
      · subst r
        simp [S₂,movedR,Sc,originReg,hoff 116 (by decide)]
      · simp [hr,S₂,movedR,Sc,h109,h116,hacc',hoff r hr']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
