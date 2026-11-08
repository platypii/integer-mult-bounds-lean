module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedOriginHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableRelease

/-! Share the lifecycle from a proved table enumeration to restoring sweep
controls: counted binary output, table release, and forward differences. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def generatedOriginControls (code : TblCode 16) : Pr P 117 Q A U :=
  .seq (countedOriginHost code) (.seq releaseOriginBank preparedNaturalAdvanceControls)

theorem generatedOriginControls_exec {W V span w K : ℕ} (origins : List ℕ)
    (code : TblCode 16) (st : TblSt 16 A)
    (hcode : TblDo A W V code st (fun F =>
      F.acc = (origins.flatMap (fun x => tblPairs A V x 0)).reverse++st.acc) K)
    (hwV : w < 2^V) (hsV : span < 2^V) (hvol : span*w < 2^V)
    (hsorted : origins.Pairwise (· ≤ ·)) (hle : ∀ x ∈ origins, x ≤ span)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ K*tblC W V+origins.length*(8*V+6)+6+(62*W+63)+
        preparedOriginAdvanceCost V span w origins.length ∧
      Exec body (generatedOriginControls code) (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R = fun k => if k.val < 31 then [] else
        if k = 91 then gatherControls A (originAdvances w 0 origins++[0])++S.R 91 else
        if k = 109 then origins.flatMap (binSyms V)++S.R 109 else
        if k = 116 then List.replicate origins.length tick else S.R k := by
  obtain ⟨v₁,S₁,n₁,st₁,hu₁,hn₁,he₁,h109,hcount,hh₁,hb₁,hi₁,ho₁,hl₁,hf₁⟩ :=
    countedOriginListHost_exec origins code st hcode (fun x hx => (hle x hx).trans_lt hsV)
      hVW hA hVpos hbound hacc v S hS h104 h106 h116
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) (hk109 : k ≠ 109) (hk116 : k ≠ 116) :
      S₁.R k = S.R k :=
    hf₁ k hk109 hk116 (fun r he => by
      have hr := originReg_range r
      rw [he] at hr
      omega)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ :=
    releaseOriginBank_width_exec (body := body) W V hVW st₁.val v₁ S₁ hh₁
  let S₂ : Stacks 117 A := {S₁ with R := fun k => if k.val < 31 then [] else S₁.R k}
  have hoff₂ (k : Fin 117) (hk : 31 ≤ k.val) (hk109 : k ≠ 109) (hk116 : k ≠ 116) :
      S₂.R k = S.R k := by
    simpa only [S₂, show ¬k.val < 31 by omega, ite_false] using hoff k hk hk109 hk116
  have hclean : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S₂.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [hoff₂ 88 (by decide) (by decide) (by decide)]; exact hfresh 88 (by simp)
    · rw [hoff₂ 89 (by decide) (by decide) (by decide)]; exact hfresh 89 (by simp)
    · rw [hoff₂ 90 (by decide) (by decide) (by decide)]; exact hfresh 90 (by simp)
    · rw [hoff₂ 106 (by decide) (by decide) (by decide)]; exact h106
  obtain ⟨v₃, F, n₃, hu₃, hn₃, he₃, hi₃, ho₃, hl₃, hF⟩ :=
    preparedOriginAdvanceControls_exec (body := body) V w span origins hwV hsV hvol hsorted hle
      v₂ S₂ (S.R 109)
      (by rw [hoff₂ 115 (by decide) (by decide) (by decide)]; exact hV)
      (by rw [hoff₂ 94 (by decide) (by decide) (by decide)]; exact hw)
      (by simpa only [S₂, show ¬(109 : Fin 117).val < 31 by decide, ite_false] using h109)
      (by simpa only [S₂, show ¬(116 : Fin 117).val < 31 by decide, ite_false] using hcount)
      (fun k hk => by simp only [S₂, show k.val < 31 by omega, ite_true])
      hclean
  refine ⟨v₃, F, n₁+(n₂+n₃), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃), hi₃.trans hi₁, ho₃.trans ho₁, hl₃.trans hl₁, ?_⟩
  funext k
  rw [hF]
  by_cases hk : k.val < 31
  · have hk91 : k ≠ 91 := by intro he; subst k; norm_num at hk
    simp [ hk91, S₂, hk]
  by_cases hk91 : k = 91
  · subst k
    simp [ S₂, hoff 91 (by decide) (by decide) (by decide)]
  by_cases hk109 : k = 109
  · subst k
    simp [ S₂, h109]
  by_cases hk116 : k = 116
  · subst k
    simp [ S₂, hcount]
  simp [ hk91, hk109, hk116, hk, hoff₂ k (by omega) hk109 hk116]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
