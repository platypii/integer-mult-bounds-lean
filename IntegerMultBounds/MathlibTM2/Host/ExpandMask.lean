module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Expand retained record selectors into symbol selectors using a retained unary width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def expandedMask (w : ℕ) (f : Fin (A+4) → Bool) (xs : List (Fin (A+4))) : List (Fin (A+4)) :=
  xs.flatMap (fun x => List.replicate w (bitSymbol (f x)))

theorem expandedMask_length (w : ℕ) (f : Fin (A+4) → Bool) (xs : List (Fin (A+4))) :
    (expandedMask w f xs).length = xs.length*w := by
  induction xs with
  | nil => simp [expandedMask]
  | cons x xs ih => simp only [expandedMask,List.flatMap_cons,List.length_append,List.length_replicate,List.length_cons] at *; nlinarith

theorem expandedMask_reverse (w : ℕ) (f : Fin (A+4) → Bool) (xs : List (Fin (A+4))) :
    expandedMask w f xs.reverse = (expandedMask w f xs).reverse := by
  simp [expandedMask,List.reverse_flatMap,Function.comp_def]

def repeatMaskWord (width dst tmp : Fin T) (f : Fin (A+4) → Bool) : Pr P T Q A U :=
  .cond (fun v => f (v.sym.getD blank))
    (umulSym 1 (bitSymbol true) width dst tmp) (umulSym 1 (bitSymbol false) width dst tmp)

theorem repeatMaskWord_exec {width dst tmp : Fin T} (hreg : [width,dst,tmp].Nodup)
    (f : Fin (A+4) → Bool) (x : Fin (A+4)) (v : HS T Q A U) (S : Stacks T A)
    (hsym : v.sym = some x) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (repeatMaskWord width dst tmp f) (mk v S) (4*(S.R width).length+5)
        (mk v' {S with R := Function.update S.R dst (List.replicate (S.R width).length (bitSymbol (f x))++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v',hu,he⟩ := umulSym_exec (body := body) 1 (bitSymbol (f x))
    ‹width ≠ dst› ‹width ≠ tmp› ‹dst ≠ tmp› v S htmp
  simp only [one_mul] at he
  refine ⟨v',hu,?_⟩
  cases hb : f x
  · exact (Exec.cond_false (by simp [hsym,hb]) (by simpa only [hb] using he)).cast (by omega) rfl
  · exact (Exec.cond_true (by simp [hsym,hb]) (by simpa only [hb] using he)).cast (by omega) rfl

def expandMask (mask width saved tmp acc out : Fin T) (f : Fin (A+4) → Bool) : Pr P T Q A U :=
  .seq (eachSym mask saved (repeatMaskWord width acc tmp f))
    (.seq (moveR saved mask id) (moveR acc out id))

theorem expandMask_exec {mask width saved tmp acc out : Fin T}
    (hreg : [mask,width,saved,tmp,acc,out].Nodup) (w : ℕ) (f : Fin (A+4) → Bool)
    (v : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [saved,tmp,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (S.R mask).length*(6*w+10)+6 ∧
      Exec body (expandMask mask width saved tmp acc out f) (mk v S) m
        (mk v' {S with R := Function.update S.R out (expandedMask w f (S.R mask)++S.R out)}) := by
  have hr := hreg
  regs_ne hr
  let xs := S.R mask
  let Ψ : ℕ → Regs T A := fun j => Function.update S.R acc (expandedMask w f (xs.take j).reverse)
  have hspec : SymSpec body (repeatMaskWord width acc tmp f) mask saved xs Ψ (4*w+5) := by
    intro j hj vi Si hsym hSi
    have hiw : (Si.R width).length = w := by
      rw [hSi width ‹mask ≠ width›.symm ‹width ≠ saved›]
      simpa [Ψ,‹width ≠ acc›] using hw
    have hit : Si.R tmp = [] := by
      rw [hSi tmp ‹mask ≠ tmp›.symm ‹saved ≠ tmp›.symm]
      simpa [Ψ,‹tmp ≠ acc›,hfresh tmp (by simp)]
    obtain ⟨vf,hu,he⟩ := repeatMaskWord_exec (body := body)
      (show [width,acc,tmp].Nodup by simp_all [ne_comm]) f xs[j] vi Si hsym hit
    refine ⟨vf,_,4*w+5,hu,le_rfl,he.cast (by rw [hiw]) rfl,?_,?_,?_⟩
    · simp [‹mask ≠ acc›]
    · simp [‹saved ≠ acc›]
    · intro k hkm hks
      by_cases hk : k = acc
      · subst k
        rw [Function.update_self,hSi acc ‹mask ≠ acc›.symm ‹saved ≠ acc›.symm]
        simp only [Ψ,Function.update_self]
        rw [List.take_succ_eq_append_getElem (by omega),List.reverse_append]
        simp [expandedMask,hiw]
      · rw [Function.update_of_ne hk,hSi k hkm hks]
        simp [Ψ,hk]
  obtain ⟨v₁,R₁,m₁,hu₁,hm₁,he₁,hmask,hsaved,hΨ⟩ := eachSym_exec (body := body)
    ‹mask ≠ saved› v S hspec (by
      intro k hkm hks
      by_cases hk : k = acc
      · subst k; simp [Ψ,expandedMask,hfresh acc (by simp)]
      · simp [Ψ,expandedMask,hk])
  let S₁ : Stacks T A := {S with R := R₁}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) saved mask ‹mask ≠ saved›.symm id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := movedR R₁ saved mask id (R₁ saved)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) acc out ‹acc ≠ out› id v₂ S₂
  have hac : R₁ acc = expandedMask w f xs.reverse := by
    simpa [Ψ,xs] using hΨ acc ‹mask ≠ acc›.symm ‹saved ≠ acc›.symm
  have hacc : S₂.R acc = expandedMask w f xs.reverse := by
    simp [S₂,movedR,‹mask ≠ acc›.symm,‹saved ≠ acc›.symm,hac]
  have hsave : R₁ saved = xs.reverse := by simpa [xs,hfresh saved (by simp)] using hsaved
  refine ⟨v₃,m₁+(2*xs.length+2)+(2*(xs.length*w)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · dsimp only [xs] at *
    nlinarith only [hm₁]
  · dsimp only [S₁]
    rw [hsave,List.length_reverse,hacc,expandedMask_length,List.length_reverse]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    change movedR S₂.R acc out id (S₂.R acc) k = _
    rw [hacc]
    by_cases ho : k = out
    · subst k
      simp only [movedR,Function.update_self,List.map_id,expandedMask_reverse,List.reverse_reverse]
      simp [S₂,S₁,movedR,hΨ out ‹mask ≠ out›.symm ‹saved ≠ out›.symm,
        Ψ,xs,‹acc ≠ out›.symm,‹mask ≠ out›.symm,‹saved ≠ out›.symm]
    by_cases ha : k = acc
    · subst k; simp [S₂,S₁,movedR,ho,hfresh acc (by simp)]
    by_cases hm : k = mask
    · subst k; simp [S₂,S₁,movedR,ho,ha,hmask,hsave,xs]
    by_cases hs : k = saved
    · subst k; simp [S₂,S₁,movedR,ho,ha,‹mask ≠ saved›.symm,hfresh saved (by simp)]
    simp [S₂,S₁,movedR,ho,ha,hm,hs,hΨ k hm hs,Ψ]

end IntegerMultBounds.MathlibTM2.Host
