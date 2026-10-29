module

public import IntegerMultBounds.MathlibTM2.Host.SpreadRecordStep

/-! Restore a sparse record stream to its local positions using a retained
record mask. The proof follows one structural scan, with no coordinate packets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def spreadRecords (src mask width saved tmp acc out : Fin T)
    (f : Fin (A+4) → Bool) (zero : Fin (A+4)) : Pr P T Q A U :=
  .seq (eachSym mask saved (spreadRecordStep width src acc tmp f zero))
    (.seq (moveR saved mask id) (moveR acc out id))

theorem spreadRecords_exec (src mask width saved tmp acc out : Fin T)
    (hreg : [src,mask,width,saved,tmp,acc,out].Nodup)
    (ms : List (Fin (A+4))) (words : List (List (Fin (A+4)))) (w : ℕ)
    (f : Fin (A+4) → Bool) (zero : Fin (A+4)) (hlen : words.length = ms.length)
    (hwidth : ∀ x ∈ words, x.length = w)
    (hzero : ∀ j (hj : j < ms.length), f ms[j] = false →
      words[j]'(by omega) = List.replicate w zero)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (gatherSymbols words (ms.map f)).flatten++tail)
    (hmask : S.R mask = ms) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [saved,tmp,acc], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ ms.length*(6*w+10)+6 ∧
      Exec body (spreadRecords src mask width saved tmp acc out f zero) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) out
          (words.flatten++S.R out))}) := by
  have hr := hreg
  regs_ne hr
  let remaining (j : ℕ) := (gatherSymbols (words.drop j) ((ms.drop j).map f)).flatten++tail
  let Ψ : ℕ → Regs T A := fun j => (Function.update (Function.update S.R src (remaining j))
    acc (words.take j).flatten.reverse)
  have hspec : SymSpec body (spreadRecordStep width src acc tmp f zero) mask saved ms Ψ (4*w+5) := by
    intro j hj vi Si hsym hSi
    have hjw : j < words.length := by omega
    have hrem : remaining j = (if f ms[j] then words[j] else [])++remaining (j+1) := by
      dsimp only [remaining]
      rw [List.drop_eq_getElem_cons hjw,List.drop_eq_getElem_cons hj]
      cases hb : f ms[j] <;> simp only [List.map_cons,gatherSymbols,hb,
        Bool.false_eq_true,ite_false,ite_true,List.flatten_cons,List.nil_append,List.append_assoc]
    have hsrcSi : Si.R src = (if f ms[j] then words[j] else [])++remaining (j+1) := by
      rw [hSi src ‹src ≠ mask› ‹src ≠ saved›]
      simpa [Ψ,‹src ≠ acc›] using hrem
    have hwSi : (Si.R width).length = w := by
      rw [hSi width ‹mask ≠ width›.symm ‹width ≠ saved›]
      simpa [Ψ,‹src ≠ width›.symm,‹width ≠ acc›] using hw
    have htmpSi : Si.R tmp = [] := by
      rw [hSi tmp ‹mask ≠ tmp›.symm ‹saved ≠ tmp›.symm]
      simp [Ψ,‹src ≠ tmp›.symm,‹tmp ≠ acc›,hfresh tmp (by simp)]
    obtain ⟨vf,hu,he⟩ := spreadRecordStep_exec width src acc tmp (by regs_nodup) f zero ms[j]
      w words[j] (remaining (j+1)) (hwidth _ (List.getElem_mem hjw)) (hzero j hj)
      vi Si hsym hwSi hsrcSi htmpSi
    refine ⟨vf,_,4*w+5,hu,le_rfl,he,?_,?_,?_⟩
    · simp [‹src ≠ mask›.symm,‹mask ≠ acc›]
    · simp [‹src ≠ saved›.symm,‹saved ≠ acc›]
    · intro k hkm hks
      by_cases hka : k = acc
      · subst k
        rw [Function.update_self,hSi acc ‹mask ≠ acc›.symm ‹saved ≠ acc›.symm]
        simp only [Ψ,Function.update_self]
        rw [List.take_succ_eq_append_getElem hjw,List.flatten_append,List.reverse_append]
        simp
      by_cases hksrc : k = src
      · subst k; simp [Ψ,‹src ≠ acc›]
      · simp only [Function.update_of_ne hka,Function.update_of_ne hksrc]
        rw [hSi k hkm hks]
        simp [Ψ,hka,hksrc]
  have hstart : ∀ k, k ≠ mask → k ≠ saved → S.R k = Ψ 0 k := by
    intro k _ _
    by_cases hk : k = src
    · subst k; simpa [Ψ,remaining,‹src ≠ acc›] using hsrc
    by_cases ha : k = acc
    · subst k; simp [Ψ,hfresh acc (by simp)]
    · simp [Ψ,hk,ha]
  obtain ⟨v₁,R₁,n₁,hu₁,hn₁,he₁,hm₁,hs₁,hframe⟩ := eachSym_exec body
    ‹mask ≠ saved› v S (by simpa only [hmask] using hspec) hstart
  let S₁ : Stacks T A := {S with R := R₁}
  have hacc : R₁ acc = words.flatten.reverse := by
    simpa [Ψ,hmask,← hlen] using hframe acc ‹mask ≠ acc›.symm ‹saved ≠ acc›.symm
  have hsource : R₁ src = tail := by
    simpa [Ψ,remaining,hmask,List.drop_eq_nil_of_le (show words.length ≤ ms.length by omega),‹src ≠ acc›,gatherSymbols] using
      hframe src ‹src ≠ mask› ‹src ≠ saved›
  have hsaved : R₁ saved = ms.reverse := by simpa [hmask,hfresh saved (by simp)] using hs₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body saved mask ‹mask ≠ saved›.symm id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := movedR R₁ saved mask id (R₁ saved)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body acc out ‹acc ≠ out› id v₂ S₂
  have hsavedLen : (S₁.R saved).length = ms.length := by simp [S₁,hsaved]
  have hacc₂ : S₂.R acc = words.flatten.reverse := by
    simp [S₂,movedR,‹mask ≠ acc›.symm,‹saved ≠ acc›.symm,hacc]
  have hwordLen : words.flatten.length = ms.length*w := by
    calc
      words.flatten.length = (words.map List.length).sum := List.length_flatten
      _ = (words.map (fun _ => w)).sum := by
        congr 1
        exact List.map_congr_left hwidth
      _ = ms.length*w := by simp [hlen]
  refine ⟨v₃,n₁+(2*ms.length+2)+(2*(ms.length*w)+2),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hmask] at hn₁
    nlinarith only [hn₁]
  · rw [hsavedLen,hacc₂,List.length_reverse,hwordLen]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hko : k = out
    · subst k
      have ho := hframe out ‹mask ≠ out›.symm ‹saved ≠ out›.symm
      simp [Ψ,‹src ≠ out›.symm,‹acc ≠ out›.symm] at ho
      simp [S₂,movedR,ho,hacc,‹mask ≠ acc›.symm,‹saved ≠ acc›.symm,
        ‹mask ≠ out›.symm,‹saved ≠ out›.symm]
    by_cases hka : k = acc
    · subst k; simp [S₂,movedR,hko,hfresh acc (by simp),‹src ≠ acc›.symm]
    by_cases hkm : k = mask
    · subst k; simp [S₂,movedR,hko,hka,hsaved,hm₁,hmask,‹src ≠ mask›.symm]
    by_cases hks : k = saved
    · subst k; simp [S₂,movedR,hko,hka,hfresh saved (by simp),‹src ≠ saved›.symm,‹mask ≠ saved›.symm]
    by_cases hksrc : k = src
    · subst k; simp [S₂,movedR,hko,hka,hkm,hks,hsource]
    · have hk := hframe k hkm hks
      simp [Ψ,hksrc,hka] at hk
      simp [S₂,movedR,hko,hka,hkm,hks,hksrc,hk]

end IntegerMultBounds.MathlibTM2.Host
