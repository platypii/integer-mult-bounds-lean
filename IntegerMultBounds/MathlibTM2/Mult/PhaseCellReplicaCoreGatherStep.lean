module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCoreGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeCopyPrefix

/-! One replica iteration advances the ambient source once, gathers its whole
movement class, and retires the local row. The reversed source archive supports
one final linear restoration after the replica loop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaCoreGatherStep (e : Fin 168 → Fin T) (count source archive saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takeCopyPrefix count source (e 110) archive saved tmp)
    (.seq (placedCoreGather e) (uclear (e 110)))

def replicaCoreGatherStepCost (V s width radius L w : ℕ) : ℕ :=
  16*(s*w)+16+restoredCoreGatherCost V s width radius L w

theorem replicaCoreGatherStep_exec (e : Fin 168 → Fin T) (he : Function.Injective e) (count source archive saved tmp : Fin T)
    (hreg : [count,source,e 110,archive,saved,tmp].Nodup)
    (hsourceOff : ∀ i, source ≠ e i) (harchiveOff : ∀ i, archive ≠ e i)
    (tail : List (Fin (A+4))) {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (C : ZMod s → GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (h163 : (S.R (e 163)).length = V) (h115 : S.R (e 115) = []) (h103 : S.R (e 103) = []) (h105 : S.R (e 105) = [])
    (hs : S.R (e 145) = binSyms V s) (hw : S.R (e 150) = binSyms V width)
    (hr : S.R (e 152) = binSyms V radius) (hL : S.R (e 165) = binSyms V L) (hz : S.R (e 154) = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hsource : S.R source = cstream A w (chirpLine s C)++tail)
    (hlocal : S.R (e 110) = [])
    (hcount : (S.R count).length = s*w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hword : (S.R (e 94)).length = w) (hcontrol : S.R (e 91) = []) (horigin : S.R (e 109) = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (e k) = [])  :
    ∃ v' n, v'.user = v.user ∧ n ≤ replicaCoreGatherStepCost V s width radius L w ∧
      Exec body (replicaCoreGatherStep e count source archive saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R source tail)
          archive ((cstream A w (chirpLine s C)).reverse++S.R archive)) (e 108)
          (cstream A w (coreGatherPayload width radius L [C])++S.R (e 108)))}) := by
  let E := cstream A w (chirpLine s C)
  have hlen : E.length = s*w := by simp [E]
  obtain ⟨v₁,hu₁,he₁⟩ := takeCopyPrefix_exec count source (e 110) archive saved tmp hreg E tail v S
    (hcount.trans hlen.symm) hsource hsaved htmp
  let H : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R source tail)
    (e 110) E) archive (E.reverse++S.R archive))}
  have he₁' : Exec body (takeCopyPrefix count source (e 110) archive saved tmp)
      (Host.mk v S) (14*E.length+14) (Host.mk v₁ H) := by
    simpa only [hlocal,List.append_nil] using he₁
  have hoff (k : Fin 168) (hk : k ≠ 110) : H.R (e k) = S.R (e k) := by
    have hke : e k ≠ e 110 := fun h => hk (he h)
    simp [H,(hsourceOff k).symm,(harchiveOff k).symm,hke]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedCoreGather_exec_within (body := body) e he
    hwidth hwide hLfit hwV hvol hA hVpos hgroup C v₁ H
    (by simpa only [hoff 163 (by decide)] using h163)
    (by simpa only [hoff 115 (by decide)] using h115)
    (by simpa only [hoff 103 (by decide)] using h103)
    (by simpa only [hoff 105 (by decide)] using h105)
    (by simpa only [hoff 145 (by decide)] using hs)
    (by simpa only [hoff 150 (by decide)] using hw)
    (by simpa only [hoff 152 (by decide)] using hr)
    (by simpa only [hoff 165 (by decide)] using hL)
    (by simpa only [hoff 154 (by decide)] using hz)
    (by intro k hk; rw [hoff k (by intro h; subst k; norm_num at hk)]; exact hblank k hk)
    (by simpa only [hoff 104 (by decide)] using h104)
    (by simpa only [hoff 106 (by decide)] using h106)
    (by simpa only [hoff 116 (by decide)] using h116)
    (by simp [H,(harchiveOff 110).symm,E])
    (by simpa only [hoff 94 (by decide)] using hword)
    (by simpa only [hoff 91 (by decide)] using hcontrol)
    (by simpa only [hoff 109 (by decide)] using horigin)
    (by intro k hk; rw [hoff k (by intro h; subst k; simp at hk)]; exact hclean k hk)
    (by intro k hk; rw [hoff k (by intro h; subst k; simp at hk)]; exact hfresh k hk) 0
  let F : Stacks T A := {H with R := (Function.update H.R (e 108)
    (cstream A w (coreGatherPayload width radius L [C])++H.R (e 108)))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body (e 110) v₂ F
  have h108110 : e 108 ≠ e 110 := fun h => (by decide : (108 : Fin 168) ≠ 110) (he h)
  have hlocalLength : (F.R (e 110)).length = s*w := by
    simp [F,H,h108110.symm,(harchiveOff 110).symm,hlen]
  refine ⟨v₃,(14*E.length+14)+(n₂+(2*(F.R (e 110)).length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂.toExec he₃)).cast rfl ?_⟩
  · rw [hlen,hlocalLength]
    dsimp only [replicaCoreGatherStepCost]
    omega
  · apply congrArg (Host.mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hkLocal : k = e 110
    · subst k
      simp [H,F,hlocal,h108110.symm,(hsourceOff 110).symm,(harchiveOff 110).symm]
    by_cases hkResult : k = e 108
    · subst k
      simp [H,F,h108110,(hsourceOff 108).symm,(harchiveOff 108).symm]
    by_cases hkSource : k = source
    · subst k
      simp [H,F,hkLocal,hkResult,
        (by have hr := hreg; regs_ne hr; exact ‹source ≠ archive› : source ≠ archive)]
    by_cases hkArchive : k = archive
    · subst k
      simp [H,F,hkLocal,hkResult,E]
    simp [H,F,hkLocal,hkResult,hkSource,hkArchive]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
