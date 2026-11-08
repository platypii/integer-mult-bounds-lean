module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRoundedKey
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! Publish using the already computed output precision, with no repeated scalar setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def publishRoundedScalar (rg : TblR 25 → Fin T)
    (precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T) : Pr P T Q A U :=
  .seq (tblUnaryCopies rg [(0,precision)])
    (.seq (.act (.push (.rt replicas) (fun _ => tick) .done))
      (.seq (publishRoundedKey precision wide width replicas rows rowWidth count src work saved tmp extra)
        (.seq (uclear replicas) (uclear precision))))

def publishRoundedScalarCost (B p W n : ℕ) : ℕ :=
  8*p+11*B+14+publishRoundedKeyCost p W 1 n

theorem publishRoundedScalar_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    {precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T}
    (hreg : [precision,wide,width,replicas,rows,rowWidth,count,src,work,saved,tmp,extra].Nodup)
    (hprecisionOff : ∀ r, rg r ≠ precision)
    (B p W n : ℕ) (hW : 2*p+13 ≤ W)
    (wl : List (Fin (A+4))) (st : TblSt 25 A) (hp : st.val 0 = p)
    (hfit : ∀ i, st.val i < 2^B)
    (xs : List GaussianInt) (hlen : xs.length = n) (hfits : ∀ x ∈ xs, TopFitsZ (2*p+13) x)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho B wl [] st))
    (hwide : (S.R wide).length = W) (hrows : (S.R rows).length = n)
    (hsrc : S.R src = cstream A (2*p+13) xs++tail)
    (hblank : ∀ k ∈ [precision,replicas,width,rowWidth,count,work,saved,tmp,extra], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publishRoundedScalarCost B p W n ∧
      Exec body (publishRoundedScalar rg precision wide width replicas rows rowWidth count src work saved tmp extra)
        (mk v S) m (mk v' {S with R := Function.update S.R src (cstream A W xs++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := tblUnaryCopies_exec (body := body) hrg wl [] st hfit
    [(0,precision)] (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hprecisionOff) v S hS
  let S₁ : Stacks T A := {S with R := Function.update S.R precision (List.replicate p tick)}
  have he₁' : Exec body (tblUnaryCopies rg [(0,precision)]) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [S₁,unaryCopiesR,hp,hblank precision (by simp),List.append_nil] using he₁
  have hm₁' : m₁ ≤ 6*p+11*B+7 := by
    simpa [unaryCopiesCost,hp] using hm₁
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R replicas [tick]}
  have he₂ : Exec body (.act (.push (.rt replicas) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,Action.run,update_rt,hblank replicas (by simp),‹precision ≠ replicas›.symm] using
      Exec.act (body := body) (.push (.rt replicas) (fun _ => tick) .done) (mk v₁ S₁)
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := publishRoundedKey_exec (body := body) hreg p W 1 n hW xs
    (by simpa using hlen) hfits tail v₁ S₂
    (by simp [S₂,S₁,‹precision ≠ replicas›])
    (by simpa [S₂,S₁,‹wide ≠ replicas›,‹precision ≠ wide›.symm] using hwide)
    (by simp [S₂])
    (by simpa [S₂,S₁,‹replicas ≠ rows›.symm,‹precision ≠ rows›.symm] using hrows)
    (by simpa [S₂,S₁,‹replicas ≠ src›.symm,‹precision ≠ src›.symm] using hsrc)
    (by intro k hk
        have hpne : k ≠ precision := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with hk | hk | hk | hk | hk | hk | hk <;>
            subst k <;> first | assumption | exact Ne.symm (by assumption)
        have hrne : k ≠ replicas := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with hk | hk | hk | hk | hk | hk | hk <;>
            subst k <;> first | assumption | exact Ne.symm (by assumption)
        have hb : S.R k = [] := hblank k (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        simpa [S₂,S₁,hpne,hrne] using hb)
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R src (cstream A W xs++tail)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body replicas v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R replicas []}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body precision v₄ S₄
  refine ⟨v₅,m₁+(1+(m₃+(4+(2*p+2)))),hu₅.trans (hu₄.trans (hu₃.trans hu₁)),
    by dsimp [publishRoundedScalarCost]; omega,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · simp [S₄,S₃,S₂,S₁, *]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hp : k = precision <;> by_cases hr : k = replicas <;>
      simp [S₄,S₃,S₂,S₁,Function.update_apply,hblank precision (by simp),hblank replicas (by simp), *, Ne.symm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
