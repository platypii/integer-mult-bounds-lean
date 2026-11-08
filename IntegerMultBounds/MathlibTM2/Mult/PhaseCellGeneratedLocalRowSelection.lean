module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowControls

/-! Generate local C-selection controls and execute the actual restoring sweep.
Controls remain available for the other replicas of the same factor page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 117 Q A U}

def generatedLocalRowSelection : Pr P 117 Q A U :=
  .seq generatedLocalRowControls (naturalGather 108 91 92 93 95 110 96 97 98 99 100 101 102 103 94)

theorem generatedLocalRowSelection_exec {W V t a origin span w n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (ha : st.val 2 = a)
    (ho : st.val 3 = origin) (hz : st.val 12 = 0) (hn : st.val 15 = n)
    (hnpos : 0 < n) (hcount : n < 2^W) (hsource : a+n ≤ s) (htarget : origin+span ≤ t)
    (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (F : ZMod t → GaussianInt) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = [])
    (hsrc : S.R 110 = cstream A w (packedInterval origin span F))
    (hrow : (S.R 103).length = 1) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], S.R k = []) :
    ∃ v' B m, v'.user = v.user ∧
      m ≤ localRowControlsCost W V span w n+n*(14*w+25)+12*(span*w)+6*w+38 ∧
      Exec body generatedLocalRowSelection (mk v S) m (mk v' B) ∧
      B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
      B.R 108 = cstream A w (packedInterval a n (fun j => F (rowIndex s t j)))++S.R 108 ∧
      ∀ k, k ≠ 108 → B.R k = if k.val < 31 then [] else
        if k = 91 then localRowControls A s t a n origin w else
        if k = 109 then (localRowOrigins s t a n origin 1).flatMap (binSyms V)++S.R 109 else
        if k = 116 then List.replicate n tick else S.R k := by
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hi₁,ho₁,hl₁,hR⟩ :=
    generatedLocalRowControls_exec (body := body) st hs ht ha ho hz hn (NeZero.pos s) hnpos hcount
      hwide hwindow hwV hspan hvol hVW hA hVpos hbound hacc v S hS hV hw h104 h106 h116 hfresh
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) (hk91 : k ≠ 91) (hk109 : k ≠ 109) (hk116 : k ≠ 116) :
      S₁.R k = S.R k := by rw [hR]; simp [show ¬k.val < 31 by omega,hk91,hk109,hk116]
  have hc : S₁.R 91 = localRowControls A s t a n origin w := by simp [hR,hcontrol]
  have hclean' : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], S₁.R k = [] := by
    intro k hk
    have hne : 31 ≤ k.val ∧ k ≠ 91 ∧ k ≠ 109 ∧ k ≠ 116 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hoff k hne.1 hne.2.1 hne.2.2.1 hne.2.2.2]
    exact hclean k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := localRowSelection_exec (body := body)
    108 91 92 93 95 110 96 97 98 99 100 101 102 103 94 (by decide) w a n origin span F
    hnpos hsource htarget hwindow v₁ S₁ hc
    (by rw [hoff 110 (by decide) (by decide) (by decide) (by decide)]; exact hsrc)
    (by rw [hoff 103 (by decide) (by decide) (by decide) (by decide)]; exact hrow)
    (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact hw) hclean'
  let B : Stacks 117 A := {S₁ with R := (Function.update S₁.R 108
    (cstream A w (packedInterval a n (fun j => F (rowIndex s t j)))++S₁.R 108))}
  refine ⟨v₂,B,m₁+m₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hi₁,ho₁,hl₁,?_,?_⟩
  · simp only [B,Function.update_self]
    rw [hoff 108 (by decide) (by decide) (by decide) (by decide)]
  · intro k hk
    simp only [B,Function.update_of_ne hk]
    rw [hR]
    simp only [hcontrol,List.append_nil]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
