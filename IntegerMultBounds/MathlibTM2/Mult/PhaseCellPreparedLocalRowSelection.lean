module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowHeaderLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedLocalRowSelection

/-! Local nearest-row selection from ordinary retained scalar headers and an
owned target window. No table, origin queue or sweep controller is supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 117 Q A U}

def preparedLocalRowSelection : Pr P 117 Q A U := .seq loadLocalRowHeaders generatedLocalRowSelection

theorem preparedLocalRowSelection_exec_of_payload {W V t a origin span w n : ℕ}
    (hn : 0 < n)
    (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (E payload : List (Fin (A+4))) (hlen : E.length = span*w)
    (hselected : (localRowOrigins s t a n origin w).flatMap (fun p => (E.drop p).take w) = payload)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hW : (S.R 114).length = W) (hV : (S.R 115).length = V)
    (hs : S.R 32 = binSyms W s) (ht : S.R 33 = binSyms W t)
    (ha : S.R 34 = binSyms W a) (ho : S.R 35 = binSyms W origin)
    (hc : S.R 36 = binSyms W n) (hz : S.R 37 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hw : (S.R 94).length = w) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = [])
    (hsrc : S.R 110 = E)
    (hrow : (S.R 103).length = 1) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], S.R k = []) :
    ∃ v' B m, v'.user = v.user ∧
      m ≤ (110*W+4*V+137)+(localRowControlsCost W V span w n+n*(14*w+25)+12*(span*w)+6*w+38) ∧
      Exec body preparedLocalRowSelection (mk v S) m (mk v' B) ∧
      B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
      B.R 108 = payload++S.R 108 ∧
      B.R 91 = localRowControls A s t a n origin w ∧
      B.R 109 = (localRowOrigins s t a n origin 1).flatMap (binSyms V)++S.R 109 ∧
      B.R 116 = List.replicate n tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → B.R k = S.R k := by
  have hleft := (hwindow 0 hn).1
  simp only [Nat.add_zero] at hleft
  obtain ⟨v₁,hu₁,he₁,htable,hframe⟩ := loadLocalRowHeaders_exec (body := body) W V s t a origin n hn hleft hwide
    v S hW hV hs ht ha ho hc hz hblank
  let B₁ : Stacks 117 A := {S with R := (chirpBankLoadR originReg localRowSource W V
    (localRowValue s t a origin n) S.R)}
  change ∀ k, 31 ≤ k.val → B₁.R k = S.R k at hframe
  let st := localRowTable A s t a origin n
  have hbound : ∀ i, st.val i < 2^W := by
    intro i
    have hh := localRowHeader_fit s t a origin n W hn hleft hwide i
    apply hh.trans_le
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    simp [localRowBits]; split_ifs <;> omega
  have hcount : n < 2^W := by omega
  have hclean' : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], B₁.R k = [] := by
    intro k hk
    have hh : 31 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hframe k hh]
    exact hclean k hk
  have hfresh' : ∀ k ∈ [(88 : Fin 117),89,90], B₁.R k = [] := by
    intro k hk
    have hh : 31 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide
    rw [hframe k hh]
    exact hfresh k hk
  obtain ⟨v₂,B,m,hu₂,hm,he₂,hi,hou,hl,h108,hR⟩ := generatedLocalRowSelection_exec_of_payload (body := body) st
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    hn hcount hwide hwindow hwV hspan hvol hVW hA hVpos hbound rfl E payload hlen hselected v₁ B₁ htable
    (by rw [hframe 115 (by decide)]; exact hV) (by rw [hframe 94 (by decide)]; exact hw)
    (by rw [hframe 104 (by decide)]; exact h104) (by rw [hframe 106 (by decide)]; exact h106)
    (by rw [hframe 116 (by decide)]; exact h116) hfresh'
    (by rw [hframe 110 (by decide)]; exact hsrc) (by rw [hframe 103 (by decide)]; exact hrow)
    (by rw [hframe 91 (by decide)]; exact hcontrol) hclean'
  refine ⟨v₂,B,(110*W+4*V+137)+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,Exec.seq he₁ he₂,
    hi,hou,hl,?_,?_,?_,?_,?_⟩
  · simpa only [hframe 108 (by decide)] using h108
  · simpa using hR 91 (by decide)
  · simpa only [show ¬(109 : Fin 117).val < 31 by decide,show (109 : Fin 117) ≠ 91 by decide,
      ite_false,ite_true,hframe 109 (by decide)] using hR 109 (by decide)
  · simpa using hR 116 (by decide)
  · intro k hk108 hk91 hk109 hk116
    rw [hR k hk108]
    by_cases hk : k.val < 31
    · simpa only [hk,ite_true] using (hblank k hk).symm
    · simp only [hk,hk91,hk109,hk116,ite_false]
      exact hframe k (by omega)

theorem preparedLocalRowSelection_exec {W V t a origin span w n : ℕ}
    (hn : 0 < n) (hsource : a+n ≤ s) (htarget : origin+span ≤ t)
    (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (F : ZMod t → GaussianInt) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hW : (S.R 114).length = W) (hV : (S.R 115).length = V)
    (hs : S.R 32 = binSyms W s) (ht : S.R 33 = binSyms W t)
    (ha : S.R 34 = binSyms W a) (ho : S.R 35 = binSyms W origin)
    (hc : S.R 36 = binSyms W n) (hz : S.R 37 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hw : (S.R 94).length = w) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = [])
    (hsrc : S.R 110 = cstream A w (packedInterval origin span F))
    (hrow : (S.R 103).length = 1) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], S.R k = []) :
    ∃ v' B m, v'.user = v.user ∧
      m ≤ (110*W+4*V+137)+(localRowControlsCost W V span w n+n*(14*w+25)+12*(span*w)+6*w+38) ∧
      Exec body preparedLocalRowSelection (mk v S) m (mk v' B) ∧
      B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
      B.R 108 = cstream A w (packedInterval a n (fun j => F (rowIndex s t j)))++S.R 108 ∧
      B.R 91 = localRowControls A s t a n origin w ∧
      B.R 109 = (localRowOrigins s t a n origin 1).flatMap (binSyms V)++S.R 109 ∧
      B.R 116 = List.replicate n tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → B.R k = S.R k := by
  exact preparedLocalRowSelection_exec_of_payload hn hwide hwindow hwV hspan hvol hVW hA hVpos
    (cstream A w (packedInterval origin span F))
    (cstream A w (packedInterval a n (fun j => F (rowIndex s t j))))
    (by rw [length_cstream,packedInterval_length F htarget])
    (localRowOrigins_payload A w a n origin span F hsource htarget hwindow)
    v S hW hV hs ht ha ho hc hz hblank hw h104 h106 h116 hfresh hsrc hrow hcontrol hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
