module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicResidualEntry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCoordinate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentColumnWidth
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankRoleCode

/-! Select a folded boundary coordinate and read its physical residual row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def cyclicEntryBase (r : TblR 5) : Fin 151 := ⟨(ForwardBankPlacement.code r).val,by
  have := (ForwardBankPlacement.code r).isLt; omega⟩
def cyclicEntryReg (r : TblR 5) : Fin 151 := Equiv.swap 5 115 (cyclicEntryBase r)

theorem cyclicEntryReg_injective : Function.Injective cyclicEntryReg := by
  apply (Equiv.injective (Equiv.swap _ _)).comp
  intro r t he
  apply ForwardBankPlacement.code_injective
  exact Fin.ext (congrArg (fun k : Fin 151 => k.val) he)

@[simp] theorem cyclicEntryReg_width : cyclicEntryReg .wr = 115 := by decide

theorem cyclicEntryReg_low (r : TblR 5) (hr : r ≠ .wr) : (cyclicEntryReg r).val < 20 := by
  have hbound : (cyclicEntryBase r).val < 20 := (ForwardBankPlacement.code r).isLt
  have h5 : cyclicEntryBase r ≠ 5 := by
    intro he
    apply hr
    apply ForwardBankPlacement.code_injective
    apply Fin.ext
    exact congrArg (fun k : Fin 151 => k.val) he
  have h115 : cyclicEntryBase r ≠ 115 := by intro he; have := congrArg (fun k : Fin 151 => k.val) he; omega
  simpa [cyclicEntryReg,Equiv.swap_apply_def,h5,h115] using hbound

theorem cyclicEntryReg_ne (k : Fin 151) (hk : 20 ≤ k.val) (h115 : k ≠ 115) : ∀ r, cyclicEntryReg r ≠ k := by
  intro r he
  by_cases hr : r = .wr
  · subst r; exact h115 he.symm
  · have hh := cyclicEntryReg_low r hr
    rw [he] at hh
    omega

def selectedCyclicColumnEntry : Pr P 151 Q A U :=
  .seq selectResidentCoordinate (.seq residentColumnWidth
    (.seq (generatedCyclicResidualEntry cyclicEntryReg 20 21 22 23 24 121 144 145 139 25 94 132 150 1 2 3 4 5 6)
      (clearWords [94,139])))

def cyclicEntryReadCost (V s a b i w : ℕ) : ℕ :=
  let j := cyclicResidualIndex s a b i
  ((s+a+b+i)*(4*V+10)+4*(8*V+12)+1+5*(4*V+4)+4*(8*V+8)+2)+
    (3*tblC V 0+((6*j+11*V+7)+(2*(5*V)+11)))+
    ((j*(12*w+9)+10*w+22)+(2*j+2))

def selectedCyclicColumnEntryCost (q V s a b n i : ℕ) : ℕ :=
  (n*(12*V+11)+27*V+6*i+36)+((8*q+9)+
    (cyclicEntryReadCost V s a b i (2*q+8)+(2*((2*q+8)+i)+5)))

theorem selectedCyclicColumnEntry_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V a b n : ℕ)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) (hn : n < B.card)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = n) (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (h94 : S.R 94 = []) (h106 : S.R 106 = []) (h135 : S.R 135 = []) (h139 : S.R 139 = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    let i := bFoldAt s B n
    ∃ v' m, v'.user = v.user ∧ m ≤ selectedCyclicColumnEntryCost q V s a b n i.val ∧
      Exec body selectedCyclicColumnEntry (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 0 []) 150
          (csyms A (2*q+8) (if a ≤ i.val ∧ i.val < b then C i else D i)++S.R 150))}) ∧
      i ∈ B ∧ bFoldPos s B i = n := by
  dsimp only
  let i := bFoldAt s B n
  let w := 2*q+8
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁,hi,hpos⟩ := selectResidentCoordinate_exec (body := body)
    B V n hA (by omega) hn pageTail v S hindex hwidth hpage h106 h139
    (fun k hk1 hk7 => hblank k (by omega) (by omega))
  let S₁ : Stacks 151 A := {S with R := Function.update (Function.update S.R 0 []) 139 (List.replicate i.val tick)}
  obtain ⟨v₂,hv₂,he₂⟩ := residentColumnWidth_exec (body := body) q v₁ S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using h94) (by simpa [S₁] using h135)
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 94 (List.replicate w tick)}
  have hlow (k : Fin 151) (hk : k.val < 31) : S₂.R k = [] := by
    have h94' : k ≠ 94 := by intro he; subst k; norm_num at hk
    have h139' : k ≠ 139 := by intro he; subst k; norm_num at hk
    by_cases h0 : k = 0
    · subst k; simp [S₂,S₁]
    · simpa [S₂,S₁,h94',h139',h0] using hblank k hk h0
  have hscalar : ∀ r, r ≠ .wr → S₂.R (cyclicEntryReg r) = [] := fun r hr =>
    hlow _ (by have := cyclicEntryReg_low r hr; omega)
  obtain ⟨v₃,m₃,hv₃,hm₃,he₃⟩ := generatedCyclicResidualEntry_exec (body := body) cyclicEntryReg cyclicEntryReg_injective
    20 21 22 23 24 121 144 145 139 25 94 132 150 1 2 3 4 5 6
    (cyclicEntryReg_ne 20 (by decide) (by decide)) (cyclicEntryReg_ne 25 (by decide) (by decide))
    (by intro src hsrc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hsrc
        rcases hsrc with rfl | rfl | rfl | rfl <;> decide)
    (by decide) V w a b i ha hb hwide C D tail (S₂.R 115) (by simpa [S₂,S₁] using hwidth) v₂ S₂
    (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using haSrc) (by simpa [S₂,S₁] using hbSrc)
    (by simp [S₂,S₁]) (by simp) hscalar
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hlow _ (by decide))
    (hlow 25 (by decide)) (by simp [S₂,w]) (by simpa [S₂,S₁] using hsource)
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hlow _ (by decide))
  let output := csyms A w (if a ≤ i.val ∧ i.val < b then C i else D i)++S.R 150
  let F : Stacks 151 A := {S₂ with R := Function.update S₂.R 150 output}
  have he₃' : Exec body (generatedCyclicResidualEntry cyclicEntryReg 20 21 22 23 24 121 144 145 139 25 94 132 150 1 2 3 4 5 6)
      (mk v₂ S₂) m₃ (mk v₃ F) := by simpa [S₂,S₁,F,output] using he₃
  have hcost₃ : m₃ ≤ cyclicEntryReadCost V s a b i.val w := by
    simpa [unaryScalarResultCost,cyclicResidualIndexInputs,binaryHeaderQueueCost_eq,
      S₂,S₁,hs,haSrc,hbSrc,cyclicEntryReadCost,Nat.add_assoc] using hm₃
  obtain ⟨v₄,hv₄,he₄⟩ := clearWords_exec (body := body) [(94 : Fin 151),139] (by decide) v₃ F
  have hsum : ([(94 : Fin 151),139].map (fun k => (F.R k).length)).sum = w+i.val := by simp [F,S₂,S₁]
  refine ⟨v₄,m₁+((8*q+9)+(m₃+(2*(w+i.val)+5))),hv₄.trans (hv₃.trans (hv₂.trans hv₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))).cast (by rw [hsum]; rfl) ?_,hi,hpos⟩
  · exact Nat.add_le_add hm₁ (Nat.add_le_add_left (Nat.add_le_add_right hcost₃ _) _)
  · apply congrArg (mk v₄)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94' : k = 94
      · subst k; simp [h94]
      by_cases h139' : k = 139
      · subst k; simp [h139]
      simp [F,S₂,S₁,output,h94',h139',Function.update_apply,w,i]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
