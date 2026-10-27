module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingRow

/-! Row arithmetic consumes prepared operand prefixes independently of their supplier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem retainedCouplingArithmetic_exec (hQ : SS.states ≤ Q) {L q w : ℕ}
    (hA : 96 ≤ A) (hw : 1 ≤ w) (hqw : q ≤ w)
    (xs as : List GaussianInt) (rhs : GaussianInt) (hxslen : xs.length = L) (haslen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ z ∈ as, Fits w z ∧ z.im = 0)
    (v : HS 117 Q A U) (T : Stacks 117 A) (rhsTail : List (Fin (A+4)))
    (hwsrc : (T.R 94).length = w)
    (hrhs : T.R 93 = csyms A w rhs++rhsTail)
    (hc : CClean mul T) (hcr : ∀ r : CR, r ∉ [CR.wn,.pn,.nn] → T.R (cr r) = [])
    (hready : Ready (fun r => T.R (cr r)) w q)
    (h96 : T.R 96 = []) (h102 : T.R 102 = []) (h104 : T.R 104 = [])
    (h105 : T.R 105 = []) (h106 : T.R 106 = []) (h108 : T.R 108 = [])
    (h109 : T.R 109 = []) (h115 : T.R 115 = []) (h116 : T.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedCouplingRowCost L w ∧
      Exec body (retainedCouplingRow hQ)
        (mk v {T with R := (Function.update (Function.update (Function.update T.R
          111 (cstream A w as++T.R 111)) 102 (List.replicate L tick))
          110 (cstream A w xs++T.R 110))}) m
        (mk v' {T with R := (Function.update T.R 113
          (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum)++T.R 113))}) := by
  let S₁ : Stacks 117 A := {T with R := (Function.update (Function.update (Function.update T.R
    111 (cstream A w as++T.R 111)) 102 (List.replicate L tick))
    110 (cstream A w xs++T.R 110))}
  have hoff (r : Fin 117) (hr : r ≠ 111 ∧ r ≠ 102 ∧ r ≠ 110) : S₁.R r = T.R r := by
    simp [S₁,hr.1,hr.2.1,hr.2.2]
  have hcrOff (r : CR) : S₁.R (cr r) = T.R (cr r) := by
    apply hoff
    have hr := (cr_range r).2.1
    constructor
    · intro he; have hv := congrArg Fin.val he; omega
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;> omega
  have hc₁ : CClean mul S₁ := by
    intro i
    have hi := i.isLt
    have hn : mul i ≠ (111 : Fin 117) ∧ mul i ≠ 102 ∧ mul i ≠ 110 := by
      simp only [mul,ne_eq,Fin.ext_iff]
      omega
    exact ⟨(hc i).1,by rw [hoff (mul i) hn]; exact (hc i).2⟩
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retainedCouplingRow_exec (body := body) (L := L) hQ hA hw hqw xs as rhs
    hxslen haslen
    hxs
    has v S₁ (T.R 110) (T.R 111) rhsTail
    (by simp [S₁]) (by simpa [S₁] using hwsrc)
    (by simp [S₁]) (by simp [S₁]) (by simpa [S₁] using hrhs) hc₁
    (by intro r hr; rw [hcrOff r]; exact hcr r hr)
    (by simpa only [hcrOff] using hready)
    (by intro k hk hgeom
        simp only [integerRowWork,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h
        · subst k; rw [hcrOff]; exact hcr _ (by decide)
        · subst k; rw [hcrOff]; exact hcr _ (by decide)
        · subst k; rw [hcrOff]; exact hcr _ (by decide)
        · subst k; rw [hcrOff]; exact hcr _ (by decide)
        · subst k; rw [hcrOff]; exact hcr _ (by decide)
        · subst k; rw [hcrOff]; exact hcr _ (by decide)
        · subst k; simpa [S₁] using h96
        · subst k; simp at hgeom
        · subst k; simp at hgeom
        · subst k; simp at hgeom
        · subst k; simpa [S₁] using h104
        · subst k; simpa [S₁] using h105
        · subst k; simpa [S₁] using h106)
    (by simpa [S₁] using h109)
    (by simpa [S₁] using h108)
    (by simpa [S₁] using h115)
    (by simpa [S₁] using h116)
  have hm₂' : m₂ ≤ retainedCouplingRowCost L w := hm₂
  have hresult :
      {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
        113 (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum)++S₁.R 113))
          110 (T.R 110)) 111 (T.R 111)) 102 [])} =
      {T with R := (Function.update T.R 113
        (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum)++T.R 113))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h111 : k = 111 <;> by_cases hk102 : k = 102 <;>
      simp [S₁,h110,h111,hk102,h102,Function.update_apply]
  exact ⟨v₂,m₂,hu₂,hm₂',he₂.cast rfl (congrArg (mk v₂) hresult)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
