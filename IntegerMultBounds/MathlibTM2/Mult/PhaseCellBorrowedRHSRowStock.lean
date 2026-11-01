module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedRHSRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowCallStock

/-! Coupling operand retirement and borrowed RHS traffic preserve one numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem retireCouplingOperands_native : mnNativePushBound 3
    (retireCouplingOperands (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [retireCouplingOperands,unaryProduct,scanP,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    discardPrefix,transfer,transferAct,clearWords,uclear,moveR,moveStep,whileR,peekR,popPush,
    mnNativePushBound,mnActPush]

theorem copyPrefix_native (count src dst saved tmp : Fin 117) : mnNativePushBound 3
    (copyPrefix (P := P₀) (Q := Q) (A := A) (U := U) count src dst saved tmp) := by
  simp [copyPrefix,transfer,transferAct,copyR,copyStep,moveR,moveStep,scanR,drainR,popDo,keepIn,
    whileR,peekR,mnNativePushBound,mnActPush]

theorem discardPrefix_native (count src trash tmp : Fin 117) : mnNativePushBound 3
    (discardPrefix (P := P₀) (Q := Q) (A := A) (U := U) count src trash tmp) := by
  simp [discardPrefix,transfer,transferAct,uclear,moveR,moveStep,scanR,drainR,popDo,keepIn,
    whileR,peekR,mnNativePushBound,mnActPush]

theorem consumedIntegerRow_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw : 1 ≤ w) (hqw : q ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 112 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L*(rmulCost w+61*w+32)+14*w+76 ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace C w L+2000*(L+1)*(w+1))) depth
        (consumedIntegerRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := fixedPointRowCall_exec_within (body := body) hQ hA hw hqw xs as rhs
    hxlen halen hxs has C hpush v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork
  let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retireCouplingOperands_exec (body := body) L w
    (cstream A w xs) (cstream A w as) tailX tailA v₁ S₁
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha)
    (by simp [hxlen]) (by simp [halen]) (by simpa [S₁] using h109)
    (by simpa [S₁] using hwork 104 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 105 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 106 (by simp [integerRowWork]))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,?_⟩
  · nlinarith only [hm₁,hm₂]
  · intro depth
    have ht₂ := mn_native_exec_within he₂ 3 retireCouplingOperands_native depth
      (mnSize (mk v₁ S₁)+depth+3*(18*L*w+11*L+21))
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₂) _)
    exact (mn_seq_within_add (he₁ depth) ht₂).mono (by intro d z hz; nlinarith)

theorem borrowedRHSRow_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw : 1 ≤ w) (hqw : q ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 93 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L*(rmulCost w+61*w+32)+30*w+92 ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (realWeightWorkspace C w L+3000*(L+1)*(w+1))) depth
        (borrowedRHSRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  have h97 : S.R 97 = [] := hwork 97 (by simp [integerRowWork])
  have h98 : S.R 98 = [] := hwork 98 (by simp [integerRowWork])
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body)
    (count := 94) (src := 93) (dst := 112) (saved := 97) (tmp := 98) (by decide)
    v S (csyms A w rhs) tailR hrhs (by simp [hwR]) h97 h98
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 112 (csyms A w rhs++S.R 112)}
  have hcr (r : CR) : cr r ≠ (112 : Fin 117) := by
    have hr := (cr_range r).2.1
    intro he
    have hv := congrArg Fin.val he
    omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := consumedIntegerRow_exec_within (body := body) hQ hA hw hqw xs as rhs
    hxlen halen hxs has C hpush v₁ S₁ tailX tailA (S.R 112)
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha) (by simp [S₁])
    (by intro i
        have hn : mul i ≠ (112 : Fin 117) := by
          intro he
          have hv := congrArg Fin.val he
          have hi := i.isLt
          simp only [mul] at hv
          omega
        simpa [S₁,hn] using hc i)
    (by simpa only [S₁,Function.update_of_ne (hcr _)] using hready)
    (by intro k hk
        have hn : k ≠ 112 := by
          simp only [integerRowWork,List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h
          all_goals subst k; first | exact hcr _ | decide
        simpa [S₁,hn] using hwork k hk)
    (by simpa [S₁] using h109)
  let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
    113 (csyms A w z++S₁.R 113)) 110 tailX) 111 tailA) 102 [])}
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 94) (src := 112) (trash := 97) (tmp := 98) (by decide)
    (csyms A w rhs) (S.R 112) v₂ S₂ (by simp [S₂,S₁])
    (by simp [S₂,S₁,hwR]) (by simpa [S₂,S₁] using h97) (by simpa [S₂,S₁] using h98)
  refine ⟨v₃,(10*w+10)+(m₂+(6*w+6)),hu₃.trans (hu₂.trans hu₁),by omega,
    ?_⟩
  intro depth
  have ht₁ := mn_native_exec_within he₁ 3 (copyPrefix_native ..) depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 3 (discardPrefix_native ..) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add (he₂ depth) ht₃)
  refine (ht.mono (by intro d z hz; simp [csyms] at hz; nlinarith)).cast (by simp) ?_
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h : k = 112 <;> simp [S₂,S₁,h,z,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
