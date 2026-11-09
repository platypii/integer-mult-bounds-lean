module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowConsume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowCallStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixReleaseStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! One integer row keeps numerical scratch separate from owned descriptor retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

@[irreducible] def consumeIntegerRowWorkspace (C L w : ℕ) : ℕ :=
  (realWeightWorkspace C w L+1000*(L+1)*(w+1))+
    (3*(12*(L*w)+9*L+12)+2*(6*w+6))

theorem consumeIntegerRow_trace_within (hQ : SS.states ≤ Q) (C L w m₁ m₂ m₃ : ℕ)
    (v₀ v₁ v₂ v₃ : HS 117 Q A U) (S₀ S₁ S₂ S₃ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+
        (realWeightWorkspace C w L+1000*(L+1)*(w+1)))
      depth (integerRowCall hQ) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : Exec body (releaseFromDimensions 102 94 99 111 104 106 105)
      (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : Exec body (releasePrefix 94 112 104 105) (mk v₂ S₂) m₃ (mk v₃ S₃))
    (hm₂ : m₂ ≤ 12*(L*w)+9*L+12) (hm₃ : m₃ ≤ 6*w+6) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+consumeIntegerRowWorkspace C L w)
      depth (consumeIntegerRow hQ) (mk v₀ S₀) (m₁+(m₂+m₃)) (mk v₃ S₃) := by
  have ht₂ := mn_native_exec_within h₂ 3 (releaseFromDimensions_native ..) depth
    (mnSize (mk v₁ S₁)+depth+3*(12*(L*w)+9*L+12)) (by omega)
  have ht₃ := mn_native_exec_within h₃ 2 (releasePrefix_native ..) depth
    (mnSize (mk v₂ S₂)+depth+2*(6*w+6)) (by omega)
  exact (mn_seq_within_add (h₁ depth) (mn_seq_within_add ht₂ ht₃)).mono (by
    intro d z hz; simpa only [consumeIntegerRowWorkspace] using hz)

theorem consumeIntegerRow_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L w : ℕ} (hw : 1 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs ++ tailX) (ha : S.R 111 = cstream A w as ++ tailA)
    (hrhs : S.R 112 = csyms A w rhs ++ tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ integerRowCost L w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+consumeIntegerRowWorkspace C L w)
        depth (consumeIntegerRow hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R
          111 tailA) 112 tailR) 113
            (csyms A w (rhs - (List.zipWith (· * ·) xs as).sum) ++ S.R 113)) })) := by
  have hcall := fixedPointRowCall_exec_within (body := body) hQ hA hw (by omega : 0 ≤ w)
    xs as rhs hxlen halen hxs has C hpush v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork
  simp only [tdivN_precision_zero] at hcall
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := hcall
  let result := csyms A w (rhs - (List.zipWith (· * ·) xs as).sum)
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 113 (result ++ S.R 113) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseFromDimensions_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 111, 104, 106, 105].Nodup by decide) v₁ S₁
    (cstream A w as) tailA (by simpa [S₁] using ha)
    (by simp [S₁, halen, hL, hwR])
    (by simpa [S₁] using hwork 99 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 104 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 106 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 105 (by simp [integerRowWork]))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 111 tailA }
  obtain ⟨v₃, hu₃, he₃⟩ := releasePrefix_exec (body := body)
    (show [(94 : Fin 117), 112, 104, 105].Nodup by decide) v₂ S₂ (csyms A w rhs) tailR
    (by simpa [S₂, S₁] using hrhs) (by simpa [S₂, S₁, csyms] using hwR)
    (by simpa [S₂, S₁] using hwork 104 (by simp [integerRowWork]))
    (by simpa [S₂, S₁] using hwork 105 (by simp [integerRowWork]))
  refine ⟨v₃, m₁ + (m₂ + (6 * w + 6)), hu₃.trans (hu₂.trans hu₁), ?_,
    (fun depth => (consumeIntegerRow_trace_within hQ C L w m₁ m₂ _
      v v₁ v₂ v₃ S S₁ S₂ _ he₁ he₂ he₃ (by
        have hlen : (cstream A w as).length = L*w := by simp [halen]
        simpa only [S₁, Function.update_of_ne (show (102 : Fin 117) ≠ 113 by decide), hL, hlen] using hm₂)
      (by simp [csyms]) depth).cast (by simp [csyms]) ?_)⟩
  · simp only [S₁, Function.update_of_ne (show (102 : Fin 117) ≠ 113 by decide), hL] at hm₂
    have hlen : (cstream A w as).length = L * w := by simp [halen]
    rw [hlen] at hm₂
    unfold integerRowCost
    nlinarith only [hm₁, hm₂]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ha' : k = 111
    · subst k; simp [S₂, S₁]
    by_cases hr : k = 112
    · subst k; simp
    by_cases ho : k = 113
    · subst k; simp [S₂, S₁, result]
    simp [S₂, S₁, ha', hr, ho]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
