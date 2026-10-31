module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarNativeStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStreamStock

/-! Route, multiply with one shared reserve, retire operands and publish. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def runWorkspace (C M L w : ℕ) : ℕ :=
  3*routeCost M L w+realScalarWorkspace C w (M*L)+3*(6*(M*L*w)+2*w+8)

theorem run_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w M L : ℕ} (hw : q + 4 ≤ w) (xs : List GaussianInt) (a : GaussianInt)
    (hlen : xs.length = M * L) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 2)
    (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hr : Ready (fun r => S.R (cr r)) w q) (hc : CClean mul S)
    (hwork : ∀ r ∈ [CR.xs, .ys, .xsv, .ysv, .acc, .out], S.R (cr r) = [])
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w xs ++ tail) (hscalar : S.R 96 = csyms A w a)
    (C : ℕ) (hpush : mnProgPush (cmulBlock cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ C)
    (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runCost M L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+runWorkspace C M L w)
        depth (run hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R 93
          (cstream A w (xs.map (fun x => tdivN q (x * a))) ++ tail)) }) := by
  have hsmall (k : Fin 117) (hk : k.val < 64) : S.R k = [] := by
    have hh := (hc ⟨k.val, hk⟩).2
    exact hh
  have h84 : S.R 84 = [] := hwork .xs (by simp)
  have h85 : S.R 85 = [] := hwork .ys (by simp)
  have h89 : S.R 89 = [] := hwork .out (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := route_exec (body := body) M L w xs a hlen v S tail
    hbatch hrows hwidth hsrc hscalar (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hsmall _ (by decide) | exact h84 | exact h85)
  let SR : Stacks 117 A := { S with R := routeR S.R (cstream A w xs) tail (csyms A w a) }
  have hfits (z : GaussianInt) (hz : ‖value q z‖ ≤ 2) : Fits w z := by
    apply fits_of_norm_value_bound _ 2 hz
    calc
      (2 : ℝ) ^ q * 2 = 2 ^ (q + 1) := by rw [pow_succ]
      _ < _ := pow_lt_pow_right₀ (by norm_num) (by omega)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := realScalarStream_exec_within (body := body) (q := q) (w := w)
    cr_injective cr_mul mul_injective (by decide) hQ hA (by omega) (by omega)
    xs a (fun x hx => hfits x (hxs x hx)) (hfits a ha) har v₁ SR
    (routeR_clean S _ _ _ hc) (routeR_ready q w S.R _ _ _ hr)
    (by simp [SR, routeR, cr, OutputPlacement.code])
    (by simp [SR, routeR, cr, OutputPlacement.code])
    (by simpa [SR, routeR, cr, OutputPlacement.code] using hwork .xsv (by simp))
    (by simpa [SR, routeR, cr, OutputPlacement.code] using hwork .ysv (by simp))
    (by simpa [SR, routeR, cr, OutputPlacement.code] using hwork .acc (by simp))
  have ho : SR.R (cr .out) = [] := by simp [SR, routeR, cr, OutputPlacement.code, h89]
  rw [ho, List.append_nil] at he₂
  have ht₂ := he₂ C hpush depth
  have he₂' : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ SR)+depth+realScalarWorkspace C w xs.length) depth (realScalarStream cr mul mul_injective (by decide) hQ) (mk v₁ SR) m₂
      (mk v₂ { S with R := (Function.update (routeR S.R (cstream A w xs) tail (csyms A w a))
        89 (cstream A w (xs.map (fun x => tdivN q (x * a))))) }) := by
    simpa only [SR, show cr .out = (89 : Fin 117) from rfl] using ht₂
  obtain ⟨v₃, hu₃, he₃⟩ := finish_exec (body := body) w xs (xs.map (fun x => tdivN q (x * a))) a
    (by simp) v₂ S tail (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hsmall _ (by decide)
      · exact h84
      · exact h85
      · exact h89)
  have ht₁ := mn_native_exec_within he₁ 3 route_native depth
    (mnSize (mk v S)+depth+3*routeCost M L w)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₁) _)
  have ht₃ := mn_native_exec_within he₃ 3 finish_native depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add he₂' ht₃)
  refine ⟨v₃,m₁+(m₂+(6*(xs.length*w)+2*w+8)),hu₃.trans (hu₂.trans hu₁),?_,ht.mono ?_⟩
  · rw [hlen] at hm₂ ⊢
    unfold runCost
    nlinarith only [hm₁, hm₂]
  · intro d z hz
    rw [hlen] at hz
    dsimp only [runWorkspace]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
