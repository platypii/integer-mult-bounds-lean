module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTranslateHaloEndpoints

/-! Refresh endpoint geometry after installing a new binary origin. The old
lower endpoint still supplies the origin needed to recover the displacement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 272 Q A U}

def refreshHaloEndpoints : Pr P 272 Q A U :=
  .seq (bsub 155 149 104 269 270 271 106)
    (.seq translateHaloEndpoints (uclear 104))

theorem refreshHaloEndpoints_exec {V x y L band : ℕ} (hxy : x ≤ y)
    (hfit : y+(L+2*band) < 2^V) (v : HS 272 Q A U) (S : Stacks 272 A)
    (h155 : S.R 155 = binSyms V y)
    (h149 : S.R 149 = binSyms V x) (h151 : S.R 151 = binSyms V (x+L))
    (h156 : S.R 156 = binSyms V (x+L)) (h164 : S.R 164 = binSyms V (x+(L+2*band)))
    (hfresh : ∀ k ∈ ([104,269,270,271] : List (Fin 272)), S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body refreshHaloEndpoints (mk v S) (42*V+43)
        (mk v' (translatedHaloEndpoints V y L band S)) := by
  have hy : y < 2^V := by omega
  have hx : x < 2^V := by omega
  have hd : y-x < 2^V := by omega
  have hmod : (y+2^V-x)%2^V = y-x := by
    rw [show y+2^V-x = (y-x)+2^V by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hd]
  obtain ⟨v₁,hu₁,_,_,he₁⟩ := bsub_exec body
    (a := 155) (b := 149) (c := 104) (tx := 269) (ty := 270) (tz := 271) (cy := 106)
    (by decide) (by decide) (by decide) hy hx v S h155 h149
    (hfresh 269 (by decide)) (hfresh 270 (by decide)) (hfresh 271 (by decide))
  let H : Stacks 272 A := {S with R := Function.update S.R 104 (binSyms V (y-x))}
  have he₁' : Exec body (bsub 155 149 104 269 270 271 106) (mk v S) (8*V+8) (mk v₁ H) := by
    simpa only [H,hmod,hfresh 104 (by decide),List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := translateHaloEndpoints_exec (body := body) hxy hfit v₁ H
    (by simpa [H] using h149) (by simpa [H] using h151)
    (by simpa [H] using h156) (by simpa [H] using h164) (by simp [H]) (by
      intro k hk
      have hn : k ≠ 104 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
      simpa only [H,Function.update_of_ne hn] using hfresh k (List.mem_cons_of_mem _ hk))
  let J := translatedHaloEndpoints V y L band H
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 104 v₂ J
  have hlen : (J.R 104).length = V := by
    simp [J,translatedHaloEndpoints,writeRight,H,length_binSyms]
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hlen]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 104
    · subst k
      simp [J,translatedHaloEndpoints,writeRight,hfresh 104 (by decide)]
    simp only [J,translatedHaloEndpoints,writeRight,H,Function.update_apply]
    split_ifs <;> simp_all only

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
