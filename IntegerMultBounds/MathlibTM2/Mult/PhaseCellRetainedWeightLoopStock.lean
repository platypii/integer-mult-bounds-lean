module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightFrameStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopWithin

/-! All retained weight rows share one arithmetic reserve; archives pay by volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem retainedWeightLoop_exec_within {V w q P s t u L B : ℕ} (lo : ℕ → ℕ) (st : TblSt 48 A)
    (hready : WeightReady A V P q s t u L st)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : ∀ i < B, lo i < s) (hL : L ≤ s)
    (hV : V = weightWorkspaceWidth P q w t u) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A+4)))
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st))
    (hwidth : (S.R 94).length = w) (hrows : (S.R 103).length = L)
    (hcount : (S.R 115).length = V) (hrow : (S.R 64).length = L*w) (hbatch : (S.R 107).length = B)
    (hsrc : S.R 109 = (List.range B).flatMap (fun i => binSyms V (lo i)) ++ tail)
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108], S.R k = []) :
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ B*(retainedWeightStepCost V w P L+3)+2 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        (2*(B*(L*w))+retainedWeightStepWorkspace V w L)) 0 retainedWeightLoop (mk v S) m (mk v' S') ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 107 = [] ∧ S'.R 109 = tail ∧
      S'.R 95 = (List.range B).reverse.flatMap (fun i => outputWeightRow A w q P s t u L (lo i)) ++ S.R 95 ∧
      S'.R 113 = (List.range B).reverse.flatMap (fun i => inputWeightRow A w q P s t u L (lo i)) ++ S.R 113 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k.val ≥ 63 → k ≠ 109 → k ≠ 95 → k ≠ 113 → k ≠ 107 → S'.R k = S.R k := by
  let X := fun i => outputWeightRow A w q P s t u L (lo i)
  let Y := fun i => inputWeightRow A w q P s t u L (lo i)
  let F : ℕ → List (Fin (A+4)) := fun i => binSyms V (lo i)
  let Inv := fun j (Si : Stacks 117 A) => ∃ sti,
    WeightReady A V P q s t u L sti ∧
    tblHolds coefficientReg Si (tblRho V (List.replicate V tick) (List.replicate w tick) sti) ∧
    Si.R 109 = ((List.range B).drop j).flatMap F ++ tail ∧
    Si.R 95 = (List.range j).reverse.flatMap X ++ S.R 95 ∧
    Si.R 113 = (List.range j).reverse.flatMap Y ++ S.R 113 ∧
    Si.inp = S.inp ∧ Si.out = S.out ∧ Si.L = S.L ∧
    ∀ k, k.val ≥ 63 → k ≠ 109 → k ≠ 95 → k ≠ 113 → k ≠ 107 → Si.R k = S.R k
  have hstock (j : ℕ) (hj : j ≤ B) (vi : HS 117 Q A U) Si
      (hI : Inv j Si) (hc : (Si.R 107).length ≤ B) :
      mnSize (mk vi Si) ≤ mnSize (mk v S)+2*(B*(L*w)) := by
    obtain ⟨sti,hr,hh,hp,hx,hy,hi,ho,hl,hf⟩ := hI
    apply retainedWeight_stock_le v vi hS hh hready.acc hr.acc hi ho hl hf (B*(L*w))
    · rw [hx]
      simp only [List.length_append]
      have hlen : ((List.range j).reverse.flatMap X).length = j*(L*w) := by
        simp [X, List.length_flatMap]
      rw [hlen]
      have hm := Nat.mul_le_mul_right (L*w) hj
      omega
    · rw [hy]
      simp only [List.length_append]
      have hlen : ((List.range j).reverse.flatMap Y).length = j*(L*w) := by
        simp [Y, List.length_flatMap]
      rw [hlen]
      have hm := Nat.mul_le_mul_right (L*w) hj
      omega
    · rw [hp,hsrc]
      simp only [List.length_append]
      have hlen (xs : List ℕ) : (xs.flatMap F).length = xs.length*V := by
        simp [F, List.length_flatMap]
      rw [hlen,hlen]
      simp only [List.length_drop,List.length_range]
      have hm := Nat.mul_le_mul_right V (Nat.sub_le B j)
      omega
    · rw [hbatch]
      exact hc
  have hstable : ∀ j Si xs, Inv j Si → Inv j { Si with R := Function.update Si.R 107 xs } := by
    intro j Si xs ⟨sti, hr, hh, hp, hx, hy, hi, ho, hl, hf⟩
    refine ⟨sti, hr, ?_, by simpa using hp, by simpa using hx, by simpa using hy, hi, ho, hl, ?_⟩
    · intro r
      have hn : coefficientReg r ≠ (107 : Fin 117) := by
        intro he; have h := coefficientReg_range r; rw [he] at h; omega
      simpa [hn] using hh r
    · intro k hk hn109 hn95 hn113 hn107
      simpa [hn107] using hf k hk hn109 hn95 hn113 hn107
  have hstep : ∀ j < B, ∀ (vi : HS 117 Q A U) Si, Inv j Si → (Si.R 107).length = B-(j+1) →
      ∃ v' S' m, v'.user = vi.user ∧ m ≤ retainedWeightStepCost V w P L ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        (2*(B*(L*w))+retainedWeightStepWorkspace V w L)) 0 retainedWeightStep (mk vi Si) m (mk v' S') ∧ S'.R 107 = Si.R 107 ∧ Inv (j+1) S' := by
    intro j hj vi Si hI hc
    have hsize := hstock j (by omega) vi Si hI (by omega)
    obtain ⟨sti, hr, hh, hp, hx, hy, hi, ho, hl, hf⟩ := hI
    have hd : (List.range B).drop j = j :: (List.range B).drop (j+1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hj)]
      simp
    let rest := ((List.range B).drop (j+1)).flatMap F ++ tail
    obtain ⟨v', S', m, st', hv, hm, he, hr', hh', hp', hs110, hx', hy', hi', ho', hl', hf'⟩ :=
      retainedWeightStep_exec_within (body := body) sti hr hP hs hst hu (hlo j hj) hL hV vi Si rest hh
      (by rw [hf 94 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
      (by rw [hf 103 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hrows)
      (by rw [hf 115 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcount)
      (by rw [hf 64 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hrow)
      (by simpa [hd, F, rest, List.append_assoc] using hp) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        all_goals rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hfresh _ (by simp))
    refine ⟨v', S', m, hv, hm, (he 0).mono (by intro d z hz; omega), hf' 107 (by decide) (by decide) (by decide) (by decide) (by decide),
      st', hr', hh', hp', ?_, ?_, hi'.trans hi, ho'.trans ho, hl'.trans hl, ?_⟩
    · rw [hx', hx]
      simp [X, List.range_succ, List.reverse_append, List.append_assoc]
    · rw [hy', hy]
      simp [Y, List.range_succ, List.reverse_append, List.append_assoc]
    · intro k hk hn109 hn95 hn113 hn107
      by_cases hk110 : k = 110
      · subst k
        exact hs110.trans (hf 110 hk hn109 hn95 hn113 hn107)
      exact (hf' k hk hn109 hk110 hn95 hn113).trans (hf k hk hn109 hn95 hn113 hn107)
  obtain ⟨v', S', m, hv, hm, he, hc, hI⟩ := countedLoop_exec_within_remaining_costs
    (body := body) 107 retainedWeightStep B
    (mnSize (mk v S)+0+(2*(B*(L*w))+retainedWeightStepWorkspace V w L))
    (fun _ => retainedWeightStepCost V w P L) Inv hstable hstep v S hbatch
    ⟨st, hready, hS, by simpa [F] using hsrc, by simp, by simp, rfl, rfl, rfl, by intros; rfl⟩
    (by omega)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hm
  obtain ⟨st', hr, hh, hp, hx, hy, hi, ho, hl, hf⟩ := hI
  have hd : (List.range B).drop B = [] := List.drop_eq_nil_of_le (by simp)
  exact ⟨v', S', m, st', hv, hm, he, hr, hh, hc, by simpa [hd] using hp,
    hx, hy, hi, ho, hl, hf⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
