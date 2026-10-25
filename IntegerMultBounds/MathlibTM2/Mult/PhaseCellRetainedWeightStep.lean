module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightPage

/-! Move one retained-initialization page into the two batch accumulators. The
source payload and initialized table survive, ready for the next binary origin. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def retainedWeightStep : Pr P₀ 117 Q A U :=
  .seq retainedWeightPage (.seq (takePrefix 64 110 95 104 105) (takePrefix 64 110 113 104 105))

def retainedWeightStepCost (V w P L : ℕ) : ℕ := retainedWeightPageCost V w P L + 12*(L*w)+12

theorem retainedWeightStep_exec {V w q P s t u L lo : ℕ} (st : TblSt 48 A)
    (hready : WeightReady A V P q s t u L st)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s)
    (hV : V = weightWorkspaceWidth P q w t u) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A+4)))
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st))
    (hwidth : (S.R 94).length = w) (hrows : (S.R 103).length = L)
    (hcount : (S.R 115).length = V) (hrow : (S.R 64).length = L*w)
    (hsrc : S.R 109 = binSyms V lo ++ tail)
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108], S.R k = []) :
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ retainedWeightStepCost V w P L ∧
      Exec body retainedWeightStep (mk v S) m (mk v' S') ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 109 = tail ∧ S'.R 110 = S.R 110 ∧
      S'.R 95 = outputWeightRow A w q P s t u L lo ++ S.R 95 ∧
      S'.R 113 = inputWeightRow A w q P s t u L lo ++ S.R 113 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k.val ≥ 63 → k ≠ 109 → k ≠ 110 → k ≠ 95 → k ≠ 113 → S'.R k = S.R k := by
  obtain ⟨v₁, S₁, m₁, st₁, hu₁, hm₁, he₁, hr₁, hh₁, hpacket, hpage, hin, hout, hleft, hframe⟩ :=
    retainedWeightPage_exec (body := body) st hready hP hs hst hu hlo hL hV v S tail
      hS hwidth hrows hcount hsrc hfresh
  let X := outputWeightRow A w q P s t u L lo
  let Y := inputWeightRow A w q P s t u L lo
  have hX : X.length = L*w := by simp [X]
  have hY : Y.length = L*w := by simp [Y]
  obtain ⟨v₂, hu₂, he₂⟩ := takePrefix_exec (body := body)
    (show [(64 : Fin 117), 110, 95, 104, 105].Nodup by decide) v₁ S₁ X (Y ++ S.R 110)
    (by simpa [weightPage, X, Y, outputWeightRow, inputWeightRow, List.append_assoc] using hpage)
    (by rw [hframe 64 (by decide) (by decide) (by decide), hX]; exact hrow)
    (by rw [hframe 104 (by decide) (by decide) (by decide)]; exact hfresh 104 (by simp))
    (by rw [hframe 105 (by decide) (by decide) (by decide)]; exact hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 110
    (Y ++ S.R 110)) 95 (X ++ S.R 95)) }
  have he₂' : Exec body (takePrefix 64 110 95 104 105) (mk v₁ S₁) (6*(L*w)+6) (mk v₂ S₂) := by
    simpa [S₂, hX, hframe 95 (by decide) (by decide) (by decide)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := takePrefix_exec (body := body)
    (show [(64 : Fin 117), 110, 113, 104, 105].Nodup by decide) v₂ S₂ Y (S.R 110)
    (by simp [S₂]) (by simpa [S₂, hY, hframe 64 (by decide) (by decide) (by decide)] using hrow)
    (by simp [S₂, hframe 104 (by decide) (by decide) (by decide), hfresh 104 (by simp)])
    (by simp [S₂, hframe 105 (by decide) (by decide) (by decide), hfresh 105 (by simp)])
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R 110 (S.R 110))
    113 (Y ++ S.R 113)) }
  have he₃' : Exec body (takePrefix 64 110 113 104 105) (mk v₂ S₂) (6*(L*w)+6) (mk v₃ S₃) := by
    simpa [S₃, S₂, hY, hframe 113 (by decide) (by decide) (by decide)] using he₃
  refine ⟨v₃, S₃, m₁+((6*(L*w)+6)+(6*(L*w)+6)), st₁, hu₃.trans (hu₂.trans hu₁),
    by dsimp only [retainedWeightStepCost]; omega, Exec.seq he₁ (Exec.seq he₂' he₃'), hr₁, ?_, ?_,
    by simp [S₃], by simp [S₃, S₂, X], by simp [S₃, Y], hin, hout, hleft, ?_⟩
  · intro r
    have hr := coefficientReg_range r
    have hn (n : Fin 117) (hh : 63 ≤ n.val) : coefficientReg r ≠ n := by intro he; rw [he] at hr; omega
    simpa [S₃, S₂, hn 110 (by decide), hn 95 (by decide), hn 113 (by decide)] using hh₁ r
  · simpa [S₃, S₂] using hpacket
  · intro k hk hk109 hk110 hk95 hk113
    simpa [S₃, S₂, hk110, hk95, hk113] using hframe k hk hk109 hk110

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
