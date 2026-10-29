module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Prepare and release the control table for any ordered origin list. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedOriginAdvanceCost (V s w count : ℕ) : ℕ :=
  (32*V+41) + (w*(4*V+10)+6*V+10) +
    (count*(3*tblC V V+29*V+30)+8*s*w+11) + (38*V+39)

/-- Convert retained origins to forward controls, restoring all borrowed state. -/
theorem preparedOriginAdvanceControls_exec (V w s : ℕ) (origins : List ℕ)
    (hwV : w < 2^V) (hsW : s < 2^V) (hsV : s*w < 2^V)
    (hsorted : origins.Pairwise (· ≤ ·)) (hle : ∀ origin ∈ origins, origin ≤ s)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = origins.flatMap (binSyms V) ++ suffix)
    (hcount : S.R 116 = List.replicate origins.length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedOriginAdvanceCost V s w origins.length ∧
      Exec body preparedNaturalAdvanceControls (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 91
        (gatherControls A (originAdvances w 0 origins ++ [0]) ++ S.R 91) := by
  have hcoords : ∀ origin ∈ origins, origin < 2^V :=
    fun origin ho => (hle origin ho).trans_lt hsW
  have hunits : ∀ origin ∈ origins, origin*w < 2^V :=
    fun origin ho => (Nat.mul_le_mul_right w (hle origin ho)).trans_lt hsV
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeAdvanceBank_exec (body := body) V v S hV
    (hfresh 106 (by simp)) (fun r => hblank _ (advanceReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR advanceReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 19 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := advanceReg_range r
    rw [he] at hk
    omega
  have hhigh (k : Fin 117) (hk : 19 ≤ k.val) : ∀ r, advanceReg r ≠ k := by
    intro r he
    have hr := advanceReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := tbl_load1_runs (body := body)
    advanceReg_injective (List.replicate V tick) (List.replicate V tick) (by simp)
    (hhigh 94 (by decide)) 2 (⟨fun _ => 0, []⟩ : TblSt 4 A) w v₁ S₁
    (by rw [hoff₁ 94 (by decide)]; exact hw) hh₁
  have hh₂' : tblHolds advanceReg S₂ (tblRho V (List.replicate V tick) (List.replicate V tick)
      (advanceHeaderState A w)) := hh₂
  have hoff₂ (k : Fin 117) (hk : 19 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  have hfit : ∀ i, (advanceHeaderState A w).val i < 2^V := by
    intro i
    simp only [advanceHeaderState, Function.update_apply]
    split_ifs <;> first | exact hwV | positivity
  have ho : (0::origins).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp, hsorted⟩
  obtain ⟨st₃, v₃, S₃, n₃, hw₃, ha₃, hb₃, hu₃, hn₃, he₃, hh₃, hout₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    originAdvanceControls_exec (body := body) le_rfl (origins) ho hcoords hunits
      (advanceHeaderState A w) (by simp [advanceHeaderState]) (by simp [advanceHeaderState]) hfit
      (List.replicate origins.length tick) suffix (by simp)
      v₂ S₂ hh₂' (by rw [hoff₂ 116 (by decide)]; exact hcount) (by
        rw [hoff₂ 109 (by decide)]
        exact hsrc)
      (by rw [hoff₂ 88 (by decide)]; exact hfresh 88 (by simp))
      (by rw [hoff₂ 89 (by decide)]; exact hfresh 89 (by simp))
      (by rw [hoff₂ 90 (by decide)]; exact hfresh 90 (by simp))
  have ha : st₃.acc = [] := ha₃
  have hh₃' : tblHolds advanceReg S₃ (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st₃.val, []⟩) := by
    have heq : st₃ = ⟨st₃.val, []⟩ := by cases st₃; simp_all
    rw [← heq]
    exact hh₃
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseAdvanceBank_exec (body := body) V st₃.val v₃ S₃ hh₃'
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 19 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 19 ≤ k.val) (hk91 : k ≠ 91) : S₃.R k = S.R k :=
    (hf₃ k hk91 (hhigh k hk)).trans (hoff₂ k hk)
  refine ⟨v₄, S₄, (32*V+41)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · have hvol : (originAdvances w 0 origins).sum ≤ s*w := by
      simpa using originAdvances_sum_le w 0 s origins ho (by omega) hle
    unfold preparedOriginAdvanceCost
    nlinarith only [hn₂, hn₃, hn₄, hvol]
  · funext k
    by_cases hk91 : k = 91
    · subst k
      simpa [S₄, hoff₂ 91 (by decide)] using hout₃
    by_cases hk : k.val < 19
    · simp [S₄, hk, hk91, hblank k hk]
    simp [S₄, hk, hk91, hoff₃ k (by omega) hk91]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
