module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputCloseStock

/-! Ordinary precision/row headers generate and retire every output control. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def outputFromHeadersWorkspace (C q b l w M L : ℕ) : ℕ :=
  3*(22*b+8*l+4*w+6*(b+2*l+2)+29)+closedOutputWorkspace C q (b+2*l+2) w M L

theorem outputFromHeaders_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b l w M L : ℕ} (hq : 1 ≤ q) (hquarter : q = 4 * b) (hw : q + (b + 2 * l + 2) + 4 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = M * L) (hdslen : ds.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 4) (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hhigh : ∀ k ∈ [(114 : Fin 117), 115, 116], S.R k = [])
    (hqR : (S.R 100).length = q) (hlR : (S.R 101).length = l) (hwR : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 96 = cstream A w (outputWeightWords q ds) ++ borrowed)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C) (depth : ℕ) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ outputFromHeadersCost q b l w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+outputFromHeadersWorkspace C q b l w M L)
        depth (outputFromHeaders hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        |(value q (decodeWord (((SF.R 93).drop (i * w)).take w))).re -
          (ds[i]'(by rw [hdslen]; exact hi) : ℝ) * ((2 : ℝ) ^ (b + 2 * l + 2) * (value q (xs[i]'hi)).re)| ≤
          (2 + (2 : ℝ) ^ (b + 2 * l + 2 + 2)) / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef,herr⟩ := outputFromHeaders_exec (body := body) hQ hA hq hquarter hw
    xs ds hlen hdslen hxs hds v S tail borrowed hc hfresh hhigh hqR hlR hwR hbatch hrows hsrc htable
  let d := b + 2 * l + 2
  let shiftSymbols := tick :: tick :: (S.R 101).reverse ++ (S.R 101).reverse ++ List.replicate b tick
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 116 shiftSymbols)
    115 ((S.R 94).reverse.drop d)) }
  have h26 : S.R 26 = [] := (hc ⟨26, by decide⟩).2
  have h27 : S.R 27 = [] := (hc ⟨27, by decide⟩).2
  obtain ⟨v₁, hu₁, he₁⟩ := outputHeaders_exec (body := body)
    (precision := 100) (rows := 101) (width := 94) (shift := 116) (rest := 115) (saved := 26) (tmp := 27)
    (by decide) b v S (by omega) (by omega)
    (hhigh 116 (by simp)) (hhigh 115 (by simp)) h26 h27
  have he₁' : Exec body (outputHeaders 100 101 94 116 115 26 27) (mk v S)
      (22 * b + 8 * l + 4 * w + 6 * d + 29) (mk v₁ S₁) := by
    simpa only [hlR, hwR] using he₁
  have hdlen : (S₁.R 116).length = d := by simp [S₁, shiftSymbols, d, hlR]; omega
  have hrlen : (S₁.R 115).length = w - d := by simp [S₁, hwR]
  have hclean : CClean mul S₁ := by
    intro i
    have hi := i.isLt
    have hn (k : Fin 117) (hk : 64 ≤ k.val) : mul i ≠ k := by
      intro he
      have hv := congrArg (fun k : Fin 117 => k.val) he
      simp only [mul] at hv
      omega
    refine ⟨(hc i).1, ?_⟩
    simpa [S₁, hn 115 (by decide), hn 116 (by decide)] using (hc i).2
  have hfr : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hn (k : Fin 117) (hk : 96 ≤ k.val) : cr r ≠ k := by
      intro he
      have hv := congrArg (fun k : Fin 117 => k.val) he
      omega
    simpa [S₁, hn 115 (by decide), hn 116 (by decide)] using hfresh r
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, _⟩ := closedOutputWeights_exec_within (body := body)
    (q := q) (d := d) (w := w) (M := M) (L := L) hQ hA hq hw xs ds hlen hdslen hxs hds
    v₁ S₁ tail borrowed hclean hfr
    (by simpa [S₁] using hhigh 114 (by simp))
    (by simpa [S₁] using hqR) (by simpa [S₁] using hwR) hdlen hrlen
    (by simpa [S₁] using hbatch) (by simpa [S₁] using hrows)
    (by simpa [S₁] using hsrc) (by simpa [S₁] using htable)
    C hpush depth
  let result := cstream A w (weightedOutputNumerators q d xs ds) ++ tail
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 93 result }
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [115, 116] (by decide) v₂ S₂
  have ht₁ := mn_native_exec_within he₁' 3 outputHeaders_native depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 0
    (by simp [clearWords,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add he₂ ht₃)
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ⟨vf,nf,huf,hnf,ht.mono ?_,herr⟩
  intro d' z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  dsimp only [d] at hz
  dsimp only [outputFromHeadersWorkspace]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
