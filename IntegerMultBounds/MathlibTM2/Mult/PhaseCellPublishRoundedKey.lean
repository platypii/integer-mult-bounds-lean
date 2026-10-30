module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenPackedKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Generate all private dimensions for common-width local output publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def publishRoundedKey (precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T) : Pr P T Q A U :=
  .seq (generateDoubleWidth 13 precision width tmp)
    (.seq (unaryProduct rows width rowWidth saved tmp)
      (.seq (widenPackedKey wide width replicas rowWidth count src work saved tmp extra)
        (.seq (uclear rowWidth) (uclear width))))

def publishRoundedKeyCost (p W N L : ℕ) : ℕ :=
  let k := 2*p+13
  widenPackedKeyCost k W N (L*k) (N*L)+8*p+L*(6*k+9)+2*k+17

/-- Starting from p, N, the core row count and common width, construct the
rounded width 2p+13, row width and total symbol count. All three owned headers
and scratch clear after the actual common-width publication. -/
theorem publishRoundedKey_exec {precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T}
    (hreg : [precision,wide,width,replicas,rows,rowWidth,count,src,work,saved,tmp,extra].Nodup)
    (p W N L : ℕ) (hW : 2*p+13 ≤ W)
    (xs : List GaussianInt) (hlen : xs.length = N*L) (hfit : ∀ z ∈ xs, TopFitsZ (2*p+13) z)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprecision : (S.R precision).length = p) (hwide : (S.R wide).length = W)
    (hreplicas : (S.R replicas).length = N) (hrows : (S.R rows).length = L)
    (hsrc : S.R src = cstream A (2*p+13) xs++tail)
    (hblank : ∀ r ∈ [width,rowWidth,count,work,saved,tmp,extra], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ publishRoundedKeyCost p W N L ∧
      Exec body (publishRoundedKey precision wide width replicas rows rowWidth count src work saved tmp extra)
        (mk v S) n (mk v' {S with R := Function.update S.R src (cstream A W xs++tail)}) := by
  have hr := hreg
  regs_ne hr
  let k := 2*p+13
  obtain ⟨v₁,hu₁,he₁⟩ := generateDoubleWidth_exec (body := body)
    (show [precision,width,tmp].Nodup by regs_nodup) p 13 v S hprecision
    (hblank width (by simp)) (hblank tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R width (List.replicate k tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (show [rows,width,rowWidth,saved,tmp].Nodup by regs_nodup) v₁ S₁
    (by simpa [S₁,‹width ≠ saved›.symm] using hblank saved (by simp))
    (by simpa [S₁,‹width ≠ tmp›.symm] using hblank tmp (by simp))
  have hn₂' : n₂ ≤ L*(4*k+9)+4 := by simpa [S₁,‹width ≠ rows›.symm,hrows] using hn₂
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R rowWidth (List.replicate (L*k) tick)}
  have he₂' : Exec body (unaryProduct rows width rowWidth saved tmp) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,‹width ≠ rows›.symm,‹width ≠ rowWidth›.symm,hrows,hblank rowWidth (by simp)] using he₂
  have hsmall : ∀ r ∈ [count,work,saved,tmp,extra], S₂.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [S₂,S₁, *, Ne.symm]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := widenPackedKey_exec (body := body)
    (show [wide,width,replicas,rowWidth,count,src,work,saved,tmp,extra].Nodup by regs_nodup)
    k W N (L*k) (by dsimp [k]; omega) hW xs hfit (by rw [hlen]; ring) tail v₂ S₂
    (by simpa [S₂,S₁, *, Ne.symm] using hwide) (by simp [S₂,S₁, *, Ne.symm])
    (by simpa [S₂,S₁, *, Ne.symm] using hreplicas) (by simp [S₂])
    (by simpa [S₂,S₁,k,‹rowWidth ≠ src›.symm,‹width ≠ src›.symm] using hsrc) hsmall
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R src (cstream A W xs++tail)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) rowWidth v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R rowWidth []}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) width v₄ S₄
  refine ⟨v₅,(8*p+9)+n₂+n₃+(2*(L*k)+2)+(2*k+2),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · rw [hlen] at hn₃
    unfold publishRoundedKeyCost
    change (8*p+9)+n₂+n₃+(2*(L*k)+2)+(2*k+2) ≤
      widenPackedKeyCost k W N (L*k) (N*L)+8*p+L*(6*k+9)+2*k+17
    have hc : L*(6*k+9) = L*(4*k+9)+2*(L*k) := by ring
    omega
  · simp [S₄,S₃,S₂,S₁, *, Ne.symm,Nat.add_assoc]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hw : i = width
    · subst i; simp [S₄,S₃,S₂,S₁, *, Ne.symm]
    by_cases hr : i = rowWidth
    · subst i; simp [S₄,S₃,S₂,S₁, *, Ne.symm]
    by_cases hs : i = src
    · subst i; simp [S₄,S₃,S₂,S₁, *, Ne.symm]
    · simp [S₄,S₃,S₂,S₁,hw,hr,hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
