module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatch

/-! # Pack both raw batches, call the product once, restore the packed banks

The reusable symbol-count and padding counters and header are explicit setup inputs. No
record has a prepared-state or execution oracle. Only the output register changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

/-- One batch packer's exact cost. -/
def batchPackCost (M r w a : ℕ) : ℕ :=
  M * (18 * (a * w) + 4 * ((r - a) * w) + 2 * (r * w) + 25) + 8

/-- Both operand packers, the shared multiplication, and both packed-bank cleanups. -/
def batchCost (p l w M a b : ℕ) : ℕ :=
  batchPackCost M (2 ^ l) w a + batchPackCost M (2 ^ l) w b +
    M * rpRecCost p l w + rpFixCost p l w + 4 * (M * 2 ^ l * w) + 4

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

noncomputable def batchProgram (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (records recordSaved countX padX srcX countY padY srcY saved acc buf savedBlock tmp : Fin T) :
    Pr P T Q A U :=
  .seq (packBatch records recordSaved countX padX srcX saved acc buf savedBlock tmp (rg .xs)) <|
  .seq (packBatch records recordSaved countY padY srcY saved acc buf savedBlock tmp (rg .ys)) <|
  .seq (rpProg rg ι h.ι_inj hT hQ) <|
  .seq (uclear (rg .xs)) (uclear (rg .ys))

/-- Execute a batch from raw streams with one shared ring-product call. Setup counters and
header are unchanged; all packed copies and scratch are restored. -/
theorem batchProgram_prefix_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (records recordSaved countX padX srcX countY padY srcY saved acc buf savedBlock tmp : Fin T)
    (hpackX : [records, recordSaved, countX, padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup)
    (hpackY : [records, recordSaved, countY, padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup)
    (hoffY : ∀ k ∈ [records, recordSaved, countY, padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs)
    (v : HS T Q A U) (S : Stacks T A) (tailX tailY : List (Fin (A + 4)))
    (hc : RpClean ι S)
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap X) ++ tailX)
    (hsrcY : S.R srcY = cstream A w ((List.range M).flatMap Y) ++ tailY)
    (hcountX : (S.R countX).length = a * w) (hcountY : (S.R countY).length = b * w)
    (hpadX : (S.R padX).length = (2 ^ l - a) * w)
    (hpadY : (S.R padY).length = (2 ^ l - b) * w)
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hwn : (S.R (rg .wn)).length = w)
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchCost p l w M a b ∧
      Exec body (batchProgram rg ι h hT hQ records recordSaved countX padX srcX countY padY srcY
        saved acc buf savedBlock tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  have ne (r s : RpReg) (hrs : r ≠ s) : rg r ≠ rg s := h.rg_inj.ne hrs
  set PX := cstream A w (rpStream M (fun n => recOf (2 ^ l) (block (X n))))
  set PY := cstream A w (rpStream M (fun n => recOf (2 ^ l) (block (Y n))))
  obtain ⟨v₁, hu₁, he₁⟩ := packBatch_coeffs_prefix_exec (body := body) hpackX M a (2 ^ l) w X ha hlenX
    v S tailX hrecords hsrcX hcountX hpadX (hscratch _ (by simp)) (hscratch _ (by simp))
    (hscratch _ (by simp)) (hscratch _ (by simp)) (hscratch _ (by simp)) (hscratch _ (by simp))
  rw [hempty .xs (by simp), List.append_nil] at he₁
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg .xs) PX }
  have e₁ (k : Fin T) (hk : k ≠ rg .xs) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂⟩ := packBatch_coeffs_prefix_exec (body := body) hpackY M b (2 ^ l) w Y hb hlenY
    v₁ S₁ tailY
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hrecords)
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hsrcY)
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hcountY)
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hpadY)
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hscratch _ (by simp))
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hscratch _ (by simp))
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hscratch _ (by simp))
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hscratch _ (by simp))
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hscratch _ (by simp))
    (by rw [e₁ _ (hoffY _ (by simp))]; exact hscratch _ (by simp))
  rw [e₁ _ (ne .ys .xs (by decide)), hempty .ys (by simp), List.append_nil] at he₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .ys) PY }
  have e₂ (r : RpReg) (hxs : r ≠ .xs) (hys : r ≠ .ys) : S₂.R (rg r) = S.R (rg r) := by
    simp [S₂, S₁, ne r .xs hxs, ne r .ys hys]
  have hc₂ : RpClean ι S₂ := by
    refine ⟨hc.1, fun j hj => ?_⟩
    simp [S₂, S₁, (h.priv .xs j hj).symm, (h.priv .ys j hj).symm, hc.2 j hj]
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := batch_exec (body := body) h hT hQ hA hp hw X Y
    (fun n hn => by rw [hlenX n hn, hlenY n hn]; exact hab) hX hY v₂ S₂ hc₂
    (by simp [S₂, S₁, ne .xs .ys (by decide), PX]) (by simp [S₂, PY])
    (by rw [e₂ .wn (by decide) (by decide)]; exact hwn)
    (by rw [e₂ .sv (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .ta (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .tb (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .acc (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .tmp (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .d0 (by decide) (by decide)]; exact hd0)
    (by rw [e₂ .d1 (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .d2 (by decide) (by decide)]; exact hempty _ (by simp))
    (by rw [e₂ .d3 (by decide) (by decide)]; exact hempty _ (by simp))
  set S₃ : Stacks T A := { S₂ with R := (Function.update S₂.R (rg .out)
    (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S₂.R (rg .out))) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body (rg .xs) v₃ S₃
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg .xs) [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body (rg .ys) v₄ S₄
  refine ⟨v₅, _, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · have hlen₁ : (S₃.R (rg .xs)).length = M * 2 ^ l * w := by
      simp [S₃, S₂, S₁, ne .xs .out (by decide), ne .xs .ys (by decide), PX]
    have hlen₂ : (S₄.R (rg .ys)).length = M * 2 ^ l * w := by
      simp [S₄, S₃, S₂, ne .ys .xs (by decide), ne .ys .out (by decide), PY]
    rw [hlen₁, hlen₂]
    unfold batchCost batchPackCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hkX : k = rg .xs
    · subst k
      simp [S₄, S₃, S₂, S₁, ne .xs .ys (by decide), ne .xs .out (by decide), hempty .xs (by simp)]
    by_cases hkY : k = rg .ys
    · subst k
      simp [S₄, S₃, S₂, S₁, ne .ys .out (by decide), hempty .ys (by simp)]
    simp [S₄, S₃, S₂, S₁, Function.update_apply, hkX, hkY,
      ne .out .xs (by decide), ne .out .ys (by decide)]

theorem batchProgram_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (records recordSaved countX padX srcX countY padY srcY saved acc buf savedBlock tmp : Fin T)
    (hpackX : [records, recordSaved, countX, padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup)
    (hpackY : [records, recordSaved, countY, padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup)
    (hoffY : ∀ k ∈ [records, recordSaved, countY, padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap X))
    (hsrcY : S.R srcY = cstream A w ((List.range M).flatMap Y))
    (hcountX : (S.R countX).length = a * w) (hcountY : (S.R countY).length = b * w)
    (hpadX : (S.R padX).length = (2 ^ l - a) * w)
    (hpadY : (S.R padY).length = (2 ^ l - b) * w)
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hwn : (S.R (rg .wn)).length = w)
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchCost p l w M a b ∧
      Exec body (batchProgram rg ι h hT hQ records recordSaved countX padX srcX countY padY srcY
        saved acc buf savedBlock tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  simpa only [List.append_nil] using
    batchProgram_prefix_exec h hT hQ hA hp hw ha hb hab X Y hlenX hlenY hX hY
      records recordSaved countX padX srcX countY padY srcY saved acc buf savedBlock tmp
      hpackX hpackY hoffY v S [] [] hc hrecords
      (by simpa using hsrcX) (by simpa using hsrcY)
      hcountX hcountY hpadX hpadY hscratch hwn hempty hd0

/-- A batch pays the ring product's fixed charge once, plus linear packing and cleanup. -/
theorem batchCost_le (p l w M a b : ℕ) (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) :
    batchCost p l w M a b ≤ M * (rpRecBound p l w + 44 * (2 ^ l * w) + 50) +
      rpFixCost p l w + 20 := by
  have hA : (2 ^ l - a) * w + a * w = 2 ^ l * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel ha]
  have hB : (2 ^ l - b) * w + b * w = 2 ^ l * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hb]
  have hpackA : 18 * (a * w) + 4 * ((2 ^ l - a) * w) + 2 * (2 ^ l * w) + 25 ≤
      20 * (2 ^ l * w) + 25 := by omega
  have hpackB : 18 * (b * w) + 4 * ((2 ^ l - b) * w) + 2 * (2 ^ l * w) + 25 ≤
      20 * (2 ^ l * w) + 25 := by omega
  have hmA := Nat.mul_le_mul_left M hpackA
  have hmB := Nat.mul_le_mul_left M hpackB
  have hmR := Nat.mul_le_mul_left M (rpRecCost_le p l w)
  unfold batchCost batchPackCost
  ring_nf at hmA hmB ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
