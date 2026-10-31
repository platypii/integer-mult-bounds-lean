module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchProgram
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchStock

/-! Complete raw short-convolution batches share one numerical workspace.
Packing adds only linear traffic, and retiring packed copies adds no stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Spec.SignedRingProduct
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

private theorem batchProgram_prefix_trace (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
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
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      rg ι h.ι_inj hT hQ) ≤ C) (depth : ℕ) :
    ∃ n z, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*batchPackCost M (2^l) w a+3*batchPackCost M (2^l) w b+
          (C+1)*rpWorkspace p l w M)) depth (batchProgram rg ι h hT hQ records recordSaved countX padX srcX countY padY srcY
        saved acc buf savedBlock tmp) (mk v S) n z := by
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
  obtain ⟨v₃, n₃, hu₃, hn₃, ht₃⟩ := batch_exec_within (body := body) h hT hQ hA hp hw X Y
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
  have ht₁ := mn_native_exec_within he₁ 3
    (packBatch_native records recordSaved countX padX srcX saved acc buf savedBlock tmp (rg .xs))
    depth _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂ 3
    (packBatch_native records recordSaved countY padY srcY saved acc buf savedBlock tmp (rg .ys))
    depth _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht₅ := mn_native_exec_within he₅ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add ht₂
    (mn_seq_within_add (ht₃ C hpush depth) (mn_seq_within_add ht₄ ht₅)))
  refine ⟨_,_,ht.mono ?_⟩
  intro d z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  unfold batchPackCost
  omega

theorem batchProgram_prefix_exec_within (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
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
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      rg ι h.ι_inj hT hQ) ≤ C) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchCost p l w M a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*batchPackCost M (2^l) w a+3*batchPackCost M (2^l) w b+
          (C+1)*rpWorkspace p l w M)) depth (batchProgram rg ι h hT hQ records recordSaved countX padX srcX countY padY srcY
        saved acc buf savedBlock tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  obtain ⟨vf,nf,huf,hnf,hef⟩ := batchProgram_prefix_exec (body := body) h hT hQ hA hp hw
    ha hb hab X Y hlenX hlenY hX hY records recordSaved countX padX srcX countY padY srcY
    saved acc buf savedBlock tmp hpackX hpackY hoffY v S tailX tailY hc hrecords hsrcX hsrcY
    hcountX hcountY hpadX hpadY hscratch hwn hempty hd0
  obtain ⟨n,z,ht⟩ := batchProgram_prefix_trace (body := body) h hT hQ hA hp hw
    ha hb hab X Y hlenX hlenY hX hY records recordSaved countX padX srcX countY padY srcY
    saved acc buf savedBlock tmp hpackX hpackY hoffY v S tailX tailY hc hrecords hsrcX hsrcY
    hcountX hcountY hpadX hpadY hscratch hwn hempty hd0 C hpush depth
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  exact ⟨vf,nf,huf,hnf,ht⟩

/-- One shared numerical reserve, linear padded payload and record counters. -/
theorem batchProgram_stock_le (C p l w M a b : ℕ) (ha : a ≤ 2^l) (hb : b ≤ 2^l) :
    3*batchPackCost M (2^l) w a+3*batchPackCost M (2^l) w b+
      (C+1)*rpWorkspace p l w M ≤
    (C+1)*rpWorkspace p l w 0+(1842*(C+1)+120)*(M*2^l*w)+150*M+48 := by
  have pack (a : ℕ) (ha : a ≤ 2^l) :
      batchPackCost M (2^l) w a ≤ M*(20*(2^l*w)+25)+8 := by
    have hsplit : (2^l-a)*w+a*w = 2^l*w := by
      rw [← Nat.add_mul,Nat.sub_add_cancel ha]
    have h := Nat.mul_le_mul_left M
      (show 18*(a*w)+4*((2^l-a)*w)+2*(2^l*w)+25 ≤ 20*(2^l*w)+25 by omega)
    unfold batchPackCost
    omega
  have hpa := pack a ha
  have hpb := pack b hb
  rw [rpWorkspace_affine p l w M]
  nlinarith only [hpa,hpb]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
