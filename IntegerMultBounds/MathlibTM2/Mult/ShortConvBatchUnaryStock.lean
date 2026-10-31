module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchUnary
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchProgramStock
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Shared unary setup and retirement preserve the batch's linear stock bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Spec.SignedRingProduct
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

private theorem batchFromUnary_prefix_trace (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    (j : SetupReg → Fin T) (hj : Function.Injective j)
    (hwidth : j .w = rg .wn) (hheader : j .header = rg .d0)
    (hoff : ∀ s ∈ setupCounters, ∀ r, j s ≠ rg r)
    (hpriv : ∀ s ∈ setupCounters, ∀ k, j s ≠ ι k)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (hpackX : [records, recordSaved, j .countX, j .padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup)
    (hpackY : [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup)
    (hoffY : ∀ k ∈ [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs)
    (hdata : ∀ k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp],
      ∀ s ∈ setupWritten, k ≠ j s)
    (v : HS T Q A U) (S : Stacks T A) (tailX tailY : List (Fin (A + 4)))
    (hc : RpClean ι S)
    (hpR : (S.R (j .p)).length = p) (hlR : (S.R (j .l)).length = l)
    (hwR : (S.R (j .w)).length = w) (haR : (S.R (j .a)).length = a) (hbR : (S.R (j .b)).length = b)
    (hemptySetup : ∀ s ∈ setupWritten ++ setupScratch, S.R (j s) = [])
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap X) ++ tailX)
    (hsrcY : S.R srcY = cstream A w ((List.range M).flatMap Y) ++ tailY)
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      rg ι h.ι_inj hT hQ) ≤ C) (depth : ℕ) :
    ∃ n z, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*batchSetupCost p l w a b+3*batchPackCost M (2^l) w a+
          3*batchPackCost M (2^l) w b+(C+1)*rpWorkspace p l w M))
        depth (batchFromUnary j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp)
        (mk v S) n z := by
  have ne (r s : RpReg) (hrs : r ≠ s) : rg r ≠ rg s := h.rg_inj.ne hrs
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := batchSetup_exec (body := body) j hj v S p l w a b
    hpR hlR hwR haR hbR hemptySetup
  set S₁ : Stacks T A := { S with R := setupBank j S.R p l w a b }
  have ering (r : RpReg) (hr : r ≠ .d0) : S₁.R (rg r) = S.R (rg r) := by
    apply setupBank_off
    intro s hs
    simp only [setupWritten, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact (hoff .countX (by simp [setupCounters]) r).symm
    · exact (hoff .padX (by simp [setupCounters]) r).symm
    · exact (hoff .countY (by simp [setupCounters]) r).symm
    · exact (hoff .padY (by simp [setupCounters]) r).symm
    · rw [hheader]; exact ne r .d0 hr
  have edata (k : Fin T) (hk : k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp]) :
      S₁.R k = S.R k := setupBank_off j S.R p l w a b k (hdata k hk)
  have ecount (s : SetupReg) (hs : s ∈ setupWritten) : S₁.R (j s) = setupValue A p l w a b s := by
    simp only [S₁, setupBank_at j hj, ite_eq_left hs]
  have hc₁ : RpClean ι S₁ := by
    refine ⟨hc.1, fun k hk => ?_⟩
    rw [show S₁.R (ι k) = S.R (ι k) from ?_]
    · exact hc.2 k hk
    · apply setupBank_off
      intro s hs
      simp only [setupWritten, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact (hpriv .countX (by simp [setupCounters]) k).symm
      · exact (hpriv .padX (by simp [setupCounters]) k).symm
      · exact (hpriv .countY (by simp [setupCounters]) k).symm
      · exact (hpriv .padY (by simp [setupCounters]) k).symm
      · rw [hheader, h.d0]
        intro he
        have := congrArg Fin.val (h.ι_inj he)
        simp at this
        omega
  obtain ⟨v₂, n₂, hu₂, hn₂, ht₂⟩ := batchProgram_prefix_exec_within (body := body) h hT hQ hA hp hw ha hb hab
    X Y hlenX hlenY hX hY records recordSaved (j .countX) (j .padX) srcX
    (j .countY) (j .padY) srcY saved acc buf savedBlock tmp hpackX hpackY hoffY v₁ S₁ tailX tailY hc₁
    (by rw [edata _ (by simp)]; exact hrecords)
    (by rw [edata _ (by simp)]; exact hsrcX) (by rw [edata _ (by simp)]; exact hsrcY)
    (by simp [ecount .countX (by simp [setupWritten]), setupValue])
    (by simp [ecount .countY (by simp [setupWritten]), setupValue])
    (by simp [ecount .padX (by simp [setupWritten]), setupValue])
    (by simp [ecount .padY (by simp [setupWritten]), setupValue])
    (fun k hk => by
      have hks : k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rw [edata k hks]
      exact hscratch k hk)
    (by rw [ering .wn (by decide), ← hwidth]; exact hwR)
    (fun r hr => by
      have hr0 : r ≠ .d0 := by intro he; subst r; simp at hr
      rw [ering r hr0]
      exact hempty r hr)
    (by rw [← hheader, ecount .header (by simp [setupWritten])]; rfl)
    C hpush depth
  set output := cstream A w (rpStream M (fun n => coeff p l (X n) (Y n)))
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .out) (output ++ S₁.R (rg .out)) }
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (setupWritten.map j)
    ((show setupWritten.Nodup by decide).map hj) v₂ S₂
  have ht₁ := mn_native_exec_within he₁ 3 (batchSetup_native j) depth
    (mnSize (mk v S)+depth+3*batchSetupCost p l w a b)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₁) _)
  have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native (setupWritten.map j))
    depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add ht₂ ht₃)
  refine ⟨_,_,ht.mono ?_⟩
  intro d z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  omega

theorem batchFromUnary_prefix_exec_within (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    (j : SetupReg → Fin T) (hj : Function.Injective j)
    (hwidth : j .w = rg .wn) (hheader : j .header = rg .d0)
    (hoff : ∀ s ∈ setupCounters, ∀ r, j s ≠ rg r)
    (hpriv : ∀ s ∈ setupCounters, ∀ k, j s ≠ ι k)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (hpackX : [records, recordSaved, j .countX, j .padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup)
    (hpackY : [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup)
    (hoffY : ∀ k ∈ [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs)
    (hdata : ∀ k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp],
      ∀ s ∈ setupWritten, k ≠ j s)
    (v : HS T Q A U) (S : Stacks T A) (tailX tailY : List (Fin (A + 4)))
    (hc : RpClean ι S)
    (hpR : (S.R (j .p)).length = p) (hlR : (S.R (j .l)).length = l)
    (hwR : (S.R (j .w)).length = w) (haR : (S.R (j .a)).length = a) (hbR : (S.R (j .b)).length = b)
    (hemptySetup : ∀ s ∈ setupWritten ++ setupScratch, S.R (j s) = [])
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap X) ++ tailX)
    (hsrcY : S.R srcY = cstream A w ((List.range M).flatMap Y) ++ tailY)
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      rg ι h.ι_inj hT hQ) ≤ C) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchUnaryCost p l w M a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*batchSetupCost p l w a b+3*batchPackCost M (2^l) w a+
          3*batchPackCost M (2^l) w b+(C+1)*rpWorkspace p l w M))
        depth (batchFromUnary j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  obtain ⟨vf,nf,huf,hnf,hef⟩ := batchFromUnary_prefix_exec (body := body) h hT hQ hA
    j hj hwidth hheader hoff hpriv hp hw ha hb hab X Y hlenX hlenY hX hY
    records recordSaved srcX srcY saved acc buf savedBlock tmp hpackX hpackY hoffY hdata
    v S tailX tailY hc hpR hlR hwR haR hbR hemptySetup hrecords hsrcX hsrcY hscratch hempty
  obtain ⟨n,z,ht⟩ := batchFromUnary_prefix_trace (body := body) h hT hQ hA
    j hj hwidth hheader hoff hpriv hp hw ha hb hab X Y hlenX hlenY hX hY
    records recordSaved srcX srcY saved acc buf savedBlock tmp hpackX hpackY hoffY hdata
    v S tailX tailY hc hpR hlR hwR haR hbR hemptySetup hrecords hsrcX hsrcY hscratch hempty C hpush depth
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  exact ⟨vf,nf,huf,hnf,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
