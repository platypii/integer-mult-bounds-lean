module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchProgram
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchSetup

/-! # Batched short convolution with generated and cleared shared setup

Raw block streams and unary dimensions are the only data inputs. The four reusable counters
and the ring header are generated once, used by one batched product call, and cleared once.
Only the output stream changes. Binary dimension conversion belongs to the caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

/-- The four generated counters live outside the ring-product bank. -/
def setupCounters : List SetupReg := [.countX, .padX, .countY, .padY]

/-- Every shared setup, batch phase and final cleanup charge. -/
def batchUnaryCost (p l w M a b : ℕ) : ℕ :=
  batchSetupCost p l w a b + batchCost p l w M a b +
    4 * (2 ^ l * w) + 2 * (header p (2 ^ l) w).length + 11

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

noncomputable def batchFromUnary (j : SetupReg → Fin T) (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T) : Pr P T Q A U :=
  .seq (batchSetup j) <|
  .seq (batchProgram rg ι h hT hQ records recordSaved (j .countX) (j .padX) srcX
    (j .countY) (j .padY) srcY saved acc buf savedBlock tmp)
    (clearWords (setupWritten.map j))

/-- Complete shared-setup batch execution, including empty batches and zero-length raw blocks. -/
theorem batchFromUnary_prefix_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
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
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchUnaryCost p l w M a b ∧
      Exec body (batchFromUnary j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
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
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := batchProgram_prefix_exec (body := body) h hT hQ hA hp hw ha hb hab
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
  set output := cstream A w (rpStream M (fun n => coeff p l (X n) (Y n)))
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .out) (output ++ S₁.R (rg .out)) }
  have hout (s : SetupReg) (hs : s ∈ setupWritten) : j s ≠ rg .out := by
    simp only [setupWritten, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hoff .countX (by simp [setupCounters]) .out
    · exact hoff .padX (by simp [setupCounters]) .out
    · exact hoff .countY (by simp [setupCounters]) .out
    · exact hoff .padY (by simp [setupCounters]) .out
    · rw [hheader]; exact ne .d0 .out (by decide)
  have written (s : SetupReg) (hs : s ∈ setupWritten) : S₂.R (j s) = setupValue A p l w a b s := by
    simp [S₂, hout s hs, ecount s hs]
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) (setupWritten.map j)
    ((show setupWritten.Nodup by decide).map hj) v₂ S₂
  have hsum : ((setupWritten.map j).map fun k => (S₂.R k).length).sum =
      2 * (2 ^ l * w) + (header p (2 ^ l) w).length := by
    simp only [List.map_map, Function.comp_def]
    have hm : setupWritten.map (fun s => (S₂.R (j s)).length) =
        setupWritten.map (fun s => (setupValue A p l w a b s).length) := by
      apply List.map_congr_left
      intro s hs
      rw [written s hs]
    rw [hm]
    exact setup_length_sum p l w a b ha hb
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hsum]
    simp only [List.length_map, setupWritten, List.length_cons, List.length_nil] at ⊢
    unfold batchUnaryCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    change (if k ∈ setupWritten.map j then [] else S₂.R k) =
      Function.update S.R (rg .out) (output ++ S.R (rg .out)) k
    by_cases hk : k ∈ setupWritten.map j
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hk
      rw [ite_eq_left hk, Function.update_of_ne (hout s hs)]
      exact (hemptySetup s (by simp [hs])).symm
    · rw [ite_eq_right hk]
      have hframe : S₁.R k = S.R k := by
        apply setupBank_off
        intro s hs hks
        exact hk (List.mem_map.mpr ⟨s, hs, hks.symm⟩)
      simp [S₂, Function.update_apply, hframe, ering .out (by decide)]

theorem batchFromUnary_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
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
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hpR : (S.R (j .p)).length = p) (hlR : (S.R (j .l)).length = l)
    (hwR : (S.R (j .w)).length = w) (haR : (S.R (j .a)).length = a) (hbR : (S.R (j .b)).length = b)
    (hemptySetup : ∀ s ∈ setupWritten ++ setupScratch, S.R (j s) = [])
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap X))
    (hsrcY : S.R srcY = cstream A w ((List.range M).flatMap Y))
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ batchUnaryCost p l w M a b ∧
      Exec body (batchFromUnary j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (fun n => coeff p l (X n) (Y n))) ++ S.R (rg .out))) }) := by
  simpa only [List.append_nil] using
    batchFromUnary_prefix_exec h hT hQ hA j hj hwidth hheader hoff hpriv
      hp hw ha hb hab X Y hlenX hlenY hX hY
      records recordSaved srcX srcY saved acc buf savedBlock tmp hpackX hpackY hoffY hdata
      v S [] [] hc hpR hlR hwR haR hbR hemptySetup hrecords
      (by simpa using hsrcX) (by simpa using hsrcY) hscratch hempty

/-- All setup and cleanup charges are independent of the number of records. -/
theorem batchUnaryCost_le (p l w M a b : ℕ) (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) :
    batchUnaryCost p l w M a b ≤
      M * (rpRecBound p l w + 44 * (2 ^ l * w) + 50) + rpFixCost p l w +
      batchSetupCost p l w a b + 4 * (2 ^ l * w) + 2 * (header p (2 ^ l) w).length + 31 := by
  have := batchCost_le p l w M a b ha hb
  unfold batchUnaryCost
  omega

/-- A fully expanded bound: one fixed product charge and one linear setup/cleanup charge
for the whole batch. -/
theorem batchUnaryCost_le_linear (p l w M a b : ℕ) (hw : 1 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) :
    batchUnaryCost p l w M a b ≤
      M * (rpRecBound p l w + 44 * (2 ^ l * w) + 50) + rpFixCost p l w +
      46 * (2 ^ l * w) + 8 * w + 18 * l + ldrHeaderCost p l w +
      2 * (header p (2 ^ l) w).length + 63 := by
  have hbatch := batchUnaryCost_le p l w M a b ha hb
  have hsetup := batchSetupCost_le p l w a b hw ha hb
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
