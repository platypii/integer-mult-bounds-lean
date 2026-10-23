module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchUnary
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchUnary

/-! # One shared product call for all chirp correlation blocks

Pack both raw operand batches, invoke S1 once, generate shared extraction counters,
select all correlations in output order, then clear the temporary full product.
Every setup and cleanup charge outside the per-record term is paid once.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

/-- Roles of the shared extraction phase; these may reuse restored S1 workspace. -/
inductive CorrelationReg
  | l | triples | dst | batch | batchSaved | skip | savedSkip | m | recordSaved | w
  | recordSymbols | src | acc | current | savedSource | saved | buf | tmp
  deriving DecidableEq

def correlationRoles : List CorrelationReg :=
  [.l, .triples, .dst, .batch, .batchSaved, .skip, .savedSkip, .m, .recordSaved, .w,
    .recordSymbols, .src, .acc, .current, .savedSource, .saved, .buf, .tmp]

theorem correlationRoles_nodup : correlationRoles.Nodup := by decide +kernel

theorem correlationRegisters_nodup {T : ℕ} (e : CorrelationReg → Fin T) (he : Function.Injective e) :
    [e .l, e .triples, e .dst, e .batch, e .batchSaved, e .skip, e .savedSkip, e .m,
      e .recordSaved, e .w, e .recordSymbols, e .src, e .acc, e .current, e .savedSource,
      e .saved, e .buf, e .tmp].Nodup :=
  correlationRoles_nodup.map he

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

/-- The shared pipeline contains one syntactic S1 batch call. -/
noncomputable def chirpBatchProduct (j : SetupReg → Fin T) (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (e : CorrelationReg → Fin T) : Pr P T Q A U :=
  .seq (batchFromUnary j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp)
    (.seq (correlationBatchFromUnary (e .l) (e .triples) (e .dst) (e .batch) (e .batchSaved)
      (e .skip) (e .savedSkip) (e .m) (e .recordSaved) (e .w) (e .recordSymbols) (e .src)
      (e .acc) (e .current) (e .savedSource) (e .saved) (e .buf) (e .tmp)) (uclear (rg .out)))

def chirpBatchProductCost (p l w m M : ℕ) : ℕ :=
  batchUnaryCost p l w M (3 * m + 1) (4 * m) + correlationBatchUnaryCost l w m M +
    2 * (M * 2 ^ l * w) + 2

/-- Complete raw-batch execution with generated parameters and only the destination changed. -/
theorem chirpBatchProduct_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    (j : SetupReg → Fin T) (hj : Function.Injective j)
    (hwidth : j .w = rg .wn) (hheader : j .header = rg .d0)
    (hoff : ∀ s ∈ setupCounters, ∀ r, j s ≠ rg r)
    (hpriv : ∀ s ∈ setupCounters, ∀ k, j s ≠ ι k)
    {p l w M m : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = 3 * m + 1) (hlenY : ∀ n < M, (Y n).length = 4 * m)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (hpackX : [records, recordSaved, j .countX, j .padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup)
    (hpackY : [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup)
    (hoffY : ∀ k ∈ [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs)
    (hdata : ∀ k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp],
      ∀ s ∈ setupWritten, k ≠ j s)
    (e : CorrelationReg → Fin T) (he : Function.Injective e)
    (el : e .l = j .l) (ew : e .w = j .w) (eb : e .batch = records) (es : e .src = rg .out)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hpR : (S.R (j .p)).length = p) (hlR : (S.R (j .l)).length = l)
    (hwR : (S.R (j .w)).length = w)
    (haR : (S.R (j .a)).length = 3 * m + 1) (hbR : (S.R (j .b)).length = 4 * m)
    (hemptySetup : ∀ s ∈ setupWritten ++ setupScratch, S.R (j s) = [])
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap X))
    (hsrcY : S.R srcY = cstream A w ((List.range M).flatMap Y))
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (hmR : (S.R (e .m)).length = m) (hout : S.R (rg .out) = [])
    (howned : ∀ r ∈ [CorrelationReg.triples, .skip, .recordSymbols], S.R (e r) = [])
    (hclean : ∀ r ∈ [CorrelationReg.batchSaved, .acc, .savedSource, .savedSkip, .recordSaved,
      .current, .saved, .buf, .tmp], S.R (e r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpBatchProductCost p l w m M ∧
      Exec body (chirpBatchProduct j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp e)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R (e .dst)
          (cstream A w (correlationStream M m (fun n => coeff p l (X n) (Y n))) ++ S.R (e .dst))) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := batchFromUnary_exec (body := body) h hT hQ hA j hj hwidth hheader
    hoff hpriv hp hw (by omega) (by omega) (by omega) X Y hlenX hlenY hX hY records recordSaved
    srcX srcY saved acc buf savedBlock tmp hpackX hpackY hoffY hdata v S hc hpR hlR hwR haR hbR
    hemptySetup hrecords hsrcX hsrcY hscratch hempty
  let Z := fun n => coeff p l (X n) (Y n)
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg .out) (cstream A w (rpStream M Z)) }
  rw [hout, List.append_nil] at he₁
  have off (r : CorrelationReg) (hr : r ≠ .src) : S₁.R (e r) = S.R (e r) := by
    simp only [S₁, ← es, Function.update_of_ne (he.ne hr)]
  have owned₁ : ∀ k ∈ [e .triples, e .skip, e .recordSymbols], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> rw [off _ (by decide)] <;> exact howned _ (by simp)
  have clean₁ : ∀ k ∈ [e .batchSaved, e .acc, e .savedSource, e .savedSkip, e .recordSaved,
      e .current, e .saved, e .buf, e .tmp], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [off _ (by decide)] <;> exact hclean _ (by simp)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := correlationBatchFromUnary_exec (body := body)
    (correlationRegisters_nodup e he) l w m M (by omega) Z v₁ S₁ []
    (by rw [off _ (by decide), el]; exact hlR)
    (by rw [off _ (by decide), ew]; exact hwR)
    (by rw [off _ (by decide)]; exact hmR)
    (by rw [off _ (by decide), eb]; exact hrecords)
    (by simp only [S₁, es, Function.update_self, List.append_nil]) owned₁ clean₁
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R (e .dst)
    (cstream A w (correlationStream M m Z) ++ S₁.R (e .dst))) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (rg .out) v₂ S₂
  have hds : e .dst ≠ rg .out := by rw [← es]; exact he.ne (by decide)
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hlen : (S₂.R (rg .out)).length = M * 2 ^ l * w := by
      simp only [S₂, S₁, Function.update_of_ne hds.symm, Function.update_self,
        length_cstream, length_rpStream]
    rw [hlen]
    unfold chirpBatchProductCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hs : k = rg .out
    · subst k
      simp only [S₂, S₁, Function.update_self, Function.update_of_ne hds.symm, hout]
    by_cases hd : k = e .dst
    · subst k
      simp only [S₂, S₁, Function.update_self, Function.update_of_ne hds, Z]
    · simp only [S₂, S₁, Function.update_of_ne hs, Function.update_of_ne hd]

/-- One fixed product charge and one setup/cleanup charge for the entire batch. -/
theorem chirpBatchProductCost_le (p l w m M : ℕ) (hw : 1 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l) :
    chirpBatchProductCost p l w m M ≤
      M * (rpRecBound p l w + 52 * (2 ^ l * w) + 38 * m * w + 19 * m + 73) +
        rpFixCost p l w + 52 * (2 ^ l * w) + 18 * m * w + 37 * m + 12 * w + 27 * l +
        ldrHeaderCost p l w + 2 * (header p (2 ^ l) w).length + 100 := by
  have h := batchUnaryCost_le_linear p l w M (3 * m + 1) (4 * m) hw (by omega) (by omega)
  unfold chirpBatchProductCost
  calc
    _ ≤ (M * (rpRecBound p l w + 44 * (2 ^ l * w) + 50) + rpFixCost p l w +
      46 * (2 ^ l * w) + 8 * w + 18 * l + ldrHeaderCost p l w +
      2 * (header p (2 ^ l) w).length + 63) + correlationBatchUnaryCost l w m M +
        2 * (M * 2 ^ l * w) + 2 := by omega
    _ = _ := by unfold correlationBatchUnaryCost; ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
