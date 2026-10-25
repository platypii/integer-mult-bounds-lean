module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGeneratedBatchCorrect

/-! # Shared correlation execution with installed and erased S1 dimensions

The dedicated binary input bank supplies all seven unary caller dimensions. The
prepared operand streams are retained, and only the correlation destination changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

def chirpDimensionBatchCost (W width q t m w l : ℕ) : ℕ :=
  let K := (q + 1) + l + w + (3 * m + 1) + 4 * m + chirpBlockCount t m + m
  18 * tblC W width + 6 * K + 77 * W + 43 +
    chirpBatchProductCost (q + 1) l w m (chirpBlockCount t m) + 2 * K + 15

/-- Install all unary dimensions, execute S1 once, extract and erase installed dimensions. -/
theorem chirpDimensionBatch_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    (j : SetupReg → Fin T) (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (e : CorrelationReg → Fin T)
    (layout : ChirpBatchLayout j rg ι e records recordSaved srcX srcY saved acc buf savedBlock tmp)
    {s t α q l w m W width : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 1 + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (v : HS T Q A U) (S : Stacks T A)
    (workspace : ChirpBatchWorkspace j rg ι e recordSaved saved acc buf savedBlock tmp S)
    (hinj : Function.Injective (chirpBatchDimensions j records e))
    (hblank : ∀ i, S.R (chirpBatchDimensions j records e i) = [])
    (hsep : ∀ k ∈ chirpBatchEmpty j rg e recordSaved saved acc buf savedBlock tmp,
      ∀ i, k ≠ chirpBatchDimensions j records e i)
    (hprivate : ∀ r : Fin 91, 4 ≤ r.val → ∀ i, ι r ≠ chirpBatchDimensions j records e i)
    (hXoff : ∀ i, srcX ≠ chirpBatchDimensions j records e i)
    (hYoff : ∀ i, srcY ≠ chirpBatchDimensions j records e i)
    (houtoff : ∀ i, e .dst ≠ chirpBatchDimensions j records e i)
    (bank : TblR 10 → Fin T) (hbank : Function.Injective bank)
    (hbankoff : ∀ i r, bank r ≠ chirpBatchDimensions j records e i)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = width)
    (hwidth : width ≤ W) (st : TblSt 10 A)
    (hqval : st.val 0 = q) (htval : st.val 1 = t) (hmval : st.val 2 = m)
    (hwval : st.val 3 = w) (hlval : st.val 4 = l)
    (hpfit : q + 1 < 2 ^ W) (hafit : 3 * m + 1 < 2 ^ W) (hbfit : 4 * m < 2 ^ W)
    (hzero : ∀ i : Fin 10, 5 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (hholds : tblHolds bank S (tblRho W wl nl st))
    (hsrcX : S.R srcX = cstream A w ((List.range (chirpBlockCount t m)).flatMap fun n =>
      chirpOperandX s t q m n (chirpInputNumerators s t α q m) u))
    (hsrcY : S.R srcY = chirpBlockStream (chirpBlockCount t m) (fun n => chirpEntryStream A w (4 * m)
      (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a))) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpDimensionBatchCost W width q t m w l ∧
      Exec body
        (.seq (chirpS1DimensionSetup bank (chirpBatchDimensions j records e))
          (.seq (chirpBatchProduct j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp e)
            (clearWords (List.ofFn (chirpBatchDimensions j records e)))))
        (mk v S) n
        (mk v' { S with R := (Function.update S.R (e .dst)
          (cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
            (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
            (chirpOperandY m n (chirpKernelNumerators s t α q m)))) ++ S.R (e .dst))) }) := by
  let dims := chirpBatchDimensions j records e
  let σ := chirpS1DimensionValues q t m w l
  let words := cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
    (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
    (chirpOperandY m n (chirpKernelNumerators s t α q m))))
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpS1DimensionSetup_exec (body := body) hbank dims
    hbankoff wl nl hwl hnl hwidth st q t m w l hqval htval hmval hwval hlval
    (NeZero.pos t) hm hpfit hafit hbfit hzero hfit v S hholds
  let S₁ : Stacks T A := { S with R := unaryCopiesR σ S.R (chirpS1Assignments dims) }
  have state := workspace.install (q := q) (t := t) (m := m) (w := w) (l := l) hinj hblank hsep hprivate
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, herr⟩ := chirpGeneratedBatch_correct (body := body)
    h hT hQ hA j records recordSaved srcX srcY saved acc buf savedBlock tmp e layout
    hst hα hq hw hm hl u hu v₁ S₁ state
    (by simpa only [S₁, σ, chirpS1Dimensions_off dims q t m w l S.R srcX hXoff] using hsrcX)
    (by simpa only [S₁, σ, chirpS1Dimensions_off dims q t m w l S.R srcY hYoff] using hsrcY)
  subst S₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (e .dst) (words ++ S₁.R (e .dst)) }
  have hat (i : Fin 7) : S₂.R (dims i) = List.replicate (chirpS1DimensionCount q t m w l i) tick := by
    change Function.update S₁.R (e .dst) _ (dims i) = _
    rw [Function.update_of_ne (houtoff i).symm]
    simpa only [S₁, σ, dims, hblank, List.append_nil] using
      chirpS1Dimensions_at (chirpBatchDimensions j records e) hinj q t m w l S.R i
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) (List.ofFn dims)
    (List.nodup_ofFn_ofInjective hinj) v₂ S₂
  have hsum : ((List.ofFn dims).map fun k => (S₂.R k).length).sum =
      (q + 1) + l + w + (3 * m + 1) + 4 * m + chirpBlockCount t m + m := by
    simp only [List.map_ofFn, Function.comp_def, hat, List.length_replicate]
    simp [List.ofFn_succ, chirpS1DimensionCount, Nat.add_assoc]
  rw [chirpS1Dimensions_cost] at hn₁
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hsum, List.length_ofFn]
    dsimp only [chirpDimensionBatchCost]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ herr
    funext k
    by_cases hk : k ∈ List.ofFn dims
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      simp only [ite_eq_left hk]
      rw [Function.update_of_ne (show dims i ≠ e .dst from (houtoff i).symm)]
      exact (hblank i).symm
    · have hoff : ∀ i, k ≠ dims i := by
        intro i hi
        exact hk (List.mem_ofFn.mpr ⟨i, hi.symm⟩)
      have hd : S₁.R (e .dst) = S.R (e .dst) := chirpS1Dimensions_off dims q t m w l S.R _ houtoff
      simp only [ite_eq_right hk, S₂, hd]
      by_cases ho : k = e .dst
      · subst k; simp only [Function.update_self]; rfl
      · simp only [Function.update_of_ne ho]
        exact chirpS1Dimensions_off dims q t m w l S.R k hoff

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
