module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRawCorrelation
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRun
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardData

/-! # Execute the complete raw-line correlation and output arithmetic

Setup is retained for reuse. The executed composition changes only the final
output tape; the correlation tape returns to its original empty state.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T} {rg : TblR 10 → Fin T}

theorem chirpForwardLine_exec {shared : Bool} (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hrg : Function.Injective rg)
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, cr .out,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (hbank : ∀ i b, rg b ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hcounter : ∀ i r, cr r ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hss : ∀ i j, ι j ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    {W e s t α q w m l dimW dimWidth : ℕ} [NeZero s] [NeZero t] (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (htval : st.val 1 = t) (hmval : st.val 2 = m) (hwval : st.val 3 = w)
    (hs : 0 < s) (ht : 0 < t) (hm : 0 < m) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 3 ≤ w)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hXblank : ρ .xs = [])
    (hY : ρ .ys = chirpBlockStream (chirpBlockCount t m) (fun n => chirpEntryStream A w (3 * m + 1)
      (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) (hout : ρ .out = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hb : tblHolds rg S (tblRho W wl nl st)) (hword : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [batch, rowCount, recordSymbols, batchSaved, acc, savedSource, recordSaved,
      current, saved, buf, tmp], S.R k = [])
    (rprg : RpReg → Fin T) (rpι : Fin 91 → Fin T) (rph : RpLayout rprg rpι)
    (hT91 : 91 ≤ T) (hQrp : rpStates ≤ Q)
    (j : SetupReg → Fin T) (records recordSaved' srcY saved' acc' buf' savedBlock tmp' : Fin T)
    (ex : CorrelationReg → Fin T)
    (layout : ChirpBatchLayout j rprg rpι ex records recordSaved' dst srcY saved' acc' buf' savedBlock tmp')
    (workspace : ChirpBatchWorkspace j rprg rpι ex recordSaved' saved' acc' buf' savedBlock tmp' S)
    (hinj : Function.Injective (chirpBatchDimensions j records ex))
    (hblankDim : ∀ i, S.R (chirpBatchDimensions j records ex i) = [])
    (hsep : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp',
      ∀ i, k ≠ chirpBatchDimensions j records ex i)
    (hprivate : ∀ r : Fin 91, 4 ≤ r.val → ∀ i, rpι r ≠ chirpBatchDimensions j records ex i)
    (hXoff : ∀ i, dst ≠ chirpBatchDimensions j records ex i)
    (hYoff : ∀ i, srcY ≠ chirpBatchDimensions j records ex i)
    (houtoff : ∀ i, ex .dst ≠ chirpBatchDimensions j records ex i)
    (dimBank : TblR 10 → Fin T) (hdimBank : Function.Injective dimBank)
    (hdimOff : ∀ i r, dimBank r ≠ chirpBatchDimensions j records ex i)
    (dimWl dimNl : List (Fin (A + 4))) (hdimWl : dimWl.length = dimW)
    (hdimNl : dimNl.length = dimWidth) (hdimWidth : dimWidth ≤ dimW)
    (dimSt : TblSt 10 A) (hdimQ : dimSt.val 0 = q) (hdimT : dimSt.val 1 = t)
    (hdimM : dimSt.val 2 = m) (hdimW : dimSt.val 3 = w) (hdimL : dimSt.val 4 = l)
    (hdimPfit : q + 1 < 2 ^ dimW) (hdimAfit : 3 * m + 1 < 2 ^ dimW) (hdimBfit : 4 * m < 2 ^ dimW)
    (hdimZero : ∀ i : Fin 10, 5 ≤ i.val → dimSt.val i = 0) (hdimFit : ∀ i, dimSt.val i < 2 ^ dimW)
    (hdimHolds : tblHolds dimBank S (tblRho dimW dimWl dimNl dimSt))
    (hsrcEmpty : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp', k ≠ dst)
    (hsrcPrivate : ∀ r : Fin 91, 4 ≤ r.val → rpι r ≠ dst)
    (hsrcBank : ∀ r, dimBank r ≠ dst) (hsrcE : ∀ r, ex r ≠ dst)
    (hsrcY : S.R srcY = chirpBlockStream (chirpBlockCount t m) (fun n => chirpEntryStream A w (4 * m)
      (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a)))
    (hYdst : srcY ≠ dst) (hblank : S.R dst = []) (hst : s < t) (hl : 7 * m ≤ 2 ^ l)
    (raw : ChirpRawReg → Fin T) (hraw : Function.Injective raw)
    (hrawSep : ∀ r b, rg b ≠ raw r) (hrawDst : raw .dst = cr .xs)
    (hsval : st.val 0 = s) (htm : t + m < 2 ^ W) (hproduct : s * (t + m) < 2 ^ W)
    (hrawSrc : S.R (raw .raw) = cstream A w (chirpLine s u))
    (hrawClean : ChirpRawReady shared s t m w raw S)
    (hproducerOff : ∀ k ∈ [dst, wordR, batch, rowCount, recordSymbols, batchSaved, acc,
      savedSource, recordSaved, current, saved, buf, tmp], k ≠ cr .xs)
    (hdimXs : ∀ i, chirpBatchDimensions j records ex i ≠ cr .xs)
    (hdimBankXs : ∀ r, dimBank r ≠ cr .xs)
    (hworkspaceXs : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp', k ≠ cr .xs)
    (hprivateXs : ∀ r : Fin 91, 4 ≤ r.val → rpι r ≠ cr .xs)
    (houtputXs : ex .dst ≠ cr .xs) (hkernelXs : srcY ≠ cr .xs)
    (O : ChirpOutputLayout T) (hjoin : ex .dst = O.cr .xs) (p Γ : ℕ)
    (hpq : p ≤ q) (hwidth : q + l + Γ + 5 ≤ w)
    (hE : ∀ e ∈ chirpOutputFactors s t α q Γ m, |(e : ℝ) / 2 ^ q| ≤ 2)
    (hO : ChirpOutputState O S q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α))
    (hdimO : ∀ i, (S.R (O.dim i)).length = chirpOutputDimensionCount p q l Γ w t i)
    (hworkO : ∀ i : Fin 22, 9 ≤ i.val → S.R (O.bank i) = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpRawCorrelationModeCost shared W e dimW dimWidth s t q l m w +
        chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t ∧
      Exec body (.seq (.seq (chirpGatherFromDimensionsMode shared rg raw) (.seq
(.seq (chirpMakeXSetup rg cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
          recordSymbols acc current savedSource saved buf tmp dst)
          (.seq (.seq (chirpS1DimensionSetup dimBank (chirpBatchDimensions j records ex))
            (.seq (chirpBatchProduct j rprg rpι rph hT91 hQrp records recordSaved' dst srcY
              saved' acc' buf' savedBlock tmp' ex) (clearWords (List.ofFn (chirpBatchDimensions j records ex)))))
            (uclear dst))) (uclear (cr .xs)))) (chirpOutputRun O hT hQ)) (mk v S) n
        (mk v' { S with R := (Function.update S.R (O.nr .out)
          (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpRawCorrelation_exec (shared := shared) (body := body)
    hcr hdisj hι hT hQ hA hrg hreg hbank hcounter hss wl nl hwl hnl heW st htval hmval hwval
    hs ht hm hα hq hw hsize hvolume hzero hfit u hu ρ hr hXblank hY hxsv hysv hacc hout
    v S hc hS hb hword hclean rprg rpι rph hT91 hQrp j records recordSaved' srcY saved' acc' buf' savedBlock tmp'
    ex layout workspace hinj hblankDim hsep hprivate hXoff hYoff houtoff dimBank hdimBank hdimOff
    dimWl dimNl hdimWl hdimNl hdimWidth dimSt hdimQ hdimT hdimM hdimW hdimL hdimPfit hdimAfit hdimBfit
    hdimZero hdimFit hdimHolds hsrcEmpty hsrcPrivate hsrcBank hsrcE hsrcY hYdst hblank hst hl
    raw hraw hrawSep hrawDst hsval htm hproduct hrawSrc hrawClean hproducerOff hdimXs hdimBankXs
    hworkspaceXs hprivateXs houtputXs hkernelXs
  let rows := chirpForwardRows s t α q l m u
  let S₁ : Stacks T A := { S with R := Function.update S.R (O.cr .xs) (cstream A w rows.flatten) }
  have hblankO : S.R (O.cr .xs) = [] := by simpa [cstream] using hO.input
  have hrows : correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
      (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
      (chirpOperandY m n (chirpKernelNumerators s t α q m))) = rows.flatten :=
    (chirpCorrelationRows_flatten _ _ _).symm
  rw [hjoin, hblankO, List.append_nil, hrows] at he₁
  have hlen : rows.flatten.length = chirpBlockCount t m * m := by
    rw [← hrows]
    exact correlationStream_length _ _ (by omega) _
  have hstate := hO.supplyInput rows
  have hdim₁ (i : Fin 9) : (S₁.R (O.dim i)).length = chirpOutputDimensionCount p q l Γ w t i := by
    simpa only [S₁, ChirpOutputLayout.dim, Function.update_of_ne (O.bank_cr _ .xs)] using hdimO i
  have hwork₁ (i : Fin 22) (hi : 9 ≤ i.val) : S₁.R (O.bank i) = [] := by
    simpa only [S₁, Function.update_of_ne (O.bank_cr i .xs)] using hworkO i hi
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpOutputRun_exec (body := body) O hT hQ hA p q l Γ w t hpq hwidth
    rows (chirpOutputFactors s t α q Γ m) (chirpNormalization q α) (by rw [chirpOutputFactors_length]; omega)
    (by simpa only [chirpOutputFactors_length] using chirpForwardRows_length s t α q l m u hl)
    (by rw [hlen]; exact chirpBlockCount_mul_ge t m hm)
    (chirpGeneratedCorrelationRows_norm hst α q l _ m hα hq hl u hu) hE
    (chirpNormalization_abs_le_one q α) v₁ S₁ hstate hdim₁ hwork₁
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
  · rw [hlen] at hn₂
    exact Nat.add_le_add hn₁ hn₂
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    exact O.consumeInput S.R hblankO _ _

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
