module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpStreamCorrelation
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherFromDimensions

/-! # Raw-line chirp correlation through one shared S1 call

Gather windows from the retained raw line, execute generated operand production and
shared correlation, then erase the gathered window stream. Only the destination changes.
The generated G/K tables and binary/template banks are retained caller inputs.
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

def chirpRawCorrelationCost (W e dimW dimWidth s t q l m w : ℕ) : ℕ :=
  chirpGatherFromDimensionsCost W e s t m w +
    chirpStreamCorrelationCost W e dimW dimWidth t q l m w +
    2 * (chirpBlockCount t m * (3 * m + 1) * w) + 2

/-- Execute the raw-line-to-correlation pipeline with complete intermediate cleanup. -/
theorem chirpRawCorrelation_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
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
    (hrawClean : ∀ r, r ≠ .raw → r ≠ .dst → S.R (raw r) = [])
    (hproducerOff : ∀ k ∈ [dst, wordR, batch, rowCount, recordSymbols, batchSaved, acc,
      savedSource, recordSaved, current, saved, buf, tmp], k ≠ cr .xs)
    (hdimXs : ∀ i, chirpBatchDimensions j records ex i ≠ cr .xs)
    (hdimBankXs : ∀ r, dimBank r ≠ cr .xs)
    (hworkspaceXs : ∀ k ∈ chirpBatchEmpty j rprg ex recordSaved' saved' acc' buf' savedBlock tmp', k ≠ cr .xs)
    (hprivateXs : ∀ r : Fin 91, 4 ≤ r.val → rpι r ≠ cr .xs)
    (houtputXs : ex .dst ≠ cr .xs) (hkernelXs : srcY ≠ cr .xs) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpRawCorrelationCost W e dimW dimWidth s t q l m w ∧
      Exec body (.seq (chirpGatherFromDimensions rg raw) (.seq
(.seq (chirpMakeXSetup rg cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
          recordSymbols acc current savedSource saved buf tmp dst)
          (.seq (.seq (chirpS1DimensionSetup dimBank (chirpBatchDimensions j records ex))
            (.seq (chirpBatchProduct j rprg rpι rph hT91 hQrp records recordSaved' dst srcY
              saved' acc' buf' savedBlock tmp' ex) (clearWords (List.ofFn (chirpBatchDimensions j records ex)))))
            (uclear dst))) (uclear (cr .xs))))
        (mk v S) n (mk v' { S with R := (Function.update S.R (ex .dst)
          (cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
            (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
            (chirpOperandY m n (chirpKernelNumerators s t α q m)))) ++ S.R (ex .dst))) }) := by
  let windows := cstream A w ((List.range (chirpBlockCount t m)).flatMap fun n => chirpWindow s t m n u)
  let output := cstream A w (correlationStream (chirpBlockCount t m) m (fun n => coeff (q + 1) l
    (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
    (chirpOperandY m n (chirpKernelNumerators s t α q m))))
  have hx0 : S.R (cr .xs) = [] := (hS .xs).trans hXblank
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpGatherFromDimensions_exec (body := body) hrg hraw hrawSep
    wl nl hwl hnl heW st s t m w hsval htval hmval hwval hs hst.le ht hm hsize hvolume
    htm hproduct hzero hfit u v S hb hrawSrc hrawClean
  let S₁ : Stacks T A := { S with R := Function.update S.R (cr .xs) windows }
  have hflat : ((List.range (chirpBlockCount t m)).flatMap fun n => cstream A w (chirpWindow s t m n u)) = windows :=
    (cstream_flatMap_rows _ _).symm
  rw [hrawDst, hx0, List.append_nil, hflat] at he₁
  have off (k : Fin T) (hk : k ≠ cr .xs) : S₁.R k = S.R k := by simp [S₁, hk]
  let ρ₁ := Function.update ρ CR.xs windows
  have hS₁ : CHolds cr S₁ ρ₁ := holds_upd hcr hS .xs windows
  have hc₁ : CClean ι S₁ := fun r => ⟨(hc r).1, (off _ (hdisj .xs r).symm).trans (hc r).2⟩
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := by
    intro r
    rw [off _ (by simpa only [hrawDst] using hrawSep .dst r)]
    exact hb r
  have bank₁ : tblHolds dimBank S₁ (tblRho dimW dimWl dimNl dimSt) := by
    intro r
    rw [off _ (hdimBankXs r)]
    exact hdimHolds r
  have workspace₁ : ChirpBatchWorkspace j rprg rpι ex recordSaved' saved' acc' buf' savedBlock tmp' S₁ :=
    workspace.update_operand (cr .xs) windows hworkspaceXs hprivateXs
  have hrowfit : 3 * m + 1 < 2 ^ W := lt_of_le_of_lt (by omega) hsize
  have hrowvolume : (3 * m + 1) * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (by omega : 3 * m + 1 ≤ s + 3 * m + 1)).trans_lt hvolume
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpStreamCorrelation_exec (body := body)
    hcr hdisj hι hT hQ hA hrg hreg hbank hcounter hss wl nl hwl hnl heW st htval hmval hwval
    hs ht hm hα hq hw hrowfit hrowvolume hzero hfit u hu ρ₁ (hr.update .xs (by simp) windows)
    (by simp [ρ₁]; rfl) (by simpa [ρ₁] using hY)
    (by simpa [ρ₁] using hxsv) (by simpa [ρ₁] using hysv)
    (by simpa [ρ₁] using hacc) (by simpa [ρ₁] using hout)
    v₁ S₁ hc₁ hS₁ hb₁
    (by rw [off _ (hproducerOff wordR (by simp))]; exact hword)
    (by
      intro k hk
      rw [off _ (hproducerOff k (List.mem_append_right [dst, wordR] hk))]
      exact hclean k hk)
    rprg rpι rph hT91 hQrp j records recordSaved' srcY saved' acc' buf' savedBlock tmp' ex layout
    workspace₁ hinj (fun i => (off _ (hdimXs i)).trans (hblankDim i)) hsep hprivate hXoff hYoff houtoff
    dimBank hdimBank hdimOff dimWl dimNl hdimWl hdimNl hdimWidth dimSt hdimQ hdimT hdimM hdimW hdimL
    hdimPfit hdimAfit hdimBfit hdimZero hdimFit bank₁ hsrcEmpty hsrcPrivate hsrcBank hsrcE
    ((off _ hkernelXs).trans hsrcY) hYdst ((off _ (hproducerOff dst (by simp))).trans hblank) hst hl
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (ex .dst) (output ++ S₁.R (ex .dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (cr .xs) v₂ S₂
  have hwindowLen : windows.length = chirpBlockCount t m * (3 * m + 1) * w := by
    rw [length_cstream]
    have hlen := length_flatten_const ((List.range (chirpBlockCount t m)).map fun n => chirpWindow s t m n u)
      (L := 3 * m + 1) (by
        intro xs hx
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
        exact length_chirpWindow hs (chirpBlock_valid ht hm (List.mem_range.mp hn)) u)
    simpa [Function.comp_def] using congrArg (fun n => n * w) hlen
  have htemp : S₂.R (cr .xs) = windows := by
    simp only [S₂, S₁, Function.update_of_ne houtputXs.symm, Function.update_self]
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [htemp, hwindowLen]
    unfold chirpRawCorrelationCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃
    funext k
    by_cases hx : k = cr .xs
    · subst k
      simp [S₂, S₁, houtputXs.symm, hx0]
    · by_cases ho : k = ex .dst
      · subst k
        simp [S₂, S₁, houtputXs, output]
      · simp [S₂, S₁, hx, ho]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
