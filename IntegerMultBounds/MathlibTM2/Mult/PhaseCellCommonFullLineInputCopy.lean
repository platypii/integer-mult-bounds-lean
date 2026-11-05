module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCopyNarrowPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalInverseInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallInverseHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAffineHeader

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

theorem inverseFullInputWidth_eq_master (p u l target t : ℕ) :
    inverseFullInputWidth p u l target s t = 2*inverseMasterValues p u l target s t 0 s 2+8 := by
  change 8*executionExponent p l _ 2+8 =
    2*(4*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) 0 s).card (PhaseCellBand.width p u))+8
  rw [inverseExecutionExponent_eq]
  omega

/-- Derive the canonical RHS width from the precision master already produced
by the inverse setup. No numerical width oracle is needed. -/
theorem fullLineInputWidth_exec (body : P → Pr P T Q A U)
    (master width tmp : Fin T) (hreg : [master,width,tmp].Nodup)
    (p u l target t : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hmaster : (S.R master).length = inverseMasterValues p u l target s t 0 s 2)
    (hwidth : S.R width = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (affineHeader 2 8 master width tmp) (mk v S) (4*(S.R master).length+5)
        (mk v' {S with R := (Function.update S.R width
          (List.replicate (inverseFullInputWidth p u l target s t) tick))}) := by
  obtain ⟨v',hu,he⟩ := affineHeader_exec body 2 8 master width tmp hreg v S hwidth htmp
  rw [hmaster,← inverseFullInputWidth_eq_master] at he
  exact ⟨v',hu,by simpa only [hmaster] using he⟩

theorem inverseFullInputWidth_le_common (p u l target t : ℕ) :
    inverseFullInputWidth p u l target s t ≤ packedHaloCommonWidth p l s u (target+1) 2 := by
  have h := packedHaloCommonWidth_fits p l s t u (target+1) 2 0 s
  simp only [packedHaloPrecision,boundaryHaloTarget,Nat.add_sub_cancel] at h
  dsimp only [inverseFullInputWidth,executionWidth,executionPrecision] at h ⊢
  omega

/-- Isolate the exact canonical RHS expected by the full-line dispatcher from
the retained common-width stream used by proper publication. The borrowed
suffix is never traversed. Control generation is a separate paid stage. -/
theorem commonFullLineInputCopy_exec (body : P → Pr P T Q A U)
    (count src dst saved tmp wide width work zero extra : Fin T)
    (hreg : [count,src,dst,saved,tmp,wide,width,work,zero,extra].Nodup)
    (p u l target t : ℕ) (Fs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A (packedHaloCommonWidth p l s u (target+1) 2)
      (Fs.map (chirpLine s)).flatten++tail)
    (hcount : (S.R count).length = Fs.length*s*packedHaloCommonWidth p l s u (target+1) 2)
    (hwide : (S.R wide).length = packedHaloCommonWidth p l s u (target+1) 2)
    (hwidth : (S.R width).length = inverseFullInputWidth p u l target s t)
    (hdst : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hwork : S.R work = []) (hzero : S.R zero = []) (hextra : S.R extra = []) (depth : ℕ) :
    let cost := copyNarrowPrefixCost (packedHaloCommonWidth p l s u (target+1) 2)
      (inverseFullInputWidth p u l target s t) (Fs.length*s)
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost) depth
        (copyNarrowPrefix count src dst saved tmp wide width work zero extra) (mk v S) cost
        (mk v' {S with R := (Function.update S.R dst
          (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}) := by
  have hlen : (Fs.map (chirpLine s)).flatten.length = Fs.length*s := by
    simp only [List.length_flatten,List.map_map,Function.comp_def,length_chirpLine,
      List.map_const',List.sum_replicate,smul_eq_mul]
  have hpositive : 1 ≤ packedHaloCommonWidth p l s u (target+1) 2 := by
    dsimp only [packedHaloCommonWidth,executionWidth]
    omega
  have he := copyNarrowPrefix_exec_within body count src dst saved tmp wide width work zero extra hreg
    (packedHaloCommonWidth p l s u (target+1) 2) (inverseFullInputWidth p u l target s t)
    hpositive (inverseFullInputWidth_le_common p u l target t) (Fs.map (chirpLine s)).flatten tail v S hsrc
    (by simpa only [hlen] using hcount) hwide hwidth hdst hsaved htmp hwork hzero hextra depth
  simpa only [hlen] using he

/-- The common caller supplies replica and line counts, rather than an
externally prepared encoded-length counter. Both generated counters retire. -/
theorem generatedCommonFullLineInputCopy_exec (body : P → Pr P T Q A U)
    (cells rowCount wide rows count src dst saved tmp width work zero extra : Fin T)
    (hreg : [cells,rowCount,wide,rows,count,src,dst,saved,tmp,width,work,zero,extra].Nodup)
    (p u l target t : ℕ) (Fs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R cells).length = Fs.length) (hs : (S.R rowCount).length = s)
    (hwide : (S.R wide).length = packedHaloCommonWidth p l s u (target+1) 2)
    (hwidth : (S.R width).length = inverseFullInputWidth p u l target s t)
    (hsrc : S.R src = cstream A (packedHaloCommonWidth p l s u (target+1) 2)
      (Fs.map (chirpLine s)).flatten++tail)
    (hfresh : ∀ k ∈ [rows,count,dst,saved,tmp,work,zero,extra], S.R k = []) (depth : ℕ) :
    let cost := generatedCopyNarrowPrefixCost Fs.length s
      (packedHaloCommonWidth p l s u (target+1) 2) (inverseFullInputWidth p u l target s t)
    ∃ v' n, v'.user = v.user ∧ n ≤ cost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost) depth
        (generatedCopyNarrowPrefix cells rowCount wide rows count src dst saved tmp width work zero extra)
        (mk v S) n (mk v' {S with R := (Function.update S.R dst
          (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}) := by
  have hlen : (Fs.map (chirpLine s)).flatten.length = Fs.length*s := by
    simp only [List.length_flatten,List.map_map,Function.comp_def,length_chirpLine,
      List.map_const',List.sum_replicate,smul_eq_mul]
  have hpositive : 1 ≤ packedHaloCommonWidth p l s u (target+1) 2 := by
    dsimp only [packedHaloCommonWidth,executionWidth]
    omega
  obtain ⟨v',n,hu,hn,he⟩ := generatedCopyNarrowPrefix_exec (body := body)
    cells rowCount wide rows count src dst saved tmp width work zero extra hreg Fs.length s
    (packedHaloCommonWidth p l s u (target+1) 2) (inverseFullInputWidth p u l target s t)
    hpositive (inverseFullInputWidth_le_common p u l target t) (Fs.map (chirpLine s)).flatten hlen
    tail v S hN hs hwide hwidth hsrc hfresh
  exact ⟨v',n,hu,hn,generatedCopyNarrowPrefix_within he hn depth⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
