module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexHaloScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Publish encoded solver rows using their own packed-reader certificates.
The byte-level scatter premise follows structurally from row alignment. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Concatenation preserves every word of a fixed-width row, including with an
arbitrary borrowed suffix. No coefficient fit or decoding premise is needed. -/
theorem cstream_rows_word {A : ℕ} (w L : ℕ) (rows : List (List GaussianInt))
    (hrows : ∀ row ∈ rows, row.length = L) (tail : List (Fin (A+4)))
    (n i : ℕ) (hn : n < rows.length) (hi : i < L) :
    ((cstream A w rows.flatten++tail).drop ((n*L+i)*w)).take w =
      ((cstream A w rows[n]).drop (i*w)).take w := by
  have hflat := length_flatten_const rows hrows
  have hidx : n*L+i < rows.flatten.length := by
    rw [hflat]
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hn)
    nlinarith
  have hrow : i < rows[n].length := by rw [hrows _ (List.getElem_mem hn)]; exact hi
  rw [cstream_word w _ tail _ hidx]
  have he := getElem_flatMap_len id L rows (fun row hr => hrows row hr) n i hn hi
    (by simpa only [List.flatMap_id,Nat.mul_comm L n] using hidx)
  simp only [List.flatMap_id,id_eq,Nat.mul_comm L n] at he
  rw [he]
  simpa only [List.append_nil] using (cstream_word (A := A) w rows[n] [] i hrow).symm

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem encodedHaloPublication_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (t band a b L q w : ℕ) (hst : s < t) (hw1 : 1 ≤ w)
    (rows : List (List GaussianInt))
    (hlen : rows.length = (haloLengthGroup s t band a b L).length)
    (hrows : ∀ row ∈ rows, row.length = L)
    (E sourceTail outputTail : List (Fin (A+4))) (hE : E.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (haloScatterGaps s t band a b L w))
    (hdst : S.R dst = E++outputTail) (hsrc : S.R src = cstream A w rows.flatten++sourceTail)
    (hw : (S.R window).length = L*w)
    (hclean : ∀ k ∈ [savedControl,gap,acc,trash,tmp], S.R k = [])
    (x : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ n : Fin (haloLengthGroup s t band a b L).length,
      PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
        (packedIntervalRead q w (haloGroupOrigin s t band a b L n).val
          (cstream A w (rows[n.val]'(by omega)))) x error) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 35*s*w+6 ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail)
          dst (scatterRows (L*w) E (cstream A w rows.flatten++sourceTail)
            (haloScatterGaps s t band a b L w)++outputTail))}) ∧
      ∀ k : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L k) L)
          (pairedCellRead q w (scatterRows (L*w) E (cstream A w rows.flatten++sourceTail)
            (haloScatterGaps s t band a b L w)++outputTail)) x error := by
  apply haloScatter_complex_accuracy_exec (body := body) hreg t band a b L q w hst hw1 E
    (cstream A w rows.flatten) sourceTail outputTail hE
    (by rw [length_cstream,length_flatten_const rows hrows,hlen,Nat.mul_assoc])
    v S hc hdst hsrc hw hclean x error
  intro n i
  rw [cstream_rows_word w L rows hrows sourceTail n.val i.val (by omega) i.isLt]
  let lo := haloGroupOrigin s t band a b L n
  have hfit : lo.val+L ≤ s := by
    dsimp only [lo]
    rw [haloGroupOrigin_val band a b L n]
    exact haloOrigins_fit s t band a b L _ (List.mem_map.mpr
      ⟨_,haloGroupPhase_mem s t band a b L n,rfl⟩)
  have hi : i.val < s := by omega
  have hval : (lo+(i.val : ZMod s)).val = lo.val+i.val := by
    rw [ZMod.val_add,ZMod.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by omega)]
  have he := hgood n (lo+(i.val : ZMod s))
    (Finset.mem_image.mpr ⟨i.val,Finset.mem_range.mpr i.isLt,rfl⟩)
  dsimp only [lo] at hval he
  simpa only [packedIntervalRead,hval,Nat.add_sub_cancel_left] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
