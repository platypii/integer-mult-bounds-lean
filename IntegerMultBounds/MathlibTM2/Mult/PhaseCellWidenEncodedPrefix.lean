module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenPackedPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! Widen actual encoded output without assuming its existential coefficient
witness fits. Signed canonicalization preserves the narrow bytes exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The returned coefficients are the signed values of the original words.
Only the counted prefix changes; controls, scratch and the suffix restore. -/
theorem widenEncodedPrefix_exec {wide width count src work saved tmp extra : Fin T}
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hcount : (S.R count).length = xs.length*w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ widenPackedPrefixCost w W xs.length ∧
      Exec body (widenPackedPrefix wide width count src work saved tmp extra) (mk v S) n
        (mk v' {S with R := Function.update S.R src (cstream A W (xs.map (symZ w))++tail)}) := by
  have hfit : ∀ z ∈ xs.map (symZ w), TopFitsZ w z := by
    intro z hz
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    exact topFitsZ_symZ hw x
  obtain ⟨v',n,hu,hn,he⟩ := widenPackedPrefix_exec (body := body) hreg w W hw hwidth
    (xs.map (symZ w)) hfit tail v S hwide hword
    (by simpa only [List.length_map] using hcount)
    (by simpa only [cstream_symZ] using hsrc) hblank
  exact ⟨v',n,hu,by simpa only [List.length_map] using hn,he⟩


/-- Widening changes representation only: every active row read is identical,
even with independently borrowed suffixes in the two encodings. -/
theorem packedIntervalRead_widenEncoded {s : ℕ} (hA : 4 ≤ A)
    (q w W a : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W) (xs : List GaussianInt)
    (tail wideTail : List (Fin (A+4))) (i : ZMod s)
    (ha : a ≤ i.val) (hi : i.val < a+xs.length) :
    packedIntervalRead q W a (cstream A W (xs.map (symZ w))++wideTail) i =
      packedIntervalRead q w a (cstream A w xs++tail) i := by
  have hj : i.val-a < xs.length := by omega
  have hW : 1 ≤ W := hw.trans hwidth
  have hf := topFitsZ_symZ hw (xs[i.val-a])
  have hfW : TopFitsZ W (symZ w (xs[i.val-a])) :=
    ⟨topFits_mono hw hwidth hf.1,topFits_mono hw hwidth hf.2⟩
  unfold packedIntervalRead
  rw [cstream_word W (xs.map (symZ w)) wideTail (i.val-a) (by simpa using hj),
    cstream_word w xs tail (i.val-a) hj,List.getElem_map,
    decodeWord_csyms_symZ hA hW,decodeWord_csyms_symZ hA hw,symZ_eq hW hfW]


open IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The publication row contract transfers without a new error term. -/
theorem widenedCoreRow_accurate {s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w W width k : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (row : List GaussianInt) (hlen : row.length = coreLength s width k)
    (target : ZMod s → ℂ) (error : ℝ)
    (hgood : (∀ i ∈ ownedCore s width k,
      ‖packedIntervalRead q w (coreStart width k) (cstream A w row) i‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k) (cstream A w row)) target error) :
    (∀ i ∈ ownedCore s width k,
      ‖packedIntervalRead q W (coreStart width k) (cstream A W (row.map (symZ w))) i‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q W (coreStart width k) (cstream A W (row.map (symZ w)))) target error := by
  have he (i : ZMod s) (hi : i ∈ ownedCore s width k) :
      packedIntervalRead q W (coreStart width k) (cstream A W (row.map (symZ w))) i =
      packedIntervalRead q w (coreStart width k) (cstream A w row) i := by
    obtain ⟨ha,hb⟩ := (mem_haloVertices _ _ i).mp hi
    simpa only [List.append_nil] using packedIntervalRead_widenEncoded hA q w W
      (coreStart width k) hw hwidth row [] [] i ha (by simpa only [hlen] using hb)
  exact ⟨fun i hi => (he i hi).symm ▸ hgood.1 i hi,
    fun i hi => (he i hi).symm ▸ hgood.2 i hi⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
