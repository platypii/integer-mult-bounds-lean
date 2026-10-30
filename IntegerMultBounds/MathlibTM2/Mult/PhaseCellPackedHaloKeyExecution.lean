module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryFrame

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedBounds

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! One keyed publication restores the loop invariant and preserves all accuracy
contracts already established on the shared packed output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedHaloKeyCost (p l s t u target rhsExp a b V L : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let band := PhaseCellBand.width p u
  let offsets := haloPackedOffsets s t band a b L
  (2*s+2*V+6*L+17*V+16)+
    installGroupHeadersCost (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u band L+
    binaryHaloClassCost V s t band a b L+
    ((if offsets = [] then 2*((2^15*p)+(executionStagePrecision p l target rhsExp+1)+q+l+s+t+u+band+2*L)+21
      else reusablePackedCellBatchPublishCost p l target rhsExp V (b-a) L offsets.length s t u)+2)

theorem packedHaloReady_publish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hkey : L < 2^V) (hwide : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail suffix E outputTail : List (Fin (A+4))) (done : List ℕ)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
      (executionWidth p l target rhsExp)
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E outputTail S)
    (hkeys : S.R 126 = binSyms V L++suffix)
    (hold : ∀ M ∈ done, PackedCellOutputSpec t p u l target rhsExp M
      (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
      (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
      (fun _ => C) (S.R 132)) :
    ∃ v' F m E', v'.user = v.user ∧
      m ≤ packedHaloKeyCost p l s t u target rhsExp a b V L ∧
      Exec body (keyedPackedHaloPublish hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
        (executionWidth p l target rhsExp)
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E' outputTail F ∧
      F.R 126 = suffix ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 126 → k ≠ 128 → k ≠ 157 → k ≠ 132 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ M ∈ L::done, PackedCellOutputSpec t p u l target rhsExp M
        (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
        (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
        (fun _ => C) (F.R 132)) ∧
      (EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
        (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
          (interiorOutputExponent p l target rhsExp) E') ∧
      PackedHaloWordFrame s t (PhaseCellBand.width p u) a b (executionWidth p l target rhsExp)
        (S.R 132) (F.R 132) ∧ F.L = S.L ∧ (F.R 128).length = L := by
  have hsource : S.R 110 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail := by
    simpa [embStk,packedCellCoreReg,releasedCellBank] using
      congrArg (fun B : Stacks 117 A => B.R 110) hready.native
  have hleft : ∀ k : Fin 168, k.val < 117 → S.L k = [] := by
    intro k hk
    let i : Fin 117 := ⟨k.val,hk⟩
    simpa [embStk,packedCellCoreReg,releasedCellBank,i] using
      congrArg (fun B : Stacks 117 A => B.L i) hready.native
  have hblank : ∀ k : Fin 168, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [] := by
    intro k hk h93 h110
    let i : Fin 117 := ⟨k.val,hk⟩
    have h93' : k.val ≠ 93 := fun he => h93 (Fin.ext he)
    have h110' : k.val ≠ 110 := fun he => h110 (Fin.ext he)
    simpa [embStk,packedCellCoreReg,releasedCellBank,i,h93',h110'] using
      congrArg (fun B : Stacks 117 A => B.R i) hready.native
  obtain ⟨v',F,m,hu',hm,he,h93,h140,houtput,hproj,hframe,h126,h128,h157,hacc,hvalid,hleftAll⟩ :=
    keyedPackedHaloPublish_sized_exec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad C hC hab hb hband hkey hwide hVeq hwV hcoords hunits tail suffix v S
      (by
        intro r hr hn
        have hv : r.1.val ≠ 128 := fun he => hn (Fin.ext he)
        simpa [groupHeaderValue,hv] using hready.masters r hr hn)
      (hready.fresh 133 (by simp)) hleft hblank hsource hready.metadata hready.keyWidth hkeys
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hready.fresh _ (by simp)) E outputTail hready.length
      (hready.fresh 129 (by simp)) hready.wordWidth hready.output (hready.fresh 140 (by simp))
      (hready.fresh 131 (by simp)) (hready.fresh 166 (by simp)) (hready.fresh 153 (by simp))
  let offsets := haloPackedOffsets s t (PhaseCellBand.width p u) a b L
  let w := executionWidth p l target rhsExp
  let ys := cstream A w (publishedWords offsets.length L
    (executedOutputWords s t p u (executionPrecision p l target rhsExp) l offsets.length L
      (executionStagePrecision p l target rhsExp) (sourceExponent l target rhsExp)
      (packedCellOrigin (s := s) a offsets) (fun _ => C)))
  let E' := scatterRows (L*w) E ys (packedCellGaps L w offsets)
  have hys : offsets.length*(L*w) ≤ ys.length := by simp [ys,Nat.mul_assoc]
  have hf : ScatterFits (L*w) E (packedCellGaps L w offsets) := by
    simpa [packedCellGaps] using windowGaps_fits (L*w) 0 (offsets.map (·*w)) E
      (fun _ _ => Nat.zero_le _) (packedCell_offsets_disjoint L w offsets (haloPackedOffsets_disjoint s t _ a b L))
      (packedCell_offsets_fit (b-a) L w offsets E hready.length (haloPackedOffsets_fit s t _ a b L))
  have hlen : E'.length = (b-a)*w :=
    (length_scatterRows _ _ _ _ hf (by simpa [packedCellGaps] using hys)).trans hready.length
  have hrdy := hready.of_publication hproj hframe houtput hlen
    (by simp only [h128,List.length_replicate]; exact hLs)
    (by simp [h157])
  change F.R 132 = E'++outputTail at houtput
  have hacc' := hacc
  rw [houtput] at hacc'
  have hall := packedHaloGroupOutputs_scatter C done E ys outputTail hready.length hys
    (by simpa only [← hready.output] using hold) (by simpa only [E',w,offsets] using hacc')
  refine ⟨v',F,m,E',hu',?_,he,h93,congrArg (fun B : Stacks 117 A => B.inp) hproj,
    congrArg (fun B : Stacks 117 A => B.out) hproj,hrdy,h126,hframe,?_,?_,?_,hleftAll,by simp [h128]⟩
  · have hb128 := hready.unaryLengthBound
    have hb157 := hready.binaryLengthBound
    dsimp only [packedHaloKeyCost]
    omega
  · rw [houtput]
    simpa only [E',w,offsets] using hall
  · intro hrange
    apply packedCellScatter_range L offsets E ys hrange
    refine ⟨_,rfl,?_⟩
    exact publishedOutputWords_norm hp hst hu hL hαu hθ hgap hbudget hpad
      (packedCellOrigin (s := s) a offsets) (fun _ => C) (fun _ _ k => hC k)
  · rw [houtput,hready.output]
    exact haloGroup_scatter_off_interior_word hst (PhaseCellBand.width p u) a b L w hb
      E ys outputTail hready.length hys

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
