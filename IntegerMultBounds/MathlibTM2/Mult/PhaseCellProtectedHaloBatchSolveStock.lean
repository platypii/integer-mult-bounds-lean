module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedHaloBatchSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedHaloGroupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedBatchSolveStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Protected group execution counts the surrounding spectator storage once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem protectedHaloBatchSolve_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (J R K : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed outTail : List (Fin (A+4)))
    (hbank : embStk groupReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L
      (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
      (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val)
      (cstream A (executionWidth p l target rhsExp)
        ((List.range (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length).flatMap
          (cellSourceRows L (haloGroupOrigin s t (PhaseCellBand.width p u) a b L) (fun _ => C))))
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) outTail S.inp S.out)
    (h129 : S.R 129 = []) (h133 : S.R 133 = []) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' S' n, v'.user = v.user ∧ n ≤ (4*B+4)+sizedClosedBatchBound p l B L s t u target rhsExp ∧
      ExecWithin (embTab groupReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+protectedBatchSolveWorkspace J R K p l B L s t u target rhsExp)
        0 (protectedBatchSolve hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧
      S'.R 110 = rhs ++ (cstream A w (chirpLine s C) ++ borrowed) ∧
      (∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      S'.R 129 = List.replicate B tick ∧
      (∀ k : Fin 144, 117 ≤ k.val → k ≠ 129 → S'.R k = S.R k) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ S'.R 93 = ys ++ outTail := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  let lo := haloGroupOrigin s t band a b L
  let raw := cstream A w (chirpLine s C)
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  have h116 : (S.R 116).length = B := by
    have hh := congrArg (fun S : Stacks 117 A => (S.R 116).length) hbank
    simpa [embStk, groupReg, batchInputBank, B] using hh
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := embTab groupReg body)
    (a := 116) (b := 129) (t := 133) (by decide) (by decide) (by decide) v S
    h133
  let S₃ : Stacks 144 A := { S with R := Function.update S.R 129 (List.replicate B tick) }
  have he₃' : Exec (embTab groupReg body) (ucopy 116 129 133) (mk v S) (4*B+4) (mk v₃ S₃) := by
    simpa [S₃, h116, h129] using he₃
  have hbank₃ : embStk groupReg S₃ = batchInputBank P N q l s t u band L B
      (fun n => (lo n).val) rhs (raw++borrowed) outTail S.inp S.out := by
    rw [groupProject_updateR S 129 (List.replicate B tick) (by decide)]
    exact hbank
  obtain ⟨vs, Ss, ns, hus, hns, hes, his, hos, hls, hrs, hcleans, hpoints, herrors, hprefix⟩ :=
    closedHaloGroup_spec_within (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hgroup hpad
      C hC x hx J R K hpushJ hpushR hpushK (embDn groupReg v₃) outTail (raw++borrowed) S.inp S.out
  obtain ⟨v₄, S₄, hv₄, hu₄, he₄, hbank₄, hoff₄⟩ :=
    exec_emb_within_stock groupReg groupReg_injective hbody (hes 0) v₃ rfl S₃ hbank₃
  have hfinalR (i : Fin 117) : S₄.R (groupReg i) = Ss.R i := congrArg (fun S : Stacks 117 A => S.R i) hbank₄
  have hfinalL (i : Fin 117) : S₄.L (groupReg i) = Ss.L i := congrArg (fun S : Stacks 117 A => S.L i) hbank₄
  have h93 : S₄.R 93 = Ss.R 93 := by simpa [groupReg] using hfinalR 93
  have h110 : S₄.R 110 = Ss.R 110 := by simpa [groupReg] using hfinalR 110
  refine ⟨v₄,S₄,(4*B+4)+ns,hu₄.trans (hus.trans hu₃),(by dsimp only [B,band]; omega),
    protectedBatchSolve_trace_within hR hQ he₃' he₄ (by
      unfold protectedBatchSolveWorkspace
      dsimp only [B,band] at *
      omega),?_,?_,?_,h110.trans hrs,?_,?_,?_,?_,?_,?_⟩
  · exact (congrArg (fun S : Stacks 117 A => S.inp) hbank₄).trans his
  · exact (congrArg (fun S : Stacks 117 A => S.out) hbank₄).trans hos
  · funext k
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val,hk⟩
      have he : groupReg i = k := Fin.ext rfl
      have hi : S.L (groupReg i) = [] := by
        have hh := congrArg (fun S : Stacks 117 A => S.L i) hbank
        simpa [embStk,batchInputBank] using hh
      rw [← he,hfinalL i,hls i,hi]
    · exact (hoff₄ k (groupReg_off k (by omega))).1
  · intro k hk hk93 hk110
    let i : Fin 117 := ⟨k.val,hk⟩
    have he : groupReg i = k := Fin.ext rfl
    rw [← he,hfinalR i]
    exact hcleans i (fun h => hk93 (he.symm.trans (congrArg groupReg h)))
      (fun h => hk110 (he.symm.trans (congrArg groupReg h)))
  · simpa [S₃] using (hoff₄ 129 (groupReg_off 129 (by decide))).2
  · intro k hk hk129
    simpa [S₃,hk129] using (hoff₄ k (groupReg_off k hk)).2
  · intro n i
    rw [h93]
    exact hpoints n i
  · intro n
    rw [h93]
    exact herrors n
  · obtain ⟨ys,hylen,hy⟩ := hprefix
    exact ⟨ys,hylen,h93.trans hy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
