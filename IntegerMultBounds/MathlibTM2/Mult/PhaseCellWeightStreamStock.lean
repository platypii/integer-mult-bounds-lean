module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream
public import IntegerMultBounds.MathlibTM2.Fast.CMulPairLoopStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Varying real factors share one coefficient reserve. Both operands restore;
only the ordered result is retained. This kernel serves both weighting passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

def realWeightWorkspace (C w N : ℕ) : ℕ := C*rmulCost w+7*(N*w)+6

theorem realWeightStream_exec_of_fits_within
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p w : ℕ} (hw : 1 ≤ w) (hshift : p ≤ w)
    (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w p)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ xs.length*(rmulCost w+6*w+2)+8 ∧
      ∀ C, mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+realWeightWorkspace C w xs.length)
        depth (realWeightStream cr ι hι hT hQ) (mk v S) n
        (mk vf {S with R := (Function.update S.R (cr .out)
          (cstream A w (List.zipWith (fun x a => tdivN p (x*a)) xs as)++S.R (cr .out)))}) := by
  obtain ⟨vf,nf,huf,hnf,hef⟩ := realWeightStream_exec_of_fits hcr hdisj hι hT hQ hA hw hshift
    xs as hlen hxs has v S hclean hr hx hy hxsv hysv hacc
  refine ⟨vf,nf,huf,hnf,?_⟩
  intro C hpush depth
  let zs := xs.zip as
  have hzX : zs.map Prod.fst = xs := List.map_fst_zip (by omega)
  have hzY : zs.map Prod.snd = as := List.map_snd_zip (by omega)
  have hzl : zs.length = xs.length := by simp [zs,hlen]
  obtain ⟨v₁,n₁,ht₁⟩ := rmulPair_loop_exec_within hcr hdisj hι hT hQ hA hw hshift zs
    (by
      intro z hz
      have hm := List.of_mem_zip hz
      exact ⟨hxs z.1 hm.1,(has z.2 hm.2).1,(has z.2 hm.2).2⟩)
    v S hclean hr (by rw [hzX]; exact hx) (by rw [hzY]; exact hy) C hpush depth
  rw [hzl] at ht₁
  let B := pairBoundary cr S w (fun x a => tdivN p (x*a)) [] zs
  have hysvB : (B.R (cr .ysv)).length = xs.length*w := by
    simp [B,pairBoundary,hysv,hcr.eq_iff,hzl]
  have haccB : (B.R (cr .acc)).length = xs.length*w := by simp [B,pairBoundary,hacc,hzl]
  have hxsvB : (B.R (cr .xsv)).length = xs.length*w := by
    simp [B,pairBoundary,hxsv,hcr.eq_iff,hzl]
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body (cr .ysv) (cr .ys) (hcr.ne (by decide)) id v₁ B
  let F : Stacks T A := {B with R := movedR B.R (cr .ysv) (cr .ys) id (B.R (cr .ysv))}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body (cr .acc) (cr .out) (hcr.ne (by decide)) id v₂ F
  let G : Stacks T A := {F with R := movedR F.R (cr .acc) (cr .out) id (F.R (cr .acc))}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body (cr .xsv) (cr .xs) (hcr.ne (by decide)) id v₃ G
  have haccF : (F.R (cr .acc)).length = xs.length*w := by simpa [F,movedR,hcr.eq_iff] using haccB
  have hxsvG : (G.R (cr .xsv)).length = xs.length*w := by
    simpa [G,F,movedR,hcr.eq_iff] using hxsvB
  have hmove (x y : CR) : mnNativePushBound 1
      (moveR (P := P) (Q := Q) (A := A) (U := U) (cr x) (cr y) id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₂ := mn_native_exec_within he₂ 1 (hmove .ysv .ys) depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 1 (hmove .acc .out) depth _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 1 (hmove .xsv .xs) depth _ (Nat.le_refl _)
  have ht₁' : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(xs.length*w+C*rmulCost w))
      depth (cwhileP (cr .ys) (rmulOne ι hι hT hQ cr)) (mk v S) n₁ (mk v₁ B) :=
    ht₁.mono (by intro d z hz; omega)
  have ht := mn_seq_within_add (mn_seq_within_add ht₁' ht₂) (mn_seq_within_add ht₃ ht₄)
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ht.mono ?_
  intro d z hz
  simp only [Nat.one_mul] at hz
  rw [hysvB,haccF,hxsvG] at hz
  dsimp only [realWeightWorkspace]
  omega

theorem realWeightStream_exec_within
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b w e f : ℕ} (hw : q + (e + f) + 2 ≤ w) (hshift : q + b ≤ w)
    (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ e)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ) ^ f ∧ a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w (q + b))
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ xs.length * (rmulCost w + 6 * w + 2) + 8 ∧
      ∀ C, mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+realWeightWorkspace C w xs.length)
        depth (realWeightStream cr ι hι hT hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs as) ++ S.R (cr .out))) }) := by
  exact realWeightStream_exec_of_fits_within hcr hdisj hι hT hQ hA (by omega) hshift xs as hlen
    (fun x hx => fits_of_value_power (by omega) x (hxs x hx))
    (fun a ha => ⟨fits_of_value_power (by omega) a (has a ha).1, (has a ha).2⟩)
    v S hclean hr hx hy hxsv hysv hacc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
