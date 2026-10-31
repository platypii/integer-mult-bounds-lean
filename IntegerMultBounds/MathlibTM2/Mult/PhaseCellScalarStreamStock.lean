module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream
public import IntegerMultBounds.MathlibTM2.Fast.CMulScalarLoopStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! A real scalar is reused across the entire coefficient stream with one
numerical reserve, retained output volume and linear restoration traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

def realScalarWorkspace (C w N : ℕ) : ℕ := C*(rmulCost w+2*w+6)+5*(N*w)+4

theorem realScalarStream_exec_within
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    (xs : List GaussianInt) (a : GaussianInt)
    (hxs : ∀ x ∈ xs, Fits w x) (ha : Fits w a) (har : a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w q)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = csyms A w a)
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(rmulCost w+6*w+8)+6 ∧
      ∀ C, mnProgPush (cmulBlock cr
        (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr)) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+realScalarWorkspace C w xs.length)
        depth (realScalarStream cr ι hι hT hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R (cr .out)
          (cstream A w (xs.map (fun x => tdivN q (x*a)))++S.R (cr .out)))}) := by
  obtain ⟨vf,nf,huf,hnf,hef⟩ := realScalarStream_exec hcr hdisj hι hT hQ hA hw hq
    xs a hxs ha har v S hclean hr hx hy hxsv hysv hacc
  refine ⟨vf,nf,huf,hnf,?_⟩
  intro C hpush depth
  obtain ⟨v₁,n₁,ht₁⟩ := rmulScalar_loop_exec_within hcr hdisj hι hT hQ hA hw hq
    xs a hxs ha har v S hclean hr hx hy hysv C hpush depth
  let B := scalarBoundary cr S w (fun x => tdivN q (x*a)) [] xs
  have haccB : (B.R (cr .acc)).length = xs.length*w := by simp [B,scalarBoundary,hacc]
  have hxsvB : (B.R (cr .xsv)).length = xs.length*w := by
    simp [B,scalarBoundary,hxsv,hcr.eq_iff]
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body (cr .acc) (cr .out) (hcr.ne (by decide)) id v₁ B
  let F : Stacks T A := {B with R := movedR B.R (cr .acc) (cr .out) id (B.R (cr .acc))}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body (cr .xsv) (cr .xs) (hcr.ne (by decide)) id v₂ F
  have hxsvF : (F.R (cr .xsv)).length = xs.length*w := by
    simpa [F,movedR,hcr.eq_iff] using hxsvB
  have hp₂ : mnNativePushBound 1 (moveR (P := P) (Q := Q) (A := A) (U := U) (cr .acc) (cr .out) id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hp₃ : mnNativePushBound 1 (moveR (P := P) (Q := Q) (A := A) (U := U) (cr .xsv) (cr .xs) id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₂ := mn_native_exec_within he₂ 1 hp₂ depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 1 hp₃ depth _ (Nat.le_refl _)
  have ht₁' : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(xs.length*w+C*(rmulCost w+2*w+6)))
      depth (cwhileP (cr .xs) (cmulBlock cr (rmulOne ι hι hT hQ cr))) (mk v S) n₁ (mk v₁ B) :=
    ht₁.mono (by intro d z hz; omega)
  have ht := mn_seq_within_add ht₁' (mn_seq_within_add ht₂ ht₃)
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ht.mono ?_
  intro d z hz
  simp only [Nat.one_mul] at hz
  rw [haccB,hxsvF] at hz
  dsimp only [realScalarWorkspace]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
