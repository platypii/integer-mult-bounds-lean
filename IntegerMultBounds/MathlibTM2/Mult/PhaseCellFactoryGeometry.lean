module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Generate the factory's binary origin and interval length from ordinary
retained unary coordinates, and install its private width word. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def factoryGeometry (a b width origin extent privateWidth span tmp saved carry : Fin T) : Pr P T Q A U :=
  .seq (ucopy width privateWidth saved)
    (.seq (toBinary a width origin saved tmp carry)
      (.seq (ucopy b span saved) (.seq (usub a span saved)
        (.seq (toBinary span width extent saved tmp carry) (uclear span)))))

def factoryGeometryCost (a b V : ℕ) : ℕ :=
  a*(4*V+10)+(b-a)*(4*V+10)+4*a+4*b+2*(b-a)+12*V+30

theorem factoryGeometry_exec (a b width origin extent privateWidth span tmp saved carry : Fin T)
    (hreg : [a,b,width,origin,extent,privateWidth,span,tmp,saved].Nodup)
    (x y V : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ha : (S.R a).length = x) (hb : (S.R b).length = y) (hw : (S.R width).length = V)
    (hblank : ∀ i ∈ [origin,extent,privateWidth,span,tmp,saved], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ factoryGeometryCost x y V ∧
      Exec body (factoryGeometry a b width origin extent privateWidth span tmp saved carry) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R privateWidth
          (List.replicate V tick)) origin (binSyms V x)) extent (binSyms V (y-x)))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹width ≠ privateWidth› ‹width ≠ saved› ‹privateWidth ≠ saved›
    v S (hblank saved (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R privateWidth (List.replicate V tick)}
  have he₁' : Exec body (ucopy width privateWidth saved) (mk v S) (4*V+4) (mk v₁ S₁) := by
    simpa only [hw,hblank privateWidth (by simp),List.append_nil,S₁] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toBinary_exec (body := body)
    (u := a) (wR := width) (c := origin) (t := saved) (tmp := tmp) (by regs_nodup) carry v₁ S₁
    (by simp [S₁,‹origin ≠ privateWidth›,hblank origin (by simp)])
    (by simp [S₁,‹privateWidth ≠ saved›.symm,hblank saved (by simp)])
    (by simp [S₁,‹privateWidth ≠ tmp›.symm,hblank tmp (by simp)])
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R origin (binSyms V x)}
  have ha₁ : (S₁.R a).length = x := by simpa only [S₁,Function.update_of_ne ‹a ≠ privateWidth›] using ha
  have hw₁ : (S₁.R width).length = V := by simpa only [S₁,Function.update_of_ne ‹width ≠ privateWidth›] using hw
  rw [ha₁,hw₁] at hn₂ he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) ‹b ≠ span› ‹b ≠ saved› ‹span ≠ saved› v₂ S₂
    (by simp [S₂,S₁,ne_comm,hblank saved (by simp), *])
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R span (List.replicate y tick)}
  have he₃' : Exec body (ucopy b span saved) (mk v₂ S₂) (4*y+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hb,hblank span (by simp),ne_comm, *] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := usub_exec (body := body) ‹a ≠ span› ‹a ≠ saved› ‹span ≠ saved› v₃ S₃
    (by simp [S₃,S₂,S₁,ne_comm,hblank saved (by simp), *])
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R span (List.replicate (y-x) tick)}
  have he₄' : Exec body (usub a span saved) (mk v₃ S₃) (4*x+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,ha,ne_comm, *] using he₄
  obtain ⟨v₅,n₅,hu₅,hn₅,he₅⟩ := toBinary_exec (body := body)
    (u := span) (wR := width) (c := extent) (t := saved) (tmp := tmp) (by regs_nodup) carry v₄ S₄
    (by simp [S₄,S₃,S₂,S₁,ne_comm,hblank extent (by simp), *])
    (by simp [S₄,S₃,S₂,S₁,ne_comm,hblank saved (by simp), *])
    (by simp [S₄,S₃,S₂,S₁,ne_comm,hblank tmp (by simp), *])
  let S₅ : Stacks T A := {S₄ with R := Function.update S₄.R extent (binSyms V (y-x))}
  have hspan₄ : (S₄.R span).length = y-x := by simp [S₄]
  have hw₄ : (S₄.R width).length = V := by simp [S₄,S₃,S₂,S₁, *]
  rw [hspan₄,hw₄] at hn₅ he₅
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec body span v₅ S₅
  have hspan₅ : (S₅.R span).length = y-x := by simp [S₅,S₄,ne_comm, *]
  rw [hspan₅] at he₆
  refine ⟨v₆,(4*V+4)+(n₂+((4*y+4)+((4*x+4)+(n₅+(2*(y-x)+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast rfl ?_⟩
  · dsimp only [factoryGeometryCost]
    omega
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hspan : i = span
    · subst i; simp [S₅,S₄,S₃,S₂,S₁,ne_comm,hblank span (by simp), *]
    by_cases hextent : i = extent
    · subst i; simp [S₅,S₄,S₃,S₂,S₁, *]
    by_cases horigin : i = origin
    · subst i; simp [S₅,S₄,S₃,S₂,S₁, *]
    by_cases hwidth : i = privateWidth
    · subst i; simp [S₅,S₄,S₃,S₂,S₁, *]
    · simp only [S₅,S₄,S₃,S₂,S₁,Function.update_of_ne hspan,Function.update_of_ne hextent,
        Function.update_of_ne horigin,Function.update_of_ne hwidth]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
