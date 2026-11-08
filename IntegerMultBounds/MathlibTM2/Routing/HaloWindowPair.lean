module

public import IntegerMultBounds.MathlibTM2.Routing.HaloWindowRun

/-! Two windows return the overlap bank roles to their original order. This is
the fixed body of the monotone scan, with no runtime parity register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloWindowPair
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloWindowRun
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def emitPair (width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) : Pr P T Q A U :=
  .seq (readEmitWindow width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
    (readEmitWindow width queue binary duplicate work bodyCount keepCount src archive spare overlap saved tmp)

theorem emitPair_native (width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) :
    mnNativePushBound 3 (emitPair (P := P) (Q := Q) (A := A) (U := U)
      width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp) :=
  ⟨readEmitWindow_native _ _ _ _ _ _ _ _ _ _ _ _ _,readEmitWindow_native _ _ _ _ _ _ _ _ _ _ _ _ _⟩

theorem emitPair_exec
    (width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (V : ℕ) (old fresh₁ kept₁ fresh₂ kept₂ tail queueTail : List (Fin (A+4)))
    (hB₁ : fresh₁.length < 2^V) (hK₁ : kept₁.length < 2^V)
    (hB₂ : fresh₂.length < 2^V) (hK₂ : kept₂.length < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = binSyms V fresh₁.length++binSyms V kept₁.length++
      binSyms V fresh₂.length++binSyms V kept₂.length++queueTail)
    (hsrc : S.R src = fresh₁++kept₁++fresh₂++kept₂++tail) (hold : S.R overlap = old)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,spare,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ 2*old.length+18*(fresh₁.length+fresh₂.length)+30*kept₁.length+28*kept₂.length+76*V+146 ∧
      Exec body (emitPair width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update
          (Function.update S.R queue queueTail) src tail)
          archive (((old++fresh₁++kept₁)++(kept₁++fresh₂++kept₂)).reverse++S.R archive)) overlap kept₂)}) := by
  have hr := hreg
  regs_ne hr
  let q := binSyms (A := A) V fresh₂.length++binSyms V kept₂.length++queueTail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readEmitWindow_exec (body := body)
    width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp hreg
    V old fresh₁ kept₁ (fresh₂++kept₂++tail) q hB₁ hK₁ v S hwidth
    (by simpa only [q,List.append_assoc] using hqueue)
    (by simpa only [List.append_assoc] using hsrc) hold hblank
  let M : Stacks T A := {S with R := (Function.update (Function.update (Function.update
    (Function.update (Function.update S.R queue q) overlap []) src (fresh₂++kept₂++tail))
    archive ((old++fresh₁++kept₁).reverse++S.R archive)) spare kept₁)}
  have off (i : Fin T) (hiq : i ≠ queue) (hio : i ≠ overlap) (his : i ≠ src)
      (hia : i ≠ archive) (hip : i ≠ spare) : M.R i = S.R i := by simp [M,hiq,hio,his,hia,hip]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := readEmitWindow_exec (body := body)
    width queue binary duplicate work bodyCount keepCount src archive spare overlap saved tmp
    (by regs_nodup) V kept₁ fresh₂ kept₂ tail queueTail hB₂ hK₂ v₁ M
    (by rw [off width ‹width ≠ queue› ‹width ≠ overlap› ‹width ≠ src› ‹width ≠ archive› ‹width ≠ spare›]; exact hwidth)
    (by simp [M,q,‹queue ≠ spare›,‹queue ≠ archive›,‹queue ≠ src›,‹queue ≠ overlap›])
    (by simp [M,‹src ≠ spare›,‹src ≠ archive›]) (by simp [M]) (by
      intro i hi
      by_cases hio : i = overlap
      · subst i
        simp [M,‹overlap ≠ spare›,‹archive ≠ overlap›.symm,‹src ≠ overlap›.symm]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact (hio rfl).elim
      | (rw [off _ (by first | assumption | exact Ne.symm (by assumption)) hio
          (by first | assumption | exact Ne.symm (by assumption))
          (by first | assumption | exact Ne.symm (by assumption))
          (by first | assumption | exact Ne.symm (by assumption))]
         exact hblank _ (by simp)))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hio : i = overlap
  · subst i; simp
  by_cases hia : i = archive
  · subst i
    simp [M,‹archive ≠ overlap›,‹archive ≠ spare›,List.reverse_append,List.append_assoc]
  by_cases his : i = src
  · subst i; simp [‹src ≠ overlap›,‹src ≠ archive›]
  by_cases hip : i = spare
  · subst i
    simp [hblank,‹overlap ≠ spare›.symm,‹archive ≠ spare›.symm,‹src ≠ spare›.symm,‹queue ≠ spare›.symm]
  by_cases hiq : i = queue
  · subst i; simp [M,‹queue ≠ overlap›,‹queue ≠ archive›,‹queue ≠ src›,‹queue ≠ spare›]
  · simp [M,hio,hia,his,hip,hiq]

end IntegerMultBounds.MathlibTM2.Routing.HaloWindowPair
