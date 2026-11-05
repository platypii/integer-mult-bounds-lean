module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonFullLineInputCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

def canonicalInputCopyProgram (master : Fin T) (r : Fin 13 → Fin T) : Pr P T Q A U :=
  .seq (affineHeader 2 8 master (r 9) (r 8))
    (.seq (generatedCopyNarrowPrefix (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12))
      (uclear (r 9)))

noncomputable def canonicalInputCopyCost (p u l target s t N : ℕ) [NeZero s] : ℕ :=
  (4*inverseMasterValues p u l target s t 0 s 2+5)+
    generatedCopyNarrowPrefixCost N s (packedHaloCommonWidth p l s u (target+1) 2)
      (inverseFullInputWidth p u l target s t)+(2*inverseFullInputWidth p u l target s t+2)

/-- Derive the canonical width, copy and resize the counted prefix, then retire
all controls. The precision master and arbitrary source suffix are preserved. -/
theorem canonicalInputCopy_exec (body : P → Pr P T Q A U)
    (master : Fin T) (r : Fin 13 → Fin T)
    (hreg : [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,r 9,r 10,r 11,r 12].Nodup)
    (hwreg : [master,r 9,r 8].Nodup)
    (p u l target t : ℕ) (Fs : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R (r 0)).length = Fs.length) (hline : (S.R (r 1)).length = s)
    (hwide : (S.R (r 2)).length = packedHaloCommonWidth p l s u (target+1) 2)
    (hmaster : (S.R master).length = inverseMasterValues p u l target s t 0 s 2)
    (hsrc : S.R (r 5) = cstream A (packedHaloCommonWidth p l s u (target+1) 2)
      (Fs.map (chirpLine s)).flatten++tail)
    (hfresh : ∀ k ∈ [r 3,r 4,r 6,r 7,r 8,r 9,r 10,r 11,r 12], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ canonicalInputCopyCost p u l target s t Fs.length ∧
      Exec body (canonicalInputCopyProgram master r) (mk v S) n
        (mk v' {S with R := (Function.update S.R (r 6)
          (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}) := by
  have hr := hreg
  regs_ne hr
  have hwidth : S.R (r 9) = [] := hfresh _ (by simp)
  have htmp : S.R (r 8) = [] := hfresh _ (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := fullLineInputWidth_exec body _ _ _ hwreg p u l target t v S hmaster hwidth htmp
  let M : Stacks T A :=
    {S with R := Function.update S.R (r 9) (List.replicate (inverseFullInputWidth p u l target s t) tick)}
  have hM (k) (hk : k ≠ r 9) : M.R k = S.R k := by
    dsimp only [M]
    exact Function.update_of_ne hk _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedCommonFullLineInputCopy_exec body
    (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12)
    hreg p u l target t Fs tail v₁ M
    (by simpa only [hM _ ‹r 0 ≠ r 9›] using hN)
    (by simpa only [hM _ ‹r 1 ≠ r 9›] using hline)
    (by simpa only [hM _ ‹r 2 ≠ r 9›] using hwide)
    (by simp [M])
    (by simpa only [hM _ ‹r 5 ≠ r 9›] using hsrc)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hM _ (by first | assumption | exact Ne.symm (by assumption))] <;>
        exact hfresh _ (by simp)) 0
  let H : Stacks T A :=
    {M with R := (Function.update M.R (r 6)
      (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body (r 9) v₂ H
  have hc : (H.R (r 9)).length = inverseFullInputWidth p u l target s t := by
    simp [H,M,Ne.symm ‹r 6 ≠ r 9›]
  have hframe : {H with R := Function.update H.R (r 9) []} =
      {S with R := (Function.update S.R (r 6)
        (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = r 9
    · subst k; simp [Ne.symm ‹r 6 ≠ r 9›,hwidth]
    · simp [H,M,Function.update_apply,hk]
  rw [hc,hframe] at he₃
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂.toExec he₃)⟩
  dsimp only [canonicalInputCopyCost]
  rw [hmaster]
  omega

theorem canonicalInputCopy_native (master : Fin T) (r : Fin 13 → Fin T) :
    mnNativePushBound 8 (canonicalInputCopyProgram (P := P) (Q := Q) (A := A) (U := U) master r) := by
  refine ⟨affineHeader_native 2 8 _ _ _,
    mnNativePushBound_mono (by decide) (generatedCopyNarrowPrefix_native ..),?_⟩
  simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem canonicalInputCopy_within {master : Fin T} {r : Fin 13 → Fin T}
    {p u l target t N n : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (canonicalInputCopyProgram master r) z n z')
    (hn : n ≤ canonicalInputCopyCost p u l target s t N) (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      8*canonicalInputCopyCost p u l target s t N) depth (canonicalInputCopyProgram master r) z n z' :=
  mn_native_exec_within he 8 (canonicalInputCopy_native ..) depth _ (by omega)


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
