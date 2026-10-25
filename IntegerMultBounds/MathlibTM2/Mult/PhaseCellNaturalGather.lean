module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherOffset
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherData
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! One restoring ambient-line sweep constructs the natural group's exact RHS.
The row-symbol count is generated from retained dimensions. Delimited advance
controls are explicit inputs here; their generation remains an outer stage. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalGatherControls (A s t band L w : ℕ) : List (Fin (A+4)) :=
  match naturalSymbolOrigins s t band L w with
  | [] => []
  | p::ps => gatherControls A (p::windowAdvances p ps)

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def naturalGather (dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rowCount wordR window buf tmp)
    (.seq (gatherOffset dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource) (uclear window))

theorem naturalGather_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp,
      initialControl, initialSource, rowCount, wordR].Nodup)
    {s : ℕ} [NeZero s] (t band L w : ℕ) (C : ZMod s → GaussianInt)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = naturalGatherControls A s t band L w)
    (hs : S.R src = cstream A w (chirpLine s C))
    (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl, advance, window, acc, current, savedSource, buf, tmp,
      initialControl, initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (naturalLengthGroup s t band L).length*(14*L*w+25)+12*s*w+6*L*w+9*L+29 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w ((List.range (naturalLengthGroup s t band L).length).flatMap
            (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C))) ++ S.R dst)) }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨p, ps, hps⟩ : ∃ p ps, naturalSymbolOrigins s t band L w = p::ps := by
    have hh : (naturalSymbolOrigins s t band L w).length > 0 := by
      simpa [naturalSymbolOrigins] using hgroup
    cases he : naturalSymbolOrigins s t band L w with
    | nil => simp [he] at hh
    | cons p ps => exact ⟨p, ps, rfl⟩
  let E := cstream A w (chirpLine s C)
  have hElength : E.length = s*w := by simp [E]
  have ho := naturalSymbolOrigins_ordered s t band L w
  have hf := naturalSymbolOrigins_fit s t band L w
  rw [hps] at ho hf
  have hp : p ≤ E.length := by have hh := hf p (by simp); omega
  have hfit : GatherFits (L*w) (E.drop p) (windowAdvances p ps) :=
    windowAdvances_fits (L*w) p ps E ho (by simpa only [hElength] using hf)
  have hvol := naturalGather_volume s t band L w p ps hps
  have hrows : gatherRows (L*w) (E.drop p) (windowAdvances p ps) =
      cstream A w ((List.range (naturalLengthGroup s t band L).length).flatMap
        (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C))) := by
    rw [gatherRows_windowAdvances (L*w) p ps E ho]
    have hh := naturalGatherRows_eq_rhs (A := A) t band L w C
    simpa only [naturalGatherRows, hps, E] using hh
  have hcount : ps.length+1 = (naturalLengthGroup s t band L).length := by
    have hh := congrArg List.length hps
    simpa [naturalSymbolOrigins] using hh.symm
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rowCount, wordR, window, buf, tmp].Nodup by regs_nodup) v S
    (hclean buf (by simp)) (hclean tmp (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R window (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct rowCount wordR window buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁, hrow, hw, hclean window (by simp)] using he₁
  have hoff (k : Fin T) (hk : k ≠ window) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂⟩ := gatherOffset_exec (body := body)
    (show [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp,
      initialControl, initialSource].Nodup by regs_nodup) (L*w) p (windowAdvances p ps) E hp hfit v₁ S₁
    (by rw [hoff control ‹control ≠ window›]; simpa [naturalGatherControls, hps] using hc)
    (by rw [hoff src ‹window ≠ src›.symm]; exact hs) (by simp [S₁]) (by
      intro k hk
      have hne : k ≠ window := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hoff k hne]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hclean _ (by simp))
  let S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (gatherRows (L*w) (E.drop p) (windowAdvances p ps) ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body window v₂ S₂
  have hwindow : (S₂.R window).length = L*w := by simp [S₂, S₁, ‹dst ≠ window›.symm]
  refine ⟨v₃, n₁+((windowAdvances p ps).length*(14*(L*w)+25)+12*(p+(windowAdvances p ps).sum)+23)+(2*(L*w)+2),
    hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hwindow]; omega) ?_⟩
  · rw [hrow, hw] at hn₁
    rw [windowAdvances_length, hcount]
    nlinarith only [hn₁, hvol]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hkw : k = window
      · subst k; simp [S₂, hclean window (by simp), ‹dst ≠ window›.symm]
      by_cases hkd : k = dst
      · subst k; simp [S₂, S₁, ‹dst ≠ window›, hrows]
      simp [S₂, S₁, hkw, hkd]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
