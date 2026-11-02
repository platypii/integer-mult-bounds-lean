module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassGeometryRetirement

/-! Wrap a certified numerical run with paid geometry loading and retirement.
The final state retains only numerical outputs; all four geometry ports are fresh. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

noncomputable def initializedClassProgram (bank : ComputedClassBank → Fin T) (src : Fin 4 → Fin T)
    (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (loadClassGeometry bank src) (.seq p (clearWords ((classGeometryCopies bank src).map Prod.snd)))

theorem initializedClassRun_exec_within (body : P → Pr P T Q A U)
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) (hoff : ∀ i k, src i ≠ bank k)
    (B : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = [])
    (hwords : ∀ i, (S.R (src i)).length = B)
    (p : Pr P T Q A U) (runTime runStock depth : ℕ)
    (Valid : List (List (Fin (A+4))) → Prop)
    (hrun : ∀ w : HS T Q A U, ∃ w' n outputs, w'.user = w.user ∧ n ≤ runTime ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk w (loadedClassGeometry bank src S))+depth+runStock)
        depth p (Host.mk w (loadedClassGeometry bank src S)) n
        (Host.mk w' {loadedClassGeometry bank src S with R :=
          (Function.update (loadedClassGeometry bank src S).R (plan bank hinj).result
            (outputs.reverse.flatten++(loadedClassGeometry bank src S).R (plan bank hinj).result))})) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (24*B+25)+(runTime+(8*B+9)) ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(2*(24*B+25)+runStock)) depth
        (initializedClassProgram bank src p) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := loadClassGeometry_exec_within body bank hinj src hoff v S hblank depth
  rw [classGeometryLoadCost_eq bank src S B hwords] at he₁
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hvalid,he₂⟩ := hrun v₁
  have hresult (i : Fin 117) : geometry bank i ≠ (plan bank hinj).result := by
    simp [geometry,plan,RecoveryBanks.plan,recovery,hinj.eq_iff]
  have hresultWord : (loadedClassGeometry bank src S).R (plan bank hinj).result = S.R (plan bank hinj).result := by
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact hresult p.2
  rw [hresultWord] at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := retireClassGeometry_exec_within body bank hinj src (plan bank hinj).result
    hresult (outputs.reverse.flatten++S.R (plan bank hinj).result) v₂ S hblank B hwords depth
  refine ⟨v₃,(24*B+25)+(n₂+(8*B+9)),outputs,hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,hvalid,?_⟩
  have he := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
  simpa only [initializedClassProgram,Nat.add_zero] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
