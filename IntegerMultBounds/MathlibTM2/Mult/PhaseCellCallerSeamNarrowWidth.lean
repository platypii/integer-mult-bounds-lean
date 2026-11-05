module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAffineHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGlobals

/-! After proper publication, borrow one restored publication header for the
seam solver's narrow word ruler. Its original unary precision source survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def seamNarrowWidthProgram (precision : Fin T) : Pr P (MachineTapes T) Q A U :=
  affineHeader 2 13 (unarySource T precision) (fullHeader T (.publication 3)) (seedReg T (.z 0))

theorem seamNarrowWidth_exec_within (body : P → Pr P (MachineTapes T) Q A U)
    (precision : Fin T) (p : ℕ) (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hprecision : (S.R (unarySource T precision)).length = p)
    (hblank : S.R (fullHeader T (.publication 3)) = []) (htmp : S.R (seedReg T (.z 0)) = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*(4*p+5)) depth
        (seamNarrowWidthProgram precision) (mk v S) (4*p+5)
        (mk v' {S with R := (Function.update S.R (fullHeader T (.publication 3))
          (List.replicate (2*p+13) tick))}) := by
  have hreg : [unarySource T precision,fullHeader T (.publication 3),seedReg T (.z 0)].Nodup := by
    have hs := (fullHeader_ne_bank id (.publication 3) precision).symm
    have ht := unarySource_ne_seed T precision (.z 0)
    have hd := fullHeader_ne_seed T (.publication 3) (.z 0)
    exact List.nodup_cons.mpr ⟨by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨hs,ht⟩,
      List.nodup_cons.mpr ⟨by simpa only [List.mem_singleton] using hd,List.nodup_singleton _⟩⟩
  obtain ⟨v',hu,he⟩ := affineHeader_exec body 2 13 (unarySource T precision)
    (fullHeader T (.publication 3)) (seedReg T (.z 0)) hreg v S hblank htmp
  rw [hprecision] at he
  refine ⟨v',hu,?_⟩
  simpa only [seamNarrowWidthProgram] using mn_native_exec_within he 13
    (affineHeader_native 2 13 (unarySource T precision) (fullHeader T (.publication 3)) (seedReg T (.z 0)))
    depth _ (by rfl)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
