module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateCoreLength
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan

/-! The shared counted-margin operation establishes a supplier's core header. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generateSupplierCoreLength_exec (halo radius core saved : Fin T)
    (hreg : [halo,radius,core,saved].Nodup) (r : PackedNormalizedJob A s)
    (v : HS T Q A U) (S : Stacks T A)
    (hhalo : (S.R halo).length = r.b-r.a) (hradius : (S.R radius).length = r.radius)
    (hcore : S.R core = []) (hsaved : S.R saved = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        2*(4*(r.b-r.a)+8*r.radius+12)) depth
        (generateCoreLength halo radius core saved) (Host.mk v S) (4*(r.b-r.a)+8*r.radius+12)
        (Host.mk v' {S with R := (Function.update S.R core
          (List.replicate (coreLength s r.coreWidth r.k) Node.tick))}) := by
  obtain ⟨v',hu,he⟩ := generateCoreLength_exec_within (body := body) halo radius core saved hreg v S hcore hsaved depth
  have hlength : r.b-r.a-2*r.radius = coreLength s r.coreWidth r.k := by
    rw [r.haloLength]
    omega
  rw [hhalo,hradius,hlength] at he
  exact ⟨v',hu,he⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
