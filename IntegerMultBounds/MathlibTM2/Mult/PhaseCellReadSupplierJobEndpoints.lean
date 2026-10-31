module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan

/-! A queued origin and shared halo width install the job's exact endpoint words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem readSupplierJobEndpoints_exec (input : SupplierInputPlan T)
    (width halo queue binary work saved tmp : Fin T)
    (hreg : [width,halo,queue,binary,input.parameters 6,input.parameters 7,work,saved,tmp].Nodup)
    (r : PackedNormalizedJob A s) (V : ℕ) (hfit : r.a < 2^V) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hwidth : (S.R width).length = V)
    (hhalo : (S.R halo).length = r.b-r.a) (hqueue : S.R queue = binSyms V r.a++tail)
    (hblank : ∀ k ∈ [binary,input.parameters 6,input.parameters 7,work,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readSupplierEndpointsCost V r.a (r.b-r.a) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        3*readSupplierEndpointsCost V r.a (r.b-r.a)) depth
        (readSupplierEndpoints width halo queue binary (input.parameters 6) (input.parameters 7) work saved tmp)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R queue tail)
          (input.parameters 6) (List.replicate r.a Node.tick)) (input.parameters 7) (List.replicate r.b Node.tick))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := readSupplierEndpoints_exec_within (body := body)
    width halo queue binary (input.parameters 6) (input.parameters 7) work saved tmp hreg V r.a (r.b-r.a) hfit tail v S
    hwidth hhalo hqueue hblank depth
  have hend : r.a+(r.b-r.a) = r.b := Nat.add_sub_of_le r.bounds.hab
  rw [hend] at he
  exact ⟨v',n,hu,hn,he⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
