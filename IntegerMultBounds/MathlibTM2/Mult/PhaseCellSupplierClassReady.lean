module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierClassHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan

/-! Generated class headers establish the invariant part of supplier readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace SupplierInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def classDest (input : SupplierInputPlan T) : Fin 7 → Fin T :=
  ![input.publication.retained 0,input.publication.headers 0,input.publication.headers 1,
    input.publication.headers 2,input.publication.headers 3,input.width,input.core]

structure ClassReady (input : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S : Stacks T A) : Prop where
  radius : (S.R (input.publication.retained 0)).length = r.radius
  headers : ∀ i, (S.R (input.publication.headers i)).length = ![r.Fs.length,r.W,r.p,(r.b-r.a)*r.W] i
  width : (S.R input.width).length = r.Bcore
  core : (S.R input.core).length = coreLength s r.coreWidth r.k

/-- Per-call setup can change everything outside the retained class headers. -/
theorem ClassReady.of_frame {input : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S F : Stacks T A}
    (h : input.ClassReady r S) (hR : ∀ i, F.R (input.classDest i) = S.R (input.classDest i)) :
    input.ClassReady r F := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [show F.R (input.publication.retained 0) = S.R (input.publication.retained 0) from hR 0]
    exact h.radius
  · intro i
    have hh : F.R (input.publication.headers i) = S.R (input.publication.headers i) := by
      fin_cases i
      · exact hR 1
      · exact hR 2
      · exact hR 3
      · exact hR 4
    rw [hh]
    exact h.headers i
  · rw [show F.R input.width = S.R input.width from hR 5]
    exact h.width
  · rw [show F.R input.core = S.R input.core from hR 6]
    exact h.core

theorem generateClassReady_exec (input : SupplierInputPlan T) (source : Fin 6 → Fin T)
    (hdst : Function.Injective input.classDest) (hsep : ∀ i j, source i ≠ input.classDest j)
    (saved tmp : Fin T) (hsource : ∀ i, [source i,saved,tmp].Nodup)
    (hdstScratch : ∀ i, [input.classDest i,saved,tmp].Nodup)
    (hproduct : source 4 ≠ source 2) (hmargin : source 4 ≠ source 0)
    (r : PackedNormalizedJob A s) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![r.radius,r.Fs.length,r.W,r.p,r.b-r.a,r.Bcore] i)
    (hblank : ∀ i, S.R (input.classDest i) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ supplierClassHeadersCost S.R source input.classDest ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        2*supplierClassHeadersCost S.R source input.classDest) depth
        (supplierClassHeaders source input.classDest saved tmp) (Host.mk v S) n (Host.mk v' F) ∧
      input.ClassReady r F ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, k ≠ input.classDest i) → F.R k = S.R k := by
  obtain ⟨v',F,n,hu,hn,he,hheads,hI,hO,hL,hframe⟩ := supplierClassHeaders_exec_within (body := body)
    source input.classDest hdst hsep saved tmp hsource hdstScratch hproduct hmargin v S hblank hsaved htmp depth
  have hcore : r.b-r.a-2*r.radius = coreLength s r.coreWidth r.k := by rw [r.haloLength]; omega
  have hvals : supplierClassValues S.R source =
      ![r.radius,r.Fs.length,r.W,r.p,(r.b-r.a)*r.W,r.Bcore,coreLength s r.coreWidth r.k] := by
    simp [supplierClassValues,hvalues,hcore]
  have hlen (i : Fin 7) := congrArg List.length (hheads i)
  simp only [List.length_replicate,hvals] at hlen
  refine ⟨v',F,n,hu,hn,he,⟨hlen 0,?_,hlen 5,hlen 6⟩,hI,hO,hL,hframe⟩
  intro i
  fin_cases i
  · exact hlen 1
  · exact hlen 2
  · exact hlen 3
  · exact hlen 4
end SupplierInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
