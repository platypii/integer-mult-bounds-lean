module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedPackedBoundaryFactoryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! The factor factory's temporary arithmetic ports overlap retained geometry.
Move its five conflicting ports into the disjoint 158--162 scratch bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

def retainedFactoryRouting : Fin 242 ≃ Fin 242 :=
  (Equiv.swap 147 158).trans ((Equiv.swap 148 159).trans
    ((Equiv.swap 149 160).trans ((Equiv.swap 150 161).trans (Equiv.swap 151 162))))

theorem retainedFactoryRouting_scratch :
    ([147,148,149,150,151] : List (Fin 242)).map retainedFactoryRouting = [158,159,160,161,162] := by
  decide

def retainedFactoryGeometryPorts : List (Fin 168) := 163::couplingIntervalPorts

theorem retainedFactoryRouting_geometry_safe (i : Fin 168) (hi : i ∈ retainedFactoryGeometryPorts) :
    let k := retainedFactoryRouting.symm (Fin.castLE (by decide : 168 ≤ 242) i)
    117 ≤ k.val ∧ k.val < 168 ∧ k ≠ 143 := by
  have h : retainedFactoryGeometryPorts.all (fun i => decide
      (let k := retainedFactoryRouting.symm (Fin.castLE (by decide : 168 ≤ 242) i)
       117 ≤ k.val ∧ k.val < 168 ∧ k ≠ 143)) = true := by decide
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp h i hi

/-- The existing arbitrary-register factory frame preserves actual geometry
through the protecting permutation, including its overlapped physical ports. -/
theorem retainedFactoryRouting_geometry_frame {A V s t band a b origin N : ℕ}
    (S F G : Stacks 242 A)
    (hproj : embStk retainedFactoryRouting F = G)
    (hframe : ∀ k : Fin 242, 117 ≤ k.val → k.val < 168 → k ≠ 143 →
      G.R k = (embStk retainedFactoryRouting S).R k)
    (h : CouplingIntervalMetadata V s t band a b origin N
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S)) :
    CouplingIntervalMetadata V s t band a b origin N
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) F) := by
  have hkeep (i : Fin 168) (hi : i ∈ retainedFactoryGeometryPorts) :
      F.R (Fin.castLE (by decide : 168 ≤ 242) i) = S.R (Fin.castLE (by decide : 168 ≤ 242) i) := by
    let k := retainedFactoryRouting.symm (Fin.castLE (by decide : 168 ≤ 242) i)
    have hs := retainedFactoryRouting_geometry_safe i hi
    have hp := congrArg (fun B : Stacks 242 A => B.R k) hproj
    have hf := hframe k hs.1 hs.2.1 hs.2.2
    have hh := hp.trans hf
    simpa only [embStk,Function.comp_apply,k,Equiv.apply_symm_apply] using hh
  apply h.of_frame
  · exact hkeep 163 (by simp [retainedFactoryGeometryPorts])
  · intro k hk
    exact hkeep k (List.mem_cons_of_mem _ hk)

/-- Place an abstract factory program before instantiating its numerical body. -/
def protectRetainedFactory {P U : Type} {Q A : ℕ} (factory : Pr P 242 Q A U) : Pr P 242 Q A U :=
  embProg (retainedFactoryRouting : Fin 242 → Fin 242) id factory

noncomputable def retainedGeometryFactory {P U : Type} {Q A : ℕ}
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  protectRetainedFactory (routedPackedBoundaryFactoryRelease (P := P) (U := U) (A := A) (Q := Q) hR hQ)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
