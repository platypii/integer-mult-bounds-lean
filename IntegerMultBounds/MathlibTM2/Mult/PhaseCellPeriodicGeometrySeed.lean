module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! Reuse completed factory geometry for a periodic coupling call. Only the four
computed metadata words are released; the dimensions and prepared factors stay. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def periodicGeometryDerived : List (Fin 242) := [148,154,156,164]

def periodicGeometrySeed {A : ℕ} (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := fun k => if k ∈ periodicGeometryDerived then [] else S.R k}

theorem periodicGeometrySeed_frame {A : ℕ} (S : Stacks 242 A) (k : Fin 242)
    (hk : k ∉ periodicGeometryDerived) : (periodicGeometrySeed S).R k = S.R k := by
  simp only [periodicGeometrySeed,ite_eq_right hk]

private theorem periodicGeometryDerived_range (k : Fin 242) (hk : k ∈ periodicGeometryDerived) :
    148 ≤ k.val ∧ k.val < 168 := by
  simp only [periodicGeometryDerived,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> decide

theorem periodicGeometrySeed_bank {A q w W N : ℕ} {S : Stacks 242 A}
    (h : PackedPreparedBank q w W N S) : PackedPreparedBank q w W N (periodicGeometrySeed S) := by
  apply h.of_runtime_frame (F := periodicGeometrySeed S) rfl
  · intro k hk
    apply periodicGeometrySeed_frame
    intro hm
    have := periodicGeometryDerived_range k hm
    omega
  · exact periodicGeometrySeed_frame S 119 (by decide)
  · intro k hk _
    apply periodicGeometrySeed_frame
    intro hm
    have := periodicGeometryDerived_range k hm
    omega

theorem periodicGeometrySeed_factorPages {A : ℕ} {S : Stacks 242 A}
    {bo hf df : List (Fin (A+4))} (h : PackedBoundaryFactorPages bo hf df S) :
    PackedBoundaryFactorPages bo hf df (periodicGeometrySeed S) := by
  apply h.of_solution_frame
  intro k hk _
  apply periodicGeometrySeed_frame
  intro hm
  have := periodicGeometryDerived_range k hm
  omega

theorem periodicGeometrySeed_data {A V s t band a b origin N : ℕ} {S : Stacks 242 A}
    (h : CouplingIntervalMetadata V s t band a b origin N
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S)) :
    ((periodicGeometrySeed S).R 163).length = V ∧
    (∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      (periodicGeometrySeed S).R (Fin.castLE (by decide) k) =
        binSyms V (couplingIntervalValue s t band a b origin N k)) ∧
    (∀ k ∈ periodicGeometryDerived, (periodicGeometrySeed S).R k = []) := by
  refine ⟨?_,?_,?_⟩
  · rw [periodicGeometrySeed_frame S 163 (by decide)]
    exact h.width
  · intro k hk
    have hoff : Fin.castLE (by decide : 168 ≤ 242) k ∉ periodicGeometryDerived := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [periodicGeometrySeed_frame S _ hoff]
    apply h.encoded k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro k hk
    simp only [periodicGeometrySeed,ite_eq_left hk]

theorem periodicGeometrySeed_exec {Q A V s t band a b origin N : ℕ} {P U : Type}
    {body : P → Pr P 242 Q A U} (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : CouplingIntervalMetadata V s t band a b origin N
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S)) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords periodicGeometryDerived) (mk v S) (8*V+9)
        (mk v' (periodicGeometrySeed S)) := by
  have hlen (k : Fin 168) (hk : k ∈ couplingIntervalPorts) :
      (S.R (Fin.castLE (by decide : 168 ≤ 242) k)).length = V := by
    have hh := congrArg List.length (h.encoded k hk)
    simpa only [embStk,Function.comp_apply,length_binSyms] using hh
  have hsum : (periodicGeometryDerived.map fun k => (S.R k).length).sum = 4*V := by
    change (S.R 148).length+((S.R 154).length+((S.R 156).length+((S.R 164).length+0))) = 4*V
    rw [show (S.R 148).length = V from hlen 148 (by decide),
      show (S.R 154).length = V from hlen 154 (by decide),
      show (S.R 156).length = V from hlen 156 (by decide),
      show (S.R 164).length = V from hlen 164 (by decide)]
    omega
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) periodicGeometryDerived (by decide) v S
  refine ⟨v',hu,he.cast ?_ rfl⟩
  rw [hsum]
  simp only [periodicGeometryDerived,List.length_cons,List.length_nil]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
