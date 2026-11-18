module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnAdd
public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnReady

/-! Execute one reverse elimination column on the physical tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def columnProgram (k : Fin d) : Pr P (N+1) columnCapacity prime U :=
  reverseColumn (Fin.last N) k (fun r i => columnAddProgram k i r)
    (coordinateSwap (fun i j => columnSwapProgram d i j) k)

noncomputable def columnProgramTime (U : Type) (k r : Fin d) (w W H J : ℕ) : ℕ :=
  let swap := fun (i j : Fin d) => 1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J
  let shear := fun a b t => 1+reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t r prime w W H J
  let cost := fun i => if k < i then shear k i i else swap i k + shear i k i + swap i k
  2*(r.val+1)+(d-1)*Finset.univ.sup cost+swap (min k r) (max k r)

theorem columnProgram_exec (k : Fin d) (rows : Fin d → Fin d) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (unit : IsUnit (matrix (rows k) k)) (tail rest : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (code : S.R (Fin.last N) = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let r := rows k
    let ready := ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+1) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i) = [] ∧ D.R (columnPorts i) = []
    let remaining := orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest
    ready (fun x => stepOp k r matrix (Ring.inverse (matrix r k)) *ᵥ addr x) S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ columnProgramTime U k r w W H J ∧
      Exec body (columnProgram k) (mk v S) n (mk z F) ∧ ready addr F ∧ clean F ∧ F.R (Fin.last N) = remaining := by
  intro r ready clean remaining initial free
  let swap := fun (i j : Fin d) => 1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J
  let shear := fun a b t => 1+reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t r prime w W H J
  let cost := fun i => if k < i then shear k i i else swap i k + shear i k i + swap i k
  let ok := fun y D => ready y D ∧ clean D ∧ D.R (Fin.last N) = remaining
  apply reverseColumn_exec body (Fin.last N) k rows matrix _ _ _ ok _ _ v S rest addr code
  · have outside (i : Fin N) : columnPorts i ≠ Fin.last N := fun e => i.isLt.ne (congrArg Fin.val e)
    have bankOutside (i : Fin 35) : columnBank i ≠ Fin.last N := outside _
    obtain ⟨word,layout,placed⟩ := initial
    refine ⟨⟨word,?_,placed⟩,fun i hi => ?_,Function.update_self ..⟩
    · rcases layout with ⟨base,width,one,padded,clock,archive,scratch,src,dst⟩
      constructor <;> simp only [Function.update_of_ne (bankOutside _)] <;> assumption
    · exact ⟨(free i hi).1,(Function.update_of_ne (outside i) ..).trans (free i hi).2⟩
  · intro i ne y u D h
    obtain ⟨z,F,n,hz,hn,run,next⟩ := columnAddProgram_exec k i r ne H J hm hw hW body u D matrix unit tail
      remaining dest q empty original y h
    exact ⟨z,F,n,hz,hn.trans (Finset.le_sup (f := cost) (Finset.mem_univ i)),run,next⟩
  · intro y u D h
    change ∃ z F n, z.user = u.user ∧ n ≤ swap (min k r) (max k r) ∧ Exec body (coordinateSwap (fun i j => columnSwapProgram d i j) k r) (mk u D) n (mk z F) ∧ ok (fun x => y x ∘ Equiv.swap k r) F
    have ordered (i j : Fin d) (lt : i < j) := columnSwapProgram_exec i j lt H J hm hw hW body u D matrix
      tail dest q original y h.1 h.2.1
    rcases lt_trichotomy k r with lt | eq | gt
    · obtain ⟨z,F,n,hz,hn,run,next,freeF,_,stream⟩ := ordered k r lt
      exact ⟨z,F,n,hz,by simpa [min_eq_left lt.le,max_eq_right lt.le] using hn,
        by simpa [coordinateSwap,lt] using run,next,freeF,stream.trans h.2.2⟩
    · refine ⟨u,D,1,rfl,by simp [swap],?_,?_⟩
      · simpa [← eq,coordinateSwap] using Exec.act (body := body) .done (mk u D)
      · simpa [← eq] using h
    · obtain ⟨z,F,n,hz,hn,run,next,freeF,_,stream⟩ := ordered r k gt
      exact ⟨z,F,n,hz,by simpa [min_eq_right gt.le,max_eq_left gt.le] using hn,
        by simpa [coordinateSwap,gt.not_gt,gt] using run,by simpa [Equiv.swap_comm k r] using next,
        freeF,stream.trans h.2.2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
