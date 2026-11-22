module

public import IntegerMultBounds.MathlibTM2.M6.BitChartCutoff
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

/-! Runtime cutoff selection at the physical owner of a flat remainder child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem inheritedDispatch_exec [M8.Machine.Net] {n Q V : ℕ} {P U : Type}
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (n+LeafCore.small) Q prime U)
    (cmp : Fin 10 ↪ Fin (n+LeafCore.small)) (src : Fin 6 → Fin n) (port : Fin n)
    (child interval : Descriptor) (size : volume prime interval = V)
    (position : Fin (volume prime child) ≃ Fin V) (width : interval.width = child.width)
    (coords : InheritedIntervalPositions child interval size position)
    (rank w L cutoff : ℕ) (scaled : (w+1)*rank = child.width) (cutFits : cutoff < 2^L)
    (fits : child.width.size ≤ L) (word : Fin V → ZMod 2)
    (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime)
    (clock : (S.R (cmp 0)).length = w) (cut : S.R (cmp 1) = binSyms L cutoff)
    (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (cmp j) = [])
    (positive : 0 < V) (headers : ∀ j, S.R ((src j).castAdd LeafCore.small) = (Routines.hdr interval j).map bitSymbol)
    (payload : RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 word S)
    (free : ∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = [])
    (f : P) (budget : ℕ) :
    let result := fun (F : Stacks (n+LeafCore.small) prime) => ∃ changed,
      RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 changed F ∧
      (∀ t, t ≠ port.castAdd LeafCore.small → F.L t = S.L t ∧ F.R t = S.R t) ∧
      ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k
    let leafBill := (descriptorHeaderCost interval : ℝ) +
      ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
      ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
    (cutoff < child.width → ∀ z, ∃ y F k, Exec body (body f) (mk z S) k (mk y F) ∧
      k ≤ budget ∧ y.user = z.user ∧ result F) →
    ∃ y F, ∃ k : ℕ, y.user = u.user ∧ (k : ℝ) ≤ (4*w+23*child.width+22*L+51 : ℕ) +
      (if cutoff < child.width then (budget : ℝ)+2 else leafBill) ∧
      Exec body ((ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7)))
        (.call f) (hostedStoppedDirectory capacity src port))) (mk u S) k (mk y F) ∧ result F := by
  intro result leafBill recurse
  rw [← scaled] at fits
  have dispatch := chartCutoff_exec body cmp rank w L cutoff cutFits fits
    (.call f) (hostedStoppedDirectory capacity src port) u S clock cut empty result
    (if cutoff < child.width then (budget : ℝ)+2 else leafBill)
  rw [scaled] at dispatch
  apply dispatch
  intro z

  by_cases active : cutoff < child.width
  · simp only [ite_eq_left active]
    obtain ⟨y,F,k,run,paid,user,out⟩ := recurse active z
    exact ⟨y,F,_,user,by exact_mod_cast Nat.add_le_add_right paid 2,Exec.call run,out⟩
  · simp only [ite_eq_right active]
    obtain ⟨y,F,k,changed,run,paid,user,out,off,read⟩ :=
      inheritedLeaf_exec capacity body src port child interval size position width coords word z S positive headers payload free
    exact ⟨y,F,k,user,paid,run,changed,out,off,read⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
