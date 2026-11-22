module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

/-! Header tapes indexed by interval, shared by every replica of that interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem flatIdleLeafBank [M8.Machine.Net] {Q : ℕ} {P U : Type} (capacity : columnCapacity ≤ Q)
    (i : Fin 9) :
    let owners := 142081+2
    let n := owners+222*6
    let fan := (Fin.castAddEmb (222*6) : Fin owners ↪ Fin n).trans (Fin.castAddEmb LeafCore.small)
    ∃ program : (Fin 32 × Fin 5) × Fin 222 → Pr P (n+LeafCore.small) Q prime U,
      ∀ w W, let V := (prime^w)^128*W
      0 < V → ∃ initial : Stacks (n+LeafCore.small) prime,
      ∀ k (child : Descriptor) (position : Fin (volume prime child) ≃ Fin V),
        let port := fan ((idleTape i k).castAdd 2)
        IdleChildPositions i k.2 w W child position →
        ∀ (body : P → Pr P (n+LeafCore.small) Q prime U) x u S, HelperFan fan x S →
          (∀ t, (∀ l, fan l ≠ t) → S.L t = initial.L t ∧ S.R t = initial.R t) →
          ∃ z F steps changed, Exec body (program k) (mk u S) steps (mk z F) ∧
            (steps : ℝ) ≤ (110+((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)))*
              ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
            z.user = u.user ∧ RecordPayload port (fun _ => blank) 0 changed F ∧
            (∀ t, t ≠ port → F.L t = S.L t ∧ F.R t = S.R t) ∧
            ∀ a, changed (position a) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
              (x (idleTape i k) ∘ position) a := by
  intro owners n fan
  let src := fun (j : Fin 222) (l : Fin 6) => (finProdFinEquiv (j,l)).natAdd owners
  let owner := fun k => ((idleTape i k).castAdd 2).castAdd (222*6)
  refine ⟨fun k => hostedStoppedDirectory capacity (src k.2) (owner k),?_⟩
  intro w W V positive
  let header : Fin (222*6) → List (Fin (prime+4)) := fun (a : Fin (222*6)) =>
    let p := finProdFinEquiv.symm a
    let e := idleInterval i p.1
    (Routines.hdr (phaseIntervalChild e.1 e.2 w W 64) p.2).map bitSymbol
  let initial : Stacks (n+LeafCore.small) prime :=
    ⟨[],[],fun _ => [],Fin.addCases (Fin.addCases (fun _ => []) header) (fun _ => [])⟩
  refine ⟨initial,?_⟩
  intro k child position port coords body x u S rep fresh
  let e := idleInterval i k.2
  let interval := phaseIntervalChild e.1 e.2 w W 64
  have size : volume prime interval = V :=
    intervalChild_volume (idleBounds i k.2).1 ((idleBounds i k.2).2.trans (by decide)) w W
  obtain ⟨z,F,steps,changed,run,paid,user,out,off,read⟩ := inheritedLeaf_exec capacity body (src k.2) (owner k) child interval size position coords.1 coords.2
    (x (idleTape i k)) u S positive (by
      intro j
      have h := fresh ((src k.2 j).castAdd LeafCore.small) (by
        intro l eq
        have ne : l.castAdd (222*6) = src k.2 j := (Fin.castAddEmb LeafCore.small).injective eq
        have val := congrArg Fin.val ne
        have := l.isLt
        simp only [src,Fin.val_castAdd,Fin.val_natAdd] at val
        omega)
      simpa [initial,src,header] using h.2) (fanPayload rep (idleTape i k)) (by
    intro j
    have h := fresh (j.natAdd n) (by
      intro l eq
      have val := congrArg Fin.val eq
      change ((l.castAdd (222*6)).castAdd LeafCore.small).val = _ at val
      simp only [Fin.val_castAdd,Fin.val_natAdd] at val
      have := l.isLt
      dsimp only [n] at val
      omega)
    simpa [initial] using h)
  refine ⟨z,F,steps,changed,run,paid.trans ?_,user,out,off,read⟩
  have headers := descriptorHeaderCost_le interval (LeafCore.positive_of_volume (size ▸ positive))
  rw [size] at headers
  have power : (1 : ℝ) ≤ ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 child.width) M8.Machine.BudgetBound.exponent_range.1.le
  have scale := le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) V) power
  have headerBill : (descriptorHeaderCost interval : ℝ) ≤ 110*V := by exact_mod_cast headers
  linarith only [headerBill,mul_le_mul_of_nonneg_left scale (by norm_num : (0 : ℝ) ≤ 110)]

end IntegerMultBounds.MathlibTM2.M6.BitNode
