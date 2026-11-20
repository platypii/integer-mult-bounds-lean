module

public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors
public import IntegerMultBounds.MathlibTM2.Cover.LabelFactorization

/-! Physical execution of a PR589 port route on the cover-label tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Cover
open IntegerMultBounds.MathlibTM2.M8.RevMachine Matrix
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Stage2Machine.Straight (words)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open IntegerMultBounds.Swap.Modular
open ActualAffineScaling (modulus)
open SharedPlacementAlphabet (setTape)

theorem stageRoute_runs [M8.Machine.Net] {T : ℕ} (io : Fin T) (c : PortCertificate)
    (checked : c.Checked) (s : Fin 8) :
    ∃ (program : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading program ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (LabelSchedule.base v w)
      let route := (reduce (modulus w) (c.route s)).submatrix stageAxis.symm stageAxis.symm
      ∃ y : Fin (volume prime v) → ZMod 2,
        LabelPermutation.Transport v B w (fun g => g * route.transpose) (ext x) (ext y) ∧
        GraphContract.Runs program (LabelCall.bank roles v d)
          (LabelCall.bank (setTape roles io (sourceWord y) 0) v d)
          (C * volume prime v + 252 * LeafCore.coreCost (volume prime v) (w*64)) := by
  let e := stageAxis.symm
  let rev := Fin.revPerm.trans e
  let A := c.spread s
  let L := (fromBlocks 1 (-A) 0 1).submatrix e e
  let M := (fromBlocks 1 0 Aᵀ 1).submatrix e e
  let R := (fromBlocks 1 A 0 (avoid s - block s)).submatrix e e
  obtain ⟨ol,om,orr⟩ := stageFactor_order c s
  have order (i j : Fin 64) (h : i < j) : stageAxis (e i) < stageAxis (e j) := by simpa [e]
  have hk : 2 ≤ 64*64 := by decide
  have hl := (stageFactor_supported c checked s rev 0).1.2
  have hm := (stageFactor_supported c checked s e 0).2.1.2
  have hr := (stageFactor_supported c checked s rev 0).2.2.2
  obtain ⟨ls,_,left⟩ := LabelRoute.upper_runs hk io L (fun i j h => ol _ _ (order j i h)) hl
  obtain ⟨rs,_,right⟩ := LabelRoute.upper_runs hk io R (fun i j h => orr _ _ (order j i h)) hr
  obtain ⟨lc,lb⟩ := LabelFactorization.overhead ls
  obtain ⟨rc,rb⟩ := LabelFactorization.overhead rs
  let coeff := fun (E : Matrix (Fin 64) (Fin 64) ℚ) (hs : ∀ op ∈ LabelAddress.pass E,
    FlatCoordinateSchedule.Supported op) => LabelProgram.coefficient (LabelProgram.pass hk E hs)
  let upperBlock := fun (ps : List (LabelSchedule.Pair 64)) (E : Matrix (Fin 64) (Fin 64) ℚ) hs =>
    Blocks.seqB (Blocks.seqB (LabelRoute.pivot io ps) (LabelProgram.program io (LabelProgram.pass hk E hs)))
      (LabelRoute.pivot io ps)
  let program := Blocks.seqB (Blocks.seqB (upperBlock rs (R.submatrix Fin.rev Fin.rev) hr)
    (LabelProgram.program io (LabelProgram.pass hk M hm))) (upperBlock ls (L.submatrix Fin.rev Fin.rev) hl)
  refine ⟨program,2*lc+2*rc+coeff (R.submatrix Fin.rev Fin.rev) hr+coeff M hm+
    coeff (L.submatrix Fin.rev Fin.rev) hl+2,Blocks.seq_leading _ _,?_⟩
  intro v w B hw hb shape pos roles x head tape d route
  have budgetL := lb v w B (by decide) hw hb shape pos
  have budgetR := rb v w B (by decide) hw hb shape pos
  have u := stageFactor_reduce c checked s rev w
  have mid := stageFactor_reduce c checked s e w
  obtain ⟨y,xy,r₁⟩ := right v w B hw hb shape pos u.2.2.2 roles x head tape
  obtain ⟨z,r₂,yz⟩ := LabelBits.pass_runs hk M hm (fun i j h => om _ _ (order i j h))
    mid.2.2.1 shape hw hb pos io (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out,zo,r₃⟩ := left v w B hw hb shape pos u.2.1
    (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at r₂ r₃
  refine ⟨out,?_,Blocks.runs_mono (Blocks.seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _)
    (Blocks.seq_runs (Blocks.seq_leading _ _) (LabelProgram.leading _ _) r₁ r₂) r₃) ?_⟩
  · have product : route = reduce (modulus w) L * (reduce (modulus w) M * reduce (modulus w) R) := by
      change ((reduce (prime^w) (c.route s)).submatrix e e) = _
      rw [mid.1,← submatrix_mul_equiv _ _ e e e,← submatrix_mul_equiv _ _ e e e]
      rfl
    intro g a ha row hrow b hB h hh m hm' k hk' t ht
    change Matrix (Fin 64) (Fin 64) (ZMod (modulus w)) at g
    let yLabel := g * (reduce (modulus w) R).transpose
    let zLabel := yLabel * (reduce (modulus w) M).transpose
    have eq : g * route.transpose = zLabel * (reduce (modulus w) L).transpose := by
      simp [product,transpose_mul,yLabel,zLabel,Matrix.mul_assoc]
    let : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩
    let read := fun label : Matrix (Fin 64) (Fin 64) (ZMod (modulus w)) => ext out
      (RecursiveInterchangeLayout.index prime v a row (b*prime^(64*(w*64))+
        (LabelAddress.address (Q := prime^w) label).val) h m k t)
    apply (congrArg read eq).trans
    exact (zo zLabel a ha row hrow b hB h hh m hm' k hk' t ht).trans
      ((yz yLabel a ha row hrow b hB h hh m hm' k hk' t ht).trans (xy g a ha row hrow b hB h hh m hm' k hk' t ht))
  · have live := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v pos
    dsimp only [coeff]
    simp only [Nat.add_mul,Nat.mul_assoc] at *
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
