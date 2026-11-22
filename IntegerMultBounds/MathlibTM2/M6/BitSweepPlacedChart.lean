module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepMatrixBudget

/-! Initialize the chart on register 28 of the physical PR589 block. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Host Stack Node Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

def sweepLiteralPorts : Fin 6 ↪ Fin 37 := ⟨![20,33,36,1,2,3],by decide⟩
private def invPorts : Fin 16 ↪ Fin 37 := ⟨![4,6,8,9,36,11,12,13,14,15,16,17,19,23,25,33],by decide⟩
private def productPorts : Fin 13 ↪ Fin 37 := ⟨![6,4,36,28,8,9,11,12,13,14,15,16,17],by decide⟩

theorem sweepPlacedChart_writes {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) :
    ∃ C : ℕ, ∀ (p : Fin 37 ↪ Fin T) (pool : Fin ((sweepMatrixDepth+1)*13) ↪ Fin T),
    (∀ i j, p i ≠ pool j) → ∀ (n : Fin 9) (r : Role), ∃ program : Pr P T Q prime U,
    ∀ w H (parent : Fin 64 → ZMod (prime^(w+1))) (dest : Fin ((prime^(w+1))^128)),
    let M := prime^(w+1)
    let N := M^128
    N < 2^H → H ≤ N+1 →
    Writes body (fun R => (R (p 27)).length = w ∧ R (p 20) = binSyms H 0 ∧
      R (p 33) = binSyms H (1 : ZMod M).val ∧ R (p 36) = binSyms H M ∧
      (∀ i ∈ ([1,2,3,4,6,8,9,11,12,13,14,15,16,17,19,25,26] : List (Fin 37)), R (p i) = []) ∧
      ∀ j, R (pool j) = []) (p 28) program (matrixWords prime H (sweepRankMatrices (w+1) parent n r dest false))
      ((C+6)*N^3) := by
  obtain ⟨C,depth,_,four,_,budget⟩ := sweepMatrixSetup_budget.choose_spec
  refine ⟨C,?_⟩
  intro p pool off n r
  let c := sweepLiteralPorts.trans p
  let inv := invPorts.trans p
  let g := productPorts.trans p
  have distinct (a b : Fin 37) (h : a ≠ b) := p.injective.ne h
  obtain ⟨inverse,makeInv⟩ := sweepQuarterInverse_exec body pool c inv (fun i j => off _ _) (fun i => distinct _ _ (by decide +revert))
    four (p 27) (p 26) (by simp [List.nodup_cons,inv,p.injective.eq_iff]; decide)
    (fun i => distinct _ _ (by decide +revert)) (distinct _ _ (by decide))
  obtain ⟨chart,write⟩ := sweepChartMatrix_writes body pool c g (fun i j => off _ _)
    (fun i => distinct _ _ (by decide +revert)) (fun i => distinct _ _ (by decide +revert)) (fun j => (off _ j).symm) n r (depth n r)
  refine ⟨.seq inverse (.seq chart (bclear (p 4))),?_⟩
  intro w H parent dest M N fits width v S ⟨clock,zeroWord,oneWord,modulus,blank,free⟩
  have fit : M < 2^H := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans_lt fits
  have scratch (i : Fin 6) (hi : 3 ≤ i) : S.R (c i) = [] := blank _ (by decide +revert)
  obtain ⟨u,k,hu,hk,init⟩ := makeInv w H v S fit clock (blank _ (by decide)) (blank _ (by decide)) oneWord modulus
    (fun i hi lo => blank _ (by decide +revert)) zeroWord oneWord modulus scratch free
  let word := binSyms (A := prime) H (Ring.inverse (4 : ZMod M)).val
  let B := {S with R := Function.update S.R (p 4) word}
  rw [show inv 0 = p 4 from rfl] at init
  change Exec body inverse (mk v S) k (mk u B) at init
  have keep (i : Fin 37) (hi : i ≠ 4) : B.R (p i) = S.R (p i) := Function.update_of_ne (p.injective.ne hi) _ _
  obtain ⟨y,l,hy,hl,emit⟩ := write (w+1) H parent dest fit u B
    ⟨⟨(keep 20 (by decide)).trans zeroWord,(keep 33 (by decide)).trans oneWord,(keep 36 (by decide)).trans modulus,
      fun i hi => (keep _ (by decide +revert)).trans (scratch i hi),
      fun j => (Function.update_of_ne (off 4 j).symm _ _).trans (free j)⟩,
      (keep 6 (by decide)).trans (blank _ (by decide)),Function.update_self ..,(keep 36 (by decide)).trans modulus,
      fun i lo hi => (keep (productPorts i) (by decide +revert)).trans (blank _ (by decide +revert))⟩
  let out := matrixWords prime H (sweepRankMatrices (w+1) parent n r dest false) ++ S.R (p 28)
  let F := {B with R := Function.update B.R (p 28) out}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (p 4) y F
  have len : (F.R (p 4)).length = H := by simp [F,B,word,length_binSyms]
  have final : {F with R := Function.update F.R (p 4) []} = {S with R := Function.update S.R (p 28) out} := by
    congr 1
    funext i
    by_cases h : i = p 4
    · subst i; simp [blank 4 (by decide)]
    · simp [F,B,Function.update_apply,h]
  rw [len,final] at clear
  have total := budget n r w H fits width
  have cost : k+l ≤ C*N^3 := by dsimp only [N,M]; dsimp only [sweepMatrixDepth] at hk hl total; omega
  have pos : 0 < N := pow_pos (pow_pos prime_prime.pos _) _
  have large := Nat.le_self_pow (by decide : 3 ≠ 0) N
  refine ⟨z,k+(l+(2*H+2)),hz.trans (hy.trans hu),by rw [Nat.add_mul]; omega,Exec.seq init (Exec.seq ?_ clear)⟩
  change Exec body chart (mk u B) l (mk y {B with R := Function.update B.R (p 28) out})
  simpa only [out,g,Function.Embedding.trans_apply,show productPorts 3 = 28 from rfl,keep 28 (by decide)] using emit

end IntegerMultBounds.MathlibTM2.M6.BitNode
