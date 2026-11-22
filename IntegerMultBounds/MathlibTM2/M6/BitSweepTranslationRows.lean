module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepIntegerEntry
public import IntegerMultBounds.MathlibTM2.M6.BitSweepRowOrder
public import IntegerMultBounds.MathlibTM2.M6.BitSweepLastRank
public import IntegerMultBounds.MathlibTM2.M6.BitSweepParentRow

/-! The fixed translation rows and archive row in the initial PR589 rank matrix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

def translationRows : Matrix (Fin 61) (Fin 64) ℤ :=
  fun i j => Sum.elim (fun k => undoTranslation ⟨i.val%8,Nat.mod_lt _ (by decide)⟩ k)
    (fun _ => 0) (stageAxis.symm j)

theorem sweepInitialMatrix_words (w H : ℕ) (parent : Fin 64 → ZMod (prime^w)) (n : Fin 9) (r : Role) :
    let M := prime^w
    let last : Fin (M^128) := ⟨M^128-1,by have := pow_pos (pow_pos prime_prime.pos w) 128; dsimp [M]; omega⟩
    matrixWords prime H (sweepRankMatrices w parent n r last true) =
      (List.replicate 128 (binSyms H (M-1))).flatten ++
      (List.ofFn fun j => binSyms H (parent j).val).flatten ++
      matrixWords prime H (fun i j => (translationRows i j : ZMod M)) := by
  intro M last
  let mat := sweepRankMatrices w parent n r last true
  have firstRows : destinationRows prime H mat = (List.replicate 128 (binSyms H (M-1))).flatten := by
    rw [show destinationRows prime H mat = _ from sweepDestinationRows w H parent n r last]
    have digit (k : Fin 128) : (FlatCoordinateLayout.coordinates last k).val = M-1 := lastRank_coordinates (M := prime^w) k
    simp only [matrixWords,digit,List.ofFn_const]
    change (List.replicate 64 (binSyms (A := prime) H (M-1))).flatten ++ ((List.replicate 64 (binSyms H (M-1))).flatten ++ []) = _
    rw [List.append_nil,← List.flatten_append,← List.replicate_add]
  have tail : mat.submatrix (Fin.natAdd 3 : Fin 61 → Fin 64) id = fun i j => (translationRows i j : ZMod M) := by
    funext i j
    have ne (k : Fin 64) (hk : k.val < 3) : Fin.natAdd 3 i ≠ k := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    change mat (Fin.natAdd 3 i) j = _
    simp only [mat,sweepRankMatrices,↓reduceIte,ne 0 (by decide),ne 1 (by decide),ne 2 (by decide)]
    cases h : stageAxis.symm j <;> simp [translationRows,h]
  let row := fun i : Fin 64 => (List.ofFn fun j => binSyms (A := prime) H (mat i j).val).flatten
  change (List.ofFn row).flatten = _
  rw [List.ofFn_add (n := 2) (m := 62),List.flatten_append]
  change destinationRows prime H mat ++ (List.ofFn (fun i : Fin 62 => row (Fin.natAdd 2 i))).flatten = _
  rw [firstRows,List.ofFn_succ,List.flatten_cons,List.append_assoc]
  have weights (j : Fin 64) : mat 2 j = parent j := by simp [mat,sweepRankMatrices]
  change _ ++ ((List.ofFn fun j => binSyms (A := prime) H (mat 2 j).val).flatten ++ _) = _
  simp only [weights]
  apply congrArg (fun xs => (List.replicate 128 (binSyms (A := prime) H (M-1))).flatten ++ xs)
  apply congrArg (fun xs => (List.ofFn fun j => binSyms (A := prime) H (parent j).val).flatten ++ xs)
  apply congrArg (matrixWords prime H)
  funext i j
  have idx : Fin.natAdd 2 i.succ = Fin.natAdd 3 i := Fin.ext (by simp; omega)
  exact (congrArg (fun k => mat k j) idx).trans (congrFun (congrFun tail i) j)

/-- Write the translation tail first, then the archived weights and the
two initial destination rows. All three stages prepend to the same tape. -/
theorem sweepInitialMatrix_writes {T Q D : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (pool : Fin ((D+1)*13) ↪ Fin T) (c : Fin 6 ↪ Fin T) (a : Fin 7 ↪ Fin T) (width out : Fin T)
    (outside : ∀ i j, c i ≠ pool j) (cOff : ∀ i, c i ≠ out) (poolOff : ∀ j, pool j ≠ out)
    (aOff : ∀ i, a i ≠ out) (widthOff : ∀ i, width ≠ a i) (external : width ≠ out)
    (depth : ∀ i j, (sweepIntFormula (translationRows i j)).depth ≤ D)
    (negDepth : (sweepIntFormula (-1)).depth ≤ D) :
    ∃ program : Pr P T Q prime U, ∀ (w H : ℕ) (parent : Fin 64 → ZMod (prime^w)) (n : Fin 9) (r : Role)
      (archiveTail : List (Fin (prime+4))), (prime^w)^128 < 2^H →
    let M := prime^w
    let last : Fin (M^128) := ⟨M^128-1,by have := pow_pos (pow_pos prime_prime.pos w) 128; dsimp [M]; omega⟩
    let constants := fun (R : Regs T prime) => R (c 0) = binSyms H 0 ∧ R (c 1) = binSyms H (1 : ZMod M).val ∧
      R (c 2) = binSyms H M ∧ (∀ i : Fin 6, 3 ≤ i → R (c i) = []) ∧ ∀ j, R (pool j) = []
    let archive := fun (R : Regs T prime) => R (a 2) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ archiveTail ∧
      (R (a 1)).length = M.size ∧ (R width).length = H ∧ ∀ j : Fin 7, j = 0 ∨ 3 ≤ j → R (a j) = []
    let timeOf := fun z => time H (fun _ => 6*H+6) (sweepIntFormula z)
    let entryCost := fun k => (D+1)*(6*H+6)+1+(k+((D+1)*(2*H+2)+1))+(4*H+4)
    let translation := Finset.univ.sup fun i => Finset.univ.sup fun j => timeOf (translationRows i j)
    Writes body (fun R => constants R ∧ archive R) out program (matrixWords prime H (sweepRankMatrices w parent n r last true))
      (61*(64*entryCost translation+1)+1+(64*(8*(64*M.size)+14*M.size+16*H+44)+1+(128*entryCost (timeOf (-1))+1))) := by
  let leaf : Leaf Empty → Fin T → Pr P T Q prime U := fun a dst => bcopy (literalSource c a) dst (c 4) (c 5)
  let emit (z : ℤ) : Pr P T Q prime U := .seq ((initFrames pool (c 2) (D+1)).seq
    ((compile leaf (registerBank pool) (sweepIntFormula z) 0 (c 3)).seq (clearFrames pool (D+1))))
    (moveRightOrdered (c 3) (c 4) out)
  let translations := sequence (fun i => sequence (fun j => emit (translationRows i j)) (List.finRange 64)) (List.finRange 61)
  let initialWords := sequence (fun _ : Unit => emit (-1)) (List.replicate 128 ())
  refine ⟨.seq translations (.seq (writeSweepParentRow 64 a width out) initialWords),?_⟩
  intro w H parent n r tail fits M last constants archive timeOf entryCost translation v S ready
  have fit : M < 2^H := (Nat.le_self_pow (by decide : 128 ≠ 0) _).trans_lt fits
  have stable (R : Regs T prime) xs (h : constants R) : constants (Function.update R out xs) := by
    simpa only [constants,Function.update_of_ne (cOff _),Function.update_of_ne (poolOff _)] using h
  obtain ⟨u,k,hu,hk,trans⟩ := sweepIntMatrix_writes body pool c outside out cOff poolOff translationRows depth H fit v S ready.1
  let tr := matrixWords prime H (fun i j => (translationRows i j : ZMod M))
  let B := {S with R := Function.update S.R out (tr ++ S.R out)}
  have inputs : archive B.R := by
    simpa only [B,archive,Function.update_of_ne (aOff _),Function.update_of_ne external] using ready.2
  obtain ⟨y,l,hy,hl,weights⟩ := writeSweepParentRow_writes body a width out external widthOff aOff parent H
    (Nat.size_le.mpr fit) tail u B inputs
  let row := (List.ofFn fun i => binSyms (A := prime) H (parent i).val).flatten
  let F := {B with R := Function.update B.R out (row ++ B.R out)}
  have neg : ((-1 : ℤ) : ZMod M).val = M-1 := by
    have general (m : ℕ) (pos : 0 < m) : ((-1 : ℤ) : ZMod m).val = m-1 := by
      cases m with
      | zero => omega
      | succ m => simpa using ZMod.val_neg_one m
    exact general M (pow_pos prime_prime.pos _)
  have top (_ : Unit) : Writes body constants out (emit (-1)) (binSyms H (M-1)) (entryCost (timeOf (-1))) := by
    rw [← neg]
    exact sweepIntEntry_writes body pool c outside out cOff (-1) negDepth H fit
  obtain ⟨z,t,hz,ht,head⟩ := sequence_writes stable top (List.replicate 128 ()) y F
    (stable _ _ (stable _ _ ready.1))
  refine ⟨z,k+(l+t),hz.trans (hy.trans hu),Nat.add_le_add hk (Nat.add_le_add hl (by simpa using ht)),Exec.seq trans (Exec.seq weights ?_)⟩
  rw [sweepInitialMatrix_words]
  simpa only [initialWords,F,B,Function.update_self,Function.update_idem,List.flatMap_def,List.map_replicate,
    List.append_assoc,tr,row] using head

end IntegerMultBounds.MathlibTM2.M6.BitNode
