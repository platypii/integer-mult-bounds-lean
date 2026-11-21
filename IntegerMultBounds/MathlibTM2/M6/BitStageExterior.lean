module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds

/-! Form the scan's exterior volume from the row descriptor and restore the scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

def stageRowFactors : Fin 11 ↪ Fin 14 := ⟨![0,1,2,7,6,8,9,10,11,12,13],by decide⟩
def stageExteriorFactors : Fin 11 ↪ Fin 14 := ⟨![6,3,4,7,5,8,9,10,11,12,13],by decide⟩

noncomputable def stageExterior (r : Fin 14 ↪ Fin T) : Pr P T Q prime U :=
  .seq (middleRowDescriptor (stageRowFactors.trans r))
    (.seq (middleRowDescriptor (stageExteriorFactors.trans r)) (bclear (r 6)))

theorem stageExterior_exec (body : P → Pr P T Q prime U) (r : Fin 14 ↪ Fin T)
    (v : RecursiveInterchangeLayout.Descriptor) (positive : v.Positive)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let W := v.beforeRows*v.rows*v.between*v.afterD
    let word := fun a : ℕ => binSyms (A := prime) a.size a
    (∀ i : Fin 4, S.R (r (i.castAdd 10)) =
      (M8.RevMachine.Routines.hdr v ((![0,1,4,5] : Fin 4 → Fin 6) i)).map bitSymbol) →
    S.R (r 4) = word 1 → (∀ i : Fin 14, 5 ≤ i.val → S.R (r i) = []) →
    ∃ z t, z.user = u.user ∧ t ≤ 868*W ∧ Exec body (stageExterior r) (mk u S) t
      (mk z {S with R := Function.update S.R (r 5) (word W)}) := by
  intro W word fields one empty
  have words (i : Fin 4) := (fields i).trans (canonicalBits_symbols _)
  obtain ⟨ha,hr,_,hg,hd⟩ := positive
  let p := v.beforeRows*v.rows*v.between
  have hp : 0 < p := Nat.mul_pos (Nat.mul_pos ha hr) hg
  obtain ⟨y,k,user,cost,first⟩ := seedProduct_exec body (stageRowFactors.trans r) _ _ _ ha hr hg u S
    (words 0) (words 1) (words 2) (fun i lo hi => empty _ ((by decide : ∀ i : Fin 11,
      3 ≤ i → i < 10 → 5 ≤ (stageRowFactors i).val) i lo hi))
  let A := {S with R := Function.update S.R (r 6) (word p)}
  have keep (i : Fin 14) (h : i ≠ 6) : A.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
  obtain ⟨y',m,same,price,second⟩ := seedProduct_exec body (stageExteriorFactors.trans r) p v.afterD 1 hp hd
    (by decide) y A (Function.update_self ..) ((keep _ (by decide)).trans (words 3))
    ((keep _ (by decide)).trans one) (fun i lo hi => by
      obtain ⟨ne,high⟩ := (by decide : ∀ i : Fin 11, 3 ≤ i → i < 10 →
        stageExteriorFactors i ≠ 6 ∧ 5 ≤ (stageExteriorFactors i).val) i lo hi
      exact (keep _ ne).trans (empty _ high))
  simp only [Nat.mul_one] at second price
  let B := {A with R := Function.update A.R (r 5) (word W)}
  obtain ⟨z,last,_,clear⟩ := bclear_exec body (r 6) y' B
  have len : (B.R (r 6)).length = p.size := by simp [B,A,word,r.injective.eq_iff,length_binSyms]
  rw [len] at clear
  have clean : Function.update B.R (r 6) [] = Function.update S.R (r 5) (word W) := by
    dsimp only [B,A]
    rw [Function.update_comm (r.injective.ne (by decide : (5 : Fin 14) ≠ 6)),Function.update_idem,
      ← empty 6 (by decide),Function.update_eq_self]
  rw [clean] at clear
  refine ⟨z,k+(m+(2*p.size+2)),last.trans (same.trans user),?_,Exec.seq first (Exec.seq second clear)⟩
  have le : p ≤ W := Nat.le_mul_of_pos_right _ hd
  have digits : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
  change k ≤ 432*p at cost
  change m ≤ 432*W at price
  omega

/-- Inputs in the parent's six headers and scalar bank. Output and scratch
occupy the stage's existing fourteen dimension registers. -/
def exteriorLayout : Fin 14 ↪ Fin 41 ⊕ Fin 14 :=
  ⟨![.inl 0,.inl 1,.inl 4,.inl 5,.inl 34,.inr 10,.inr 0,
    .inr 3,.inr 4,.inr 5,.inr 6,.inr 7,.inr 8,.inr 9],by decide⟩

def exteriorBank {J G : ℕ} (frame : Fin 41 ↪ Fin J) : Fin 14 ↪ Fin (J+14+G) :=
  (((exteriorLayout.trans (frame.sumMap (Function.Embedding.refl _))).trans
    finSumFinEquiv.toEmbedding).trans (Fin.castAddEmb G))

theorem exteriorBank_exec {J G : ℕ} (body : P → Pr P (J+14+G) Q prime U) (frame : Fin 41 ↪ Fin J)
    (row : RecursiveInterchangeLayout.Descriptor) (pos : row.Positive)
    (u : HS (J+14+G) Q prime U) (S : Stacks (J+14+G) prime) :
    let ext := fun i : Fin 14 => (i.natAdd J).castAdd G
    let parent := fun i => ((frame i).castAdd 14).castAdd G
    ∀ tail, row.beforeRows*row.rows*row.between*row.afterD = tail →
    (∀ i : Fin 6, S.R (parent (i.castAdd 35)) = (M8.RevMachine.Routines.hdr row i).map bitSymbol) →
    S.R (parent 34) = binSyms 1 1 → S.R (ext 10) = [] → S.R (ext 0) = [] →
    (∀ j : Fin 7, S.R (ext ((j.natAdd 3).castAdd 4)) = []) →
    ∃ z F t, z.user = u.user ∧ t ≤ 868*tail ∧ Exec body (stageExterior (exteriorBank frame))
      (mk u S) t (mk z F) ∧ F.L = S.L ∧ F.R (ext 10) = binSyms tail.size tail ∧
      ∀ j, j ≠ ext 10 → F.R j = S.R j := by
  intro ext parent tail eq fields unit output partialFree scratch
  subst tail
  obtain ⟨z,t,user,time,exec⟩ := stageExterior_exec body (exteriorBank frame) row pos u S (by
    intro i
    fin_cases i <;> first | exact fields 0 | exact fields 1 | exact fields 4 | exact fields 5) unit (by
    intro i h
    fin_cases i <;> first | contradiction | omega | exact output | exact partialFree | (first | exact scratch 0 | exact scratch 1 | exact scratch 2 | exact scratch 3 | exact scratch 4 | exact scratch 5 | exact scratch 6))
  exact ⟨z,_,t,user,time,exec,rfl,Function.update_self ..,fun j h => Function.update_of_ne h _ _⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
