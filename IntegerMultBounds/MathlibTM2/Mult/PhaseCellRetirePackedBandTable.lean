module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePackedBandStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Retire the packed boundary table in reverse column order and preserve its borrowed tail. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def retirePackedBandTable : Pr P 224 Q A U :=
  .seq (ucopy 116 152 135) (countedLoop 152 retirePackedBandStep)

def retirePackedBandTableCost (N W w : ℕ) : ℕ :=
  (4*N+4)+(Finset.range N).sum (fun j => retirePackedBandStepCost (N-(j+1)) W N w+3)+2

theorem retirePackedBandTable_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hW : (S.R 190).length = W) (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = bandTableWords A w B W columns 0++tail)
    (hfresh : ∀ i ∈ ([152,151,131,134,135,136,137,138] : List (Fin 224)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retirePackedBandTableCost B.card W w ∧
      Exec body retirePackedBandTable (mk v S) m
        (mk v' {S with R := Function.update S.R 132 tail}) := by
  let N := B.card
  let page (j : ℕ) := bandTableWords A w B W (columns.take (N-j)) 0++tail
  let Inv (j : ℕ) (X : Stacks 224 A) := X.inp = S.inp ∧ X.out = S.out ∧ X.L = S.L ∧
    ∀ i : Fin 224, i ≠ 152 → X.R i = (Function.update S.R 132 (page j)) i
  have hstable : ∀ j X xs, Inv j X → Inv j {X with R := Function.update X.R 152 xs} := by
    intro j X xs hI
    refine ⟨hI.1,hI.2.1,hI.2.2.1,?_⟩
    intro i hi
    simpa only [Function.update_of_ne hi] using hI.2.2.2 i hi
  have hstep : ∀ j < N, ∀ (vi : HS 224 Q A U) X, Inv j X → (X.R 152).length = N-(j+1) →
      ∃ v' X' m, v'.user = vi.user ∧ m ≤ retirePackedBandStepCost (N-(j+1)) W N w ∧
        Exec body retirePackedBandStep (mk vi X) m (mk v' X') ∧ X'.R 152 = X.R 152 ∧ Inv (j+1) X' := by
    intro j hj vi X hI hc
    let n := N-(j+1)
    have hn : n < columns.length := by dsimp [n,N] at *; omega
    have htake : columns.take (N-j) = columns.take n++[columns[n]] := by
      have heq : N-j = n+1 := by omega
      rw [heq,List.take_succ_eq_append_getElem hn]
    have hpage : page j = bandColumnWords A w B W n columns[n]++page (j+1) := by
      dsimp only [page]
      rw [htake,bandTableWords_append]
      simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt hn),Nat.zero_add,List.append_assoc]
      rfl
    have hframe (i : Fin 224) (hi : i ≠ 152) (hi132 : i ≠ 132) : X.R i = S.R i := by
      simpa only [Function.update_of_ne hi132] using hI.2.2.2 i hi
    obtain ⟨v₁,m,hu,hm,he⟩ := retirePackedBandStep_exec (body := body) n W N w
      (bandColumnWords A w B W n columns[n]) (page (j+1)) vi X hc
      (by rw [hframe 190 (by decide) (by decide)]; exact hW)
      (by rw [hframe 116 (by decide) (by decide)]; exact hN)
      (by rw [hframe 160 (by decide) (by decide)]; exact hw)
      (by have hh := hI.2.2.2 132 (by decide); simpa only [Function.update_self,hpage] using hh)
      (by simp [bandColumnWords,foldedBandRows,foldedBandIndices,N]) (by
        intro i hi
        have hi152 : i ≠ 152 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hi132 : i ≠ 132 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hframe i hi152 hi132]
        exact hfresh i (List.mem_cons_of_mem 152 hi))
    refine ⟨v₁,{X with R := Function.update X.R 132 (page (j+1))},m,hu,hm,he,by simp,?_⟩
    refine ⟨hI.1,hI.2.1,hI.2.2.1,?_⟩
    intro i hi152
    by_cases hi132 : i = 132
    · subst i; simp
    · simpa only [Function.update_of_ne hi132] using hframe i hi152 hi132
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 116) (b := 152) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 152 (List.replicate N tick)}
  have he₁' : Exec body (ucopy 116 152 135) (mk v S) (4*N+4) (mk v₁ S₁) := by
    simpa [S₁,hN,hfresh 152 (by simp),N] using he₁
  have hInv : Inv 0 S₁ := by
    refine ⟨rfl,rfl,rfl,?_⟩
    intro i hi152
    have hp : page 0 = S.R 132 := by simp [page,N,← hlen,← hsource]
    simp [S₁,hi152,hp]
  obtain ⟨v₂,S₂,m₂,hu₂,hm₂,he₂,h152,hI₂⟩ := countedLoop_exec_remaining_costs (body := body)
    152 retirePackedBandStep N (fun j => retirePackedBandStepCost (N-(j+1)) W N w)
    Inv hstable hstep v₁ S₁ (by simp [S₁]) hInv
  refine ⟨v₂,(4*N+4)+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,
    (Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext hI₂.1 hI₂.2.1 hI₂.2.2.1 ?_
  funext i
  by_cases hi152 : i = 152
  · subst i; simpa [hfresh 152 (by simp)] using h152
  · simpa [page,bandTableWords] using hI₂.2.2.2 i hi152

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
