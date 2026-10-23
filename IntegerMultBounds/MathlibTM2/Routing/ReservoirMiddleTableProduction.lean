module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMiddleTableScan
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Produce the complete local matching table from the physical table and live
binary middle width. Counter selectors and unary count are generated and erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def middleProductionCounter (j : Fin 5) : Fin 44 := j.castAdd 39

def middleProductionScan (j : Fin 42) : Fin 44 := j.castAdd 2

def reservoirMiddleTableProductionProgram : Pr P 44 Q A U :=
  .seq (toUnary 43 42 1 2 3)
    (.seq (counterSourceGenerateProgram middleProductionCounter 42 40 35 39 33)
      (.seq (bclear 0)
        (.seq (embProg middleProductionScan Empty.elim (reservoirMiddleTableScanFinishProgram (P := Empty)))
          (.seq (bclear 39) (.seq (bclear 42) (bcopy 25 0 1 2))))))

variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)

def reservoirMiddleProductionBank (mate : Fin n → Fin n) (j : Fin 44) : List (Fin (A + 4)) :=
  if h : j.val < 33 then reservoirMiddleLookupBank n H hfit w hw k L mate 0 ⟨j.val, h⟩
  else if j = 43 then binSyms L (n - 3 * w) else []

/-- The physical table is the only bank field that depends on the matching. -/
theorem reservoirMiddleProductionBank_mate_congr (mate mate' : Fin n → Fin n)
    (j : Fin 44) (hj : j ≠ 21) :
    reservoirMiddleProductionBank (A := A) n H hfit w hw k L mate j =
      reservoirMiddleProductionBank n H hfit w hw k L mate' j := by
  unfold reservoirMiddleProductionBank
  split
  · rename_i hlt
    have h21 : (⟨j.val, hlt⟩ : Fin 33) ≠ 21 := by
      intro he
      exact hj (Fin.ext (congrArg (fun x : Fin 33 => x.val) he))
    simp only [reservoirMiddleLookupBank, ite_eq_right h21]
  · rfl

theorem reservoirMiddleTableProduction_exec (body : P → Pr P 44 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (v : HS 44 Q A U) (S : Stacks 44 A)
    (hbank : S.R = reservoirMiddleProductionBank n H hfit w hw k L mate) :
    ∃ (v' : HS 44 Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (n - 3 * w) * (n * (30 * L + 39) + 682 * L + 842) + 35 * L + 46 ∧
      Exec body reservoirMiddleTableProductionProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R 34 (matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate (reservoirMiddleMatching n H hfit w hw k mate hinv hfix)))) }) := by
  let W := n - 3 * w
  let ticks := List.replicate W (IntegerMultBounds.MathlibTM2.Node.tick (A := A))
  let selectors := counterSourceWord (A := A) L 0 W
  let table := matchingEntryWords (A := A) L (matchingTableEntries W
    (matchingMateCoordinate (reservoirMiddleMatching n H hfit w hw k mate hinv hfix)))
  have hinit0 : S.R 0 = binSyms L 0 := by simp [hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank]
  have hzero : S.R 25 = binSyms L 0 := by simp [hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank]
  have hblank (j : Fin 44) (hj : 33 ≤ j.val ∧ j.val < 43) : S.R j = [] := by
    have hj43 : j ≠ 43 := by intro he; subst j; norm_num at hj
    simp [hbank, reservoirMiddleProductionBank, show ¬j.val < 33 by omega, hj43]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := (43 : Fin 44)) (z := 42) (w := 1) (t := 2) (t₂ := 3)
    (by decide) (by dsimp [W]; omega : W < 2 ^ L) v S
    (by simp [hbank, reservoirMiddleProductionBank, W])
    (by simp [hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank])
    (by simp [hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank])
    (by simp [hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank])
  rw [hblank 42 (by decide), List.append_nil] at he₁
  let F : Stacks 44 A := { S with R := Function.update S.R 42 ticks }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := counterSourceGenerate_exec body middleProductionCounter
    (by intro i j he; exact Fin.ext (congrArg (fun x : Fin 44 => x.val) he)) 42 40 35 39 33
    (by decide) (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> decide) L 0 ticks v₁ F
    (by simp [F]) (by simpa [F, middleProductionCounter] using hinit0)
    (by simp [F, hblank 40 (by decide)]) (by simp [F, hblank 35 (by decide)])
    (by simp [F, hblank 33 (by decide)])
    (by intro j hj; fin_cases j <;> simp_all [F, middleProductionCounter, reservoirMiddleProductionBank, reservoirMiddleLookupBank])
  have hticks : ticks.length = W := List.length_replicate ..
  rw [hticks, show F.R 39 = [] by simp [F, hblank 39 (by decide)], List.append_nil] at he₂
  rw [hticks] at hm₂
  let G : Stacks 44 A := { F with R := Function.update F.R 39 selectors }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (0 : Fin 44) v₂ G
  have hg0 : (G.R 0).length = L := by simp [G, F, hinit0]
  rw [hg0] at he₃
  let B : Stacks 44 A := { G with R := Function.update G.R 0 [] }
  have ready : MiddleTableScanReady n H hfit w hw k L mate (embStk middleProductionScan B) := by
    constructor
    · intro j hj
      let i : Fin 44 := j.castAdd 11
      change B.R i = reservoirMiddleLookupBank n H hfit w hw k L mate 0 j
      have hi33 : i.val < 33 := j.isLt
      have hi0 : i ≠ 0 := by
        intro he
        apply hj
        exact Fin.ext (congrArg (fun x : Fin 44 => x.val) he)
      have hi39 : i ≠ 39 := by intro he; have := congrArg (fun x : Fin 44 => x.val) he; omega
      have hi42 : i ≠ 42 := by intro he; have := congrArg (fun x : Fin 44 => x.val) he; omega
      simp only [B, G, F, Function.update_of_ne hi0, Function.update_of_ne hi39, Function.update_of_ne hi42]
      rw [hbank]
      simp only [reservoirMiddleProductionBank, dite_eq_left hi33]
      rfl
    · intro j hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [embStk, middleProductionScan, B, G, F, hbank, reservoirMiddleProductionBank]
  let smallBody : Empty → Pr Empty 42 Q A U := Empty.elim
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := reservoirMiddleTableFromSelectors_exec n H hfit w hw k L smallBody
    hn mate hinv hfix (embDn middleProductionScan v₃) (embStk middleProductionScan B) ready
    (by simp [embStk, middleProductionScan, B, G, selectors, W])
    (by simp [embStk, middleProductionScan, B, G, F, hblank 40 (by decide)])
    (by simp [embStk, middleProductionScan, B, G, F, hblank 35 (by decide)])
  obtain ⟨v₅, hu₅, he₅⟩ := exec_emb_stream middleProductionScan
    (by intro i j he; exact Fin.ext (congrArg (fun x : Fin 44 => x.val) he)) Empty.elim smallBody body
    (by intro f; exact f.elim) reservoirMiddleTableScanFinishProgram v₃ B v₄ m₄ 34 table he₄
  let C : Stacks 44 A := { B with R := Function.update B.R 34 table }
  obtain ⟨v₆, hu₆, _, he₆⟩ := bclear_exec body (39 : Fin 44) v₅ C
  have hc39 : (C.R 39).length = W * (L + 3) := by
    simp [C, B, G, selectors, counterSourceWord_length]
  rw [hc39] at he₆
  let D : Stacks 44 A := { C with R := Function.update C.R 39 [] }
  obtain ⟨v₇, hu₇, _, he₇⟩ := bclear_exec body (42 : Fin 44) v₆ D
  have hd42 : (D.R 42).length = W := by simp [D, C, B, G, F, hticks]
  rw [hd42] at he₇
  let E : Stacks 44 A := { D with R := Function.update D.R 42 [] }
  obtain ⟨v₈, hu₈, he₈⟩ := bcopy_exec body (a := (25 : Fin 44)) (c := 0) (t₁ := 1) (t₂ := 2)
    (by decide) v₇ E
    (by simp [E, D, C, B, G, F, hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank])
    (by simp [E, D, C, B, G, F, hbank, reservoirMiddleProductionBank, reservoirMiddleLookupBank])
  have he25 : E.R 25 = binSyms L 0 := by simp [E, D, C, B, G, F, hzero]
  have he0 : E.R 0 = [] := by simp [E, D, C, B]
  rw [he25, he0, List.append_nil, length_binSyms] at he₈
  have hfinal : Function.update E.R 0 (binSyms L 0) = Function.update S.R 34 table := by
    funext j
    by_cases h0 : j = 0
    · subst j; simp [hinit0]
    by_cases h39 : j = 39
    · subst j; simp [E, D, hblank 39 (by decide)]
    by_cases h42 : j = 42
    · subst j; simp [E, hblank 42 (by decide)]
    by_cases h34 : j = 34
    · subst j; simp [E, D, C]
    · simp [E, D, C, B, G, F, h0, h39, h42, h34]
  rw [hfinal] at he₈
  refine ⟨v₈, m₁ + (m₂ + ((2 * L + 2) + (m₄ + ((2 * (W * (L + 3)) + 2) + ((2 * W + 2) + (6 * L + 6)))))),
    hu₈.trans (hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))))), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₅ (Exec.seq he₆ (Exec.seq he₇ he₈)))))⟩
  dsimp only [counterSourceIterationCost] at hm₂
  dsimp only [W] at *
  nlinarith

end IntegerMultBounds.MathlibTM2.Routing
