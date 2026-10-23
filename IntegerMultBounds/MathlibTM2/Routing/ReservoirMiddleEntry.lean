module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMiddleLookup
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite

/-! One restoring row call for local-table generation. The existing serializer
and stack move emit a reversed frame for the shared scanner's accumulator. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def middleEntryCore (j : Fin 33) : Fin 38 := j.castAdd 5

def reservoirMiddleEntryProgram : Pr P 38 Q A U :=
  .seq (bcopy 0 33 36 37)
    (.seq (embProg middleEntryCore Empty.elim (reservoirMiddleLookupProgram (P := Empty)))
      (.seq (configurationWrite 34 36 37 [33, 0])
        (.seq (coordinateReplaceProgram 33 0 36 37) (moveR 34 35 id))))

variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)

theorem reservoirMiddleEntry_exec (body : P → Pr P 38 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) (q : Fin (n - 3 * w))
    (v : HS 38 Q A U) (S : Stacks 38 A)
    (hbank : ∀ j, S.R (middleEntryCore j) = reservoirMiddleLookupBank n H hfit w hw k L mate q.val j)
    (hblank : ∀ j : Fin 38, j = 33 ∨ j = 34 ∨ j = 36 ∨ j = 37 → S.R j = []) :
    ∃ (v' : HS 38 Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ n * (30 * L + 39) + 650 * L + 763 ∧
      Exec body reservoirMiddleEntryProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R 35 ((matchingEntryWord L q.val (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val).reverse ++ S.R 35) }) := by
  let localMate := reservoirMiddleMatching n H hfit w hw k mate hinv hfix q
  have hq : S.R 0 = binSyms L q.val := by
    simpa [middleEntryCore, reservoirMiddleLookupBank] using hbank 0
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body (a := 0) (c := 33) (t₁ := 36) (t₂ := 37)
    (by decide) v S (hblank 36 (by simp)) (hblank 37 (by simp))
  rw [hq, hblank 33 (by simp), List.append_nil, length_binSyms] at he₁
  let G : Stacks 38 A := { S with R := Function.update S.R 33 (binSyms L q.val) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := reservoirMiddleLookup_embedded_exec n H hfit w hw k L body
    middleEntryCore (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 38 => x.val) h)) hn mate hinv hfix q v₁ G
    (by intro j
        have hj : middleEntryCore j ≠ 33 := by have := j.isLt; simp [middleEntryCore, Fin.ext_iff]; omega
        simpa [G, hj] using hbank j)
  let J : Stacks 38 A := { G with R := Function.update G.R 0 (binSyms L localMate.val) }
  obtain ⟨v₃, hu₃, he₃⟩ := configurationWrite_exec body 34 36 37 (by decide) [33, 0]
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> decide) v₂ J
    (by simp [J, G, hblank 36 (by simp)]) (by simp [J, G, hblank 37 (by simp)])
  have hcost : configurationWriteCost J.R [33, 0] = 12 * L + 15 := by
    simp [configurationWriteCost, J, G]; omega
  have hword : configurationWords ([33, 0].map J.R) ++ J.R 34 =
      matchingEntryWord L q.val localMate.val := by
    simp [J, G, configurationWords, matchingEntryWord, hblank 34 (by simp)]
  rw [hcost, hword] at he₃
  let C : Stacks 38 A := { J with R := Function.update J.R 34 (matchingEntryWord L q.val localMate.val) }
  let B : Stacks 38 A := { C with R := Function.update C.R 33 [] }
  obtain ⟨v₄, hu₄, he₄⟩ := coordinateReplace_exec body (33 : Fin 38) 0 36 37 (by decide)
    L (binSyms L q.val) (length_binSyms L _) v₃ B
    (by simp [B, C, J]) (by simp [B])
    (by simp [B, C, J, G, hblank 36 (by simp)])
    (by simp [B, C, J, G, hblank 37 (by simp)])
  have hstart : { B with R := Function.update B.R 33 (binSyms L q.val) } = C := by
    simp [B, C, J, G]
  rw [hstart] at he₄
  let D : Stacks 38 A := { B with R := Function.update B.R 0 (binSyms L q.val) }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body (34 : Fin 38) 35 (by decide) id v₄ D
  have hd : D.R 34 = matchingEntryWord L q.val localMate.val := by simp [D, B, C]
  have hf : movedR D.R 34 35 id (D.R 34) = Function.update S.R 35
      ((matchingEntryWord L q.val localMate.val).reverse ++ S.R 35) := by
    funext j
    by_cases h35 : j = 35
    · subst j; simp [movedR, D, B, C, J, G]
    by_cases h34 : j = 34
    · subst j; simp [movedR, hblank 34 (by simp)]
    by_cases h33 : j = 33
    · subst j; simp [movedR, D, B, hblank 33 (by simp)]
    by_cases h0 : j = 0
    · subst j; simp [movedR, D, hq]
    · simp [movedR, D, B, C, J, G, h35, h34, h33, h0]
  rw [hf, hd] at he₅
  have hlen : (matchingEntryWord (A := A) L q.val localMate.val).length = 2 * L + 2 := by
    simp [matchingEntryWord]; omega
  rw [hlen] at he₅
  exact ⟨v₅, (6 * L + 6) + (m₂ + ((12 * L + 15) + ((10 * L + 10) + (2 * (2 * L + 2) + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩

end IntegerMultBounds.MathlibTM2.Routing
