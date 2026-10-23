module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirClassTableProduction
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMiddleTableProduction

/-! Original matching table to local reservoir-class table, with the intermediate
physical class table generated and erased inside one fixed program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def classLocalClassRegisters (j : Fin 13) : Fin 57 :=
  if j = 11 then 21 else ⟨44 + j.val, by have := j.isLt; omega⟩

def classLocalMiddleRegisters (j : Fin 44) : Fin 57 := j.castAdd 13

theorem classLocalClassRegisters_injective : Function.Injective classLocalClassRegisters := by decide +kernel

def reservoirClassLocalTableProgram (k : Fin 3) : Pr P 57 Q A U :=
  .seq (embProg classLocalClassRegisters Empty.elim (reservoirClassTableProgram (P := Empty) k))
    (.seq (embProg classLocalMiddleRegisters Empty.elim (reservoirMiddleTableProductionProgram (P := Empty)))
      (bclear 21))

variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)

def reservoirClassLocalMatching (mate : Fin n → Fin n) (hinv : Function.Involutive mate) :
    Fin (n - 3 * w) → Fin (n - 3 * w) :=
  reservoirMiddleMatching n H hfit w hw k
    (matchingClass (routingReservoir n H hfit) mate k)
    (matchingClass_involutive (routingReservoir n H hfit) mate hinv k)
    (fun q hq => matchingClass_fixes (routingReservoir n H hfit) mate
      (routingReservoir_disjoint n H hfit) k q hq)

theorem reservoirClassLocalMatching_involutive (mate : Fin n → Fin n)
    (hinv : Function.Involutive mate) :
    Function.Involutive (reservoirClassLocalMatching n H hfit w hw k mate hinv) :=
  reservoirMiddleMatching_involutive n H hfit w hw k _ _ _

def reservoirClassLocalBank (mate : Fin n → Fin n) (j : Fin 57) : List (Fin (A + 4)) :=
  if h : j.val < 44 then
    Function.update (reservoirMiddleProductionBank n H hfit w hw k L mate) 21 [] ⟨j.val, h⟩
  else if j = 46 then binSyms L (3 * H)
  else if j = 47 then binSyms L (6 * H)
  else if j = 52 then matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate))
  else []

theorem reservoirClassLocalTable_exec (body : P → Pr P 57 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (v : HS 57 Q A U) (S : Stacks 57 A)
    (hbank : S.R = reservoirClassLocalBank n H hfit w hw k L mate) :
    ∃ (v' : HS 57 Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (n - 3 * w) * (n * (30 * L + 39) + 682 * L + 842) + n * (72 * L + 89) + 35 * L + 54 ∧
      Exec body (reservoirClassLocalTableProgram k) (mk v S) steps
        (mk v' { S with R := Function.update S.R 34 (matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate (reservoirClassLocalMatching n H hfit w hw k mate hinv)))) }) := by
  let cls := matchingClass (routingReservoir n H hfit) mate k
  have hcls : Function.Involutive cls := matchingClass_involutive (routingReservoir n H hfit) mate hinv k
  have hfix : ∀ q ∈ routingReservoir n H hfit k, cls q = q :=
    fun q hq => matchingClass_fixes (routingReservoir n H hfit) mate
      (routingReservoir_disjoint n H hfit) k q hq
  let classWord := matchingEntryWords (A := A) L (matchingTableEntries n (matchingMateCoordinate cls))
  let localWord := matchingEntryWords (A := A) L (matchingTableEntries (n - 3 * w)
    (matchingMateCoordinate (reservoirClassLocalMatching n H hfit w hw k mate hinv)))
  let classBody : Empty → Pr Empty 13 Q A U := Empty.elim
  have hclassBank : (embStk classLocalClassRegisters S).R = reservoirClassTableBank n H L mate := by
    funext j
    fin_cases j <;> simp [embStk, classLocalClassRegisters, hbank, reservoirClassLocalBank,
      reservoirClassTableBank]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := reservoirClassTable_exec n H hfit L classBody hn mate k
    (embDn classLocalClassRegisters v) (embStk classLocalClassRegisters S) hclassBank
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream classLocalClassRegisters classLocalClassRegisters_injective
    Empty.elim classBody body (by intro f; exact f.elim) (reservoirClassTableProgram k) v S v₁ m₁ 11 classWord he₁
  let G : Stacks 57 A := { S with R := Function.update S.R 21 classWord }
  have hmiddleBank : (embStk classLocalMiddleRegisters G).R =
      reservoirMiddleProductionBank n H hfit w hw k L cls := by
    funext j
    change G.R (classLocalMiddleRegisters j) = _
    by_cases hj : j = 21
    · subst j
      simp [G, classLocalMiddleRegisters, reservoirMiddleProductionBank, reservoirMiddleLookupBank, classWord]
    have hne : classLocalMiddleRegisters j ≠ 21 := by
      intro he
      exact hj (Fin.ext (congrArg (fun x : Fin 57 => x.val) he))
    rw [show G.R (classLocalMiddleRegisters j) = S.R (classLocalMiddleRegisters j) by simp [G, hne], hbank]
    unfold reservoirClassLocalBank
    rw [dite_eq_left (show (classLocalMiddleRegisters j).val < 44 from j.isLt)]
    change Function.update (reservoirMiddleProductionBank n H hfit w hw k L mate) 21 [] j = _
    rw [Function.update_of_ne hj]
    exact reservoirMiddleProductionBank_mate_congr n H hfit w hw k L mate cls j hj
  let middleBody : Empty → Pr Empty 44 Q A U := Empty.elim
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := reservoirMiddleTableProduction_exec n H hfit w hw k L middleBody
    hn cls hcls hfix (embDn classLocalMiddleRegisters v₂) (embStk classLocalMiddleRegisters G) hmiddleBank
  obtain ⟨v₄, hu₄, he₄⟩ := exec_emb_stream classLocalMiddleRegisters
    (by intro i j he; exact Fin.ext (congrArg (fun x : Fin 57 => x.val) he)) Empty.elim middleBody body
    (by intro f; exact f.elim) reservoirMiddleTableProductionProgram v₂ G v₃ m₃ 34 localWord he₃
  let J : Stacks 57 A := { G with R := Function.update G.R 34 localWord }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec body (21 : Fin 57) v₄ J
  have hlen : (J.R 21).length = n * (2 * L + 2) := by
    simp [J, G, classWord, matchingEntryWords_length, matchingTableEntries]
  have hblank : S.R 21 = [] := by simp [hbank, reservoirClassLocalBank]
  have hfinal : Function.update J.R 21 [] = Function.update S.R 34 localWord := by
    funext j
    by_cases h21 : j = 21
    · subst j; simp [hblank]
    by_cases h34 : j = 34
    · subst j; simp [J, h21]
    · simp [J, G, h21, h34]
  rw [hlen, hfinal] at he₅
  exact ⟨v₅, m₁ + (m₃ + (2 * (n * (2 * L + 2)) + 2)),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by nlinarith,
    Exec.seq he₂ (Exec.seq he₄ he₅)⟩

end IntegerMultBounds.MathlibTM2.Routing
