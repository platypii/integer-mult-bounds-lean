module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCounter

/-! Generate consecutive directory labels with a tape-counted radix scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryLoop
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open RadixDigits RadixCounterData Host Node LabelDirectoryCounter

variable {T Q q : ℕ} {P U : Type} {body : P → Pr P T Q q U}

private theorem advance_succ (hq : 2 ≤ q) (j : ℕ) (xs : List (Fin q)) :
    advance hq (j+1) xs = increment hq (advance hq j xs) := by
  induction j generalizing xs with
  | zero => rfl
  | succ j ih => exact ih (increment hq xs)

def words (hq : 2 ≤ q) (xs : List (Fin q)) (n : ℕ) :=
  (List.range n).flatMap fun j => (advance hq j xs).map digitSymbol

private theorem words_succ (hq : 2 ≤ q) (xs : List (Fin q)) (j : ℕ) :
    words hq xs (j+1) = words hq xs j ++ (advance hq j xs).map digitSymbol := by
  simp [words,List.range_succ]

/-- Counter, reverse output, successor scratch, width, temporary, count and saved count. -/
def program (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T) : Pr P T Q q U :=
  eachSym (r 5) (r 6) (tick hq (fun _ => r 0) ![r 1,r 2] (r 3) (r 3) (r 4))

theorem loop_exec (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T) (xs : List (Fin q)) (hx : 0 < xs.length)
    (u : HS T Q q U) (S : Stacks T q) (hin : S.R (r 0) = xs.map digitSymbol)
    (hw : (S.R (r 3)).length = xs.length) (hs : S.R (r 2) = []) (ht : S.R (r 4) = []) :
    let N := (S.R (r 5)).length
    ∃ v R n, v.user = u.user ∧ n ≤ N*(7*xs.length+13)+2 ∧
      Exec body (program hq r) (mk u S) n (mk v {S with R := R}) ∧
      R (r 5) = [] ∧ R (r 6) = (S.R (r 5)).reverse ++ S.R (r 6) ∧
      ∀ k, k ≠ r 5 → k ≠ r 6 → R k = Function.update (Function.update S.R (r 1)
        ((words hq xs N).reverse ++ S.R (r 1))) (r 0) ((advance hq N xs).map digitSymbol) k := by
  let Ψ (j : ℕ) := Function.update (Function.update S.R (r 1)
    ((words hq xs j).reverse ++ S.R (r 1))) (r 0) ((advance hq j xs).map digitSymbol)
  have layout : AutoLayout (fun _ : Fin 1 => r 0) ![r 1,r 2] (r 3) (r 3) (r 4) := by
    constructor
    · exact fun _ _ _ => Subsingleton.elim _ _
    · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
    · intro i j; fin_cases j <;> simp
    · intro i; simp
    · intro i; simp
    · intro j; fin_cases j <;> simp
    · intro j; fin_cases j <;> simp
    · simp
    · intro i; simp
  apply eachSym_exec (body := body) (a := r 5) (t := r 6) (Ψ := Ψ) (c := 7*xs.length+10) (by simp) u S
  · intro j hj v M _ hM
    have slot (i : Fin 7) (h5 : i ≠ 5) (h6 : i ≠ 6) : M.R (r i) = Ψ j (r i) :=
      hM _ (by simpa) (by simpa)
    obtain ⟨v',n,hu,hn,he⟩ := tick_exec (body := body) hq layout (advance hq j xs)
      (by simpa using hx) v M (by simpa [slot 3 (by decide) (by decide),Ψ] using hw)
      (by simpa [slot 4 (by decide) (by decide),Ψ] using ht)
      (by simpa [slot 2 (by decide) (by decide),Ψ] using hs)
      (by simp [slot 0 (by decide) (by decide),Ψ])
    refine ⟨v',_,n,hu,by simpa using hn,he,by simp,by simp,?_⟩
    intro k h5 h6
    by_cases h0 : k = r 0
    · subst k; simp [Ψ,advance_succ]
    by_cases h1 : k = r 1
    · subst k; simp [Ψ,words_succ,slot 1 (by decide) (by decide),List.append_assoc]
    simpa [Ψ,h0,h1] using hM k h5 h6
  · intro k _ _
    by_cases h0 : k = r 0
    · subst k; simpa [Ψ,advance] using hin
    by_cases h1 : k = r 1
    · subst k; simp [Ψ,words]
    simp [Ψ,h0,h1]

/-- Restore the count and prepend the directory words to the destination in physical order. -/
def write (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T) (out : Fin T) : Pr P T Q q U :=
  .seq (program hq r) (.seq (moveR (r 6) (r 5) id) (moveR (r 1) out id))

theorem write_exec (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T) (out : Fin T) (apart : ∀ i, out ≠ r i)
    (xs : List (Fin q)) (hx : 0 < xs.length) (u : HS T Q q U) (S : Stacks T q)
    (hin : S.R (r 0) = xs.map digitSymbol) (hw : (S.R (r 3)).length = xs.length)
    (hf : ∀ i ∈ ([1,2,4,6] : List (Fin 7)), S.R (r i) = []) :
    let N := (S.R (r 5)).length
    ∃ v n, v.user = u.user ∧ n ≤ N*(9*xs.length+15)+6 ∧
      Exec body (write hq r out) (mk u S) n (mk v {S with R := Function.update (Function.update S.R (r 0) ((advance hq N xs).map digitSymbol)) out (words hq xs N ++ S.R out)}) := by
  intro N
  obtain ⟨v,R,n,hu,hn,he,h5,h6,hr⟩ := loop_exec (body := body) hq r xs hx u S hin hw
    (hf 2 (by simp)) (hf 4 (by simp))
  rw [hf 6 (by simp),List.append_nil] at h6
  let M : Stacks T q := {S with R := R}
  let M' : Stacks T q := {M with R := movedR R (r 6) (r 5) id (R (r 6))}
  obtain ⟨v',hu',he'⟩ := moveR_exec body (r 6) (r 5) (by simp) id v M
  obtain ⟨v'',hu'',he''⟩ := moveR_exec body (r 1) out (apart 1).symm id v' M'
  have acc : M'.R (r 1) = (words hq xs N).reverse := by
    simp [M',movedR,hr _ (by simp : r 1 ≠ r 5) (by simp : r 1 ≠ r 6),hf 1 (by simp),N]
  have dst : M'.R out = S.R out := by simp [M',movedR,apart,hr out (apart 5) (apart 6)]
  have len (j : ℕ) : (words hq xs j).length = j*xs.length := by
    induction j with
    | zero => simp [words]
    | succ j ih => simp [words_succ,ih,Nat.succ_mul]
  refine ⟨v'',_,hu''.trans (hu'.trans hu),?_,(Exec.seq he (Exec.seq he' he'')).cast rfl ?_⟩
  · simp only [M,h6,List.length_reverse,acc,len]
    dsimp [N] at *
    nlinarith
  · apply congrArg (mk v'')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases ho : k = out
    · subst k; simp [movedR,acc,dst]
    by_cases h1 : k = r 1
    · subst k; simp [movedR,ho,hf 1 (by simp)]
    by_cases hk5 : k = r 5
    · subst k; simp [movedR,M',ho,h6,h5]
    by_cases hk6 : k = r 6
    · subst k; simp [movedR,M',ho,hf 6 (by simp)]
    simp [movedR,M',ho,h1,hk5,hk6,hr k hk5 hk6,Function.update_apply,N]


open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)

/-- Starting at zero gives exactly the directory entries of the outermost level. -/
theorem root_words (m w n : ℕ) :
    words prime_prime.two_le (zeros prime_prime.two_le (w*(m*m))) n =
      (List.range n).flatMap (LabelDirectory.entry (fun _ => []) m w) := by
  rfl

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryLoop
