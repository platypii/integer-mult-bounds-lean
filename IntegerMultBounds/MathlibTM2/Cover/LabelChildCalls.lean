module

public import IntegerMultBounds.MathlibTM2.Cover.LabelChildMerge

/-! Call the two children on consecutive prefixes and merge their transformed records. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelChildCalls
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def program (r : Fin 12 ↪ Fin T) (good bad : P) : Pr P T Q A U :=
  .seq (.call good) (.seq (.call bad) (LabelChildMerge.program ((Fin.castLEEmb (by decide)).trans r)))

/-- A child consumes equally many directory and payload records, preserving the remaining
inputs and prepending its result to the output register. -/
def Child (body : P → Pr P T Q A U) (proc : P) (dir src count out : Fin T) (ids : List ℕ)
    (entry data result : ℕ → List (Fin (A+4))) (cost : ℕ) :=
  ∀ (u : HS T Q A U) (S : Stacks T A) (a b : List (Fin (A+4))),
    (S.R count).length = ids.length → S.R dir = ids.flatMap entry ++ a →
    S.R src = ids.flatMap data ++ b →
    ∃ z n, z.user = u.user ∧ n ≤ cost ∧ Exec body (body proc) (mk u S) n
      (mk z {S with R := Function.update (Function.update (Function.update S.R dir a) src b) out (ids.flatMap result ++ S.R out)})

theorem calls_exec (r : Fin 12 ↪ Fin T) (g b : P) (ids : List ℕ) (keep : ℕ → Bool)
    (entry data good bad : ℕ → List (Fin (A+4))) (w cg cb : ℕ)
    (hg : ∀ i ∈ ids.filter keep, (good i).length = w)
    (hb : ∀ i ∈ ids.filter (fun k => !(keep k)), (bad i).length = w)
    (u : HS T Q A U) (S : Stacks T A) (dirTail dataTail : List (Fin (A+4))) :
    let G := ids.filter keep
    let B := ids.filter (fun k => !(keep k))
    Child body g (r 8) (r 9) (r 10) (r 0) G entry data good cg →
    Child body b (r 8) (r 9) (r 11) (r 1) B entry data bad cb →
    S.R (r 8) = G.flatMap entry ++ B.flatMap entry ++ dirTail →
    S.R (r 9) = G.flatMap data ++ B.flatMap data ++ dataTail →
    (S.R (r 10)).length = G.length → (S.R (r 11)).length = B.length →
    S.R (r 3) = (ids.map keep).map bitSymbol → (S.R (r 2)).length = w →
    (∀ i ∈ ([4,5,6] : List (Fin 12)), S.R (r i) = []) →
    let result := ids.flatMap fun j => if keep j then good j else bad j
    ∃ z n, z.user = u.user ∧ n ≤ cg+cb+ids.length*(6*w+10)+10 ∧
      Exec body (program r g b) (mk u S) n (mk z {S with R := Function.update (Function.update (Function.update S.R (r 8) dirTail) (r 9) dataTail) (r 7) (result ++ S.R (r 7))}) := by
  intro G B runG runB dir src lenG lenB mask width fresh result
  obtain ⟨u₁,n₁,h₁,c₁,e₁⟩ := runG u S (B.flatMap entry ++ dirTail) (B.flatMap data ++ dataTail)
    lenG (by simpa [List.append_assoc] using dir) (by simpa [List.append_assoc] using src)
  let M : Stacks T A := {S with R := Function.update (Function.update (Function.update S.R (r 8)
    (B.flatMap entry ++ dirTail)) (r 9) (B.flatMap data ++ dataTail)) (r 0) (G.flatMap good ++ S.R (r 0))}
  obtain ⟨u₂,n₂,h₂,c₂,e₂⟩ := runB u₁ M dirTail dataTail (by simpa [M] using lenB)
    (by simp [M]) (by simp [M])
  let H : Stacks T A := {M with R := Function.update (Function.update (Function.update M.R (r 8) dirTail) (r 9) dataTail) (r 1) (B.flatMap bad ++ M.R (r 1))}
  let merge := (Fin.castLEEmb (by decide : 8 ≤ 12)).trans r
  obtain ⟨z,t,hz,ct,e₃⟩ := LabelChildMerge.children_exec (body := body) merge ids keep good bad w hg hb
    (S.R (r 0)) (S.R (r 1)) u₂ H (by simp [H,M,merge,G]) (by simp [H,M,merge,B])
    (by simpa [H,M,merge] using mask) (by simpa [H,M,merge] using width) (by
      intro i hi; apply Eq.trans _ (fresh (Fin.castLE (by decide) i) _)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> simp [H,M,merge]
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide)
  refine ⟨z,_,hz.trans (h₂.trans h₁),by omega,(Exec.seq (Exec.call e₁) (Exec.seq (Exec.call e₂) e₃)).cast rfl ?_⟩
  apply congrArg (mk z)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h7 : k = r 7
  · subst k; simp [merge,H,M,result]
  by_cases h0 : k = r 0
  · subst k; simp [merge]
  by_cases h1 : k = r 1
  · subst k; simp [merge]
  by_cases h8 : k = r 8 <;> by_cases h9 : k = r 9 <;> simp [merge,H,M,Function.update_apply,h7,h0,h1,h8,h9]

end
end IntegerMultBounds.MathlibTM2.Cover.LabelChildCalls
