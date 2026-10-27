module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectWeightKey

/-! Structural traversal of retained pages. Each counted step returns its page to
 the reversed completed stream; one final move restores the original family. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U K : Type} {body : P → Pr P 151 Q A U}

/-- The invariant contains the numerical caller frame and the remaining key count.
The page queues are tracked separately, so no numerical invariant can hide a lost page. -/
theorem weightFamilyLoop_exec (step : Pr P 151 Q A U)
    (page : K → List (Fin (A+4))) (cost : K → ℕ)
    (ready : List K → Stacks 151 A → Prop)
    (tail : List (Fin (A+4)))
    (hstep : ∀ k keys v S, ready (k::keys) S →
      S.R 148 = weightKeyFamily ((k::keys).map page)++tail →
      ∃ v' S' n, v'.user = v.user ∧ v'.flag = keys.head?.isSome ∧
        n ≤ cost k ∧ Exec body step (mk v S) n (mk v' S') ∧
        S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ready keys S' ∧
        S'.R 148 = weightKeyFamily (keys.map page)++tail ∧
        S'.R 150 = (weightKeyPacket (page k)).reverse++S.R 150)
    (keys : List K) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hready : ready keys S)
    (hsource : S.R 148 = weightKeyFamily (keys.map page)++tail)
    (hflag : v.flag = keys.head?.isSome) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ (keys.map (fun k => cost k+1)).sum+1 ∧
      Exec body (.loop (·.flag) step) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ready [] S' ∧
      S'.R 148 = tail ∧
      S'.R 150 = (weightKeyFamily (keys.map page)).reverse++S.R 150 := by
  induction keys generalizing v S with
  | nil =>
    refine ⟨v,S,1,rfl,by simp,Exec.loop_false ?_,rfl,rfl,rfl,hready,?_,?_⟩
    · change v.flag = false
      simpa using hflag
    · simpa [weightKeyFamily] using hsource
    · simp [weightKeyFamily]
  | cons k keys ih =>
    obtain ⟨v₁,S₁,n₁,hu₁,hflag₁,hn₁,he₁,hi₁,ho₁,hl₁,hr₁,hs₁,hc₁⟩ :=
      hstep k keys v S hready hsource
    obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hr₂,hs₂,hc₂⟩ :=
      ih v₁ S₁ hr₁ hs₁ hflag₁
    refine ⟨v₂,S₂,n₁+n₂+1,hu₂.trans hu₁,?_,Exec.loop_true ?_ he₁ he₂,
      hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,hr₂,hs₂,?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · change v.flag = true
      simpa using hflag
    · rw [hc₂,hc₁]
      simp only [List.map_cons,weightKeyFamily_cons,List.reverse_append,List.append_assoc]

/-- Starting with an empty completed stream makes the family reusable after the loop. -/
theorem weightFamilyLoop_restore_exec (step : Pr P 151 Q A U)
    (page : K → List (Fin (A+4))) (cost : K → ℕ)
    (ready : List K → Stacks 151 A → Prop) (tail : List (Fin (A+4)))
    (hstep : ∀ k keys v S, ready (k::keys) S →
      S.R 148 = weightKeyFamily ((k::keys).map page)++tail →
      ∃ v' S' n, v'.user = v.user ∧ v'.flag = keys.head?.isSome ∧
        n ≤ cost k ∧ Exec body step (mk v S) n (mk v' S') ∧
        S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ready keys S' ∧
        S'.R 148 = weightKeyFamily (keys.map page)++tail ∧
        S'.R 150 = (weightKeyPacket (page k)).reverse++S.R 150)
    (keys : List K) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hready : ready keys S) (hsource : S.R 148 = weightKeyFamily (keys.map page)++tail)
    (hcomplete : S.R 150 = []) (hflag : v.flag = keys.head?.isSome) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (keys.map (fun k => cost k+1)).sum+2*(weightKeyFamily (keys.map page)).length+3 ∧
      Exec body (.seq (.loop (·.flag) step) restoreWeightKeyFamily) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R 148 = S.R 148 ∧ S'.R 150 = [] ∧
      ∃ T : Stacks 151 A, ready [] T ∧
        ∀ i : Fin 151, i ≠ 148 → i ≠ 150 → S'.R i = T.R i := by
  obtain ⟨v₁,T,n,hu,hn,he,hi,ho,hl,hr,hs,hc⟩ :=
    weightFamilyLoop_exec step page cost ready tail hstep keys v S hready hsource hflag
  obtain ⟨v₂,hu₂,he₂⟩ := restoreWeightKeyFamily_exec (body := body) v₁ T (keys.map page) tail
    (by simpa [hcomplete] using hc) hs
  refine ⟨v₂,_,_,hu₂.trans hu,by omega,Exec.seq he he₂,hi,ho,hl,?_,?_,?_⟩
  · simpa using hsource.symm
  · simp
  · exact ⟨T,hr,fun i hi148 hi150 => by simp [hi148,hi150]⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
