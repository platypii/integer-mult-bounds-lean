module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloKeyExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloInput

/-! Counted traversal of packed halo length keys. Each iteration restores the
reusable solver state and extends the accuracy contracts on one shared buffer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def packedHaloKeyStep (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq (.act (.pop (.rt 127) (fun v _ => v) .done))
    (.seq (keyedPackedHaloPublish hR hQ) (.act (peekR 127)))

def packedHaloKeyLoopCost (p l s t u target rhsExp a b V : ℕ) (keys : List ℕ) : ℕ :=
  (keys.map (fun L => packedHaloKeyCost p l s t u target rhsExp a b V L+3)).sum+1

theorem packedHaloKeyLoop_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (keys : List ℕ) (hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail suffix E outputTail : List (Fin (A+4))) (done : List ℕ)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
      (executionWidth p l target rhsExp)
      (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E outputTail S)
    (hkeys : S.R 126 = keys.flatMap (binSyms V)++suffix)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hflag : v.flag = keys.head?.isSome)
    (hold : ∀ M ∈ done, PackedCellOutputSpec t p u l target rhsExp M
      (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
      (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
      (fun _ => C) (S.R 132)) :
    ∃ v' F m E', v'.user = v.user ∧
      m ≤ packedHaloKeyLoopCost p l s t u target rhsExp a b V keys ∧
      Exec body (.loop (·.flag) (packedHaloKeyStep hR hQ)) (mk v S) m (mk v' F) ∧
      F.R 93 = S.R 93 ∧ F.inp = S.inp ∧ F.out = S.out ∧
      PackedHaloReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b V
        (executionWidth p l target rhsExp)
        (cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail) E' outputTail F ∧
      F.R 126 = suffix ∧ F.R 127 = [] ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 126 → k ≠ 127 → k ≠ 128 → k ≠ 157 → k ≠ 132 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ M ∈ keys++done, PackedCellOutputSpec t p u l target rhsExp M
        (haloPackedOffsets s t (PhaseCellBand.width p u) a b M)
        (packedCellOrigin (s := s) a (haloPackedOffsets s t (PhaseCellBand.width p u) a b M))
        (fun _ => C) (F.R 132)) ∧
      (EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
        (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A (executionWidth p l target rhsExp) (executionPrecision p l target rhsExp)
          (interiorOutputExponent p l target rhsExp) E') ∧
      PackedHaloWordFrame s t (PhaseCellBand.width p u) a b (executionWidth p l target rhsExp)
        (S.R 132) (F.R 132) ∧ F.L = S.L ∧
      (∀ bound, (S.R 128).length ≤ bound → (∀ L ∈ keys, L ≤ bound) →
        (F.R 128).length ≤ bound) := by
  induction keys generalizing v S E done with
  | nil =>
    have he := Exec.loop_false (body := body) (p := packedHaloKeyStep hR hQ) (s := mk v S)
      (by change v.flag = false; simpa using hflag)
    refine ⟨v,S,1,E,rfl,by simp [packedHaloKeyLoopCost],he,rfl,rfl,rfl,hready,?_,?_,?_,?_,?_,?_,rfl,fun _ h _ => h⟩
    · simpa using hkeys
    · simpa using hcount
    · intros; exact ⟨rfl,rfl⟩
    · simpa using hold
    · exact fun h => h
    · exact PackedHaloWordFrame.refl _ _ _ _ _ _ _
  | cons L keys ih =>
    obtain ⟨hL,hLs,hpad,hkey⟩ := hbounds L (by simp)
    let S₀ : Stacks 168 A := {S with R := Function.update S.R 127 (List.replicate keys.length tick)}
    have hpop : Exec body (.act (.pop (.rt 127) (fun v _ => v) .done)) (mk v S) 1 (mk v S₀) := by
      have hp := Exec.act (body := body) (.pop (.rt 127) (fun v _ => v) .done) (mk v S)
      simpa [Action.run,update_rt,hcount,List.replicate_succ,S₀] using hp
    obtain ⟨v₁,F₁,m₁,E₁,hu₁,hm₁,he₁,h93₁,hi₁,ho₁,hready₁,hkeys₁,hframe₁,hall₁,hrange₁,hwords₁,hleft₁,hlength₁⟩ := packedHaloReady_publish (body := body)
      hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad C hC hab hb hband hkey hwide
      hVeq hwV hcoords hunits tail (keys.flatMap (binSyms V)++suffix) E outputTail done v S₀
      (hready.update_count _) (by simpa [S₀,List.flatMap_cons,List.append_assoc] using hkeys)
      (by simpa [S₀] using hold)
    have hc₁ : F₁.R 127 = List.replicate keys.length tick := by
      simpa [S₀] using (hframe₁ 127 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    let v₁' : HS 168 Q A U := {v₁ with flag := (F₁.R 127).head?.isSome}
    have hpeek : Exec body (.act (peekR 127)) (mk v₁ F₁) 1 (mk v₁' F₁) := by
      simpa only [peekR_run,v₁'] using Exec.act (body := body) (peekR 127) (mk v₁ F₁)
    obtain ⟨v₂,F₂,m₂,E₂,hu₂,hm₂,he₂,h93₂,hi₂,ho₂,hready₂,hkeys₂,hcount₂,hframe₂,hall₂,hrange₂,hwords₂,hleft₂,hlength₂⟩ :=
      ih (fun M hM => hbounds M (by simp [hM])) E₁ (L::done) v₁' F₁ hready₁ hkeys₁ hc₁
        (by cases keys <;> simp [v₁',hc₁,List.replicate_succ]) hall₁
    refine ⟨v₂,F₂,m₁+m₂+3,E₂,hu₂.trans hu₁,?_,?_,h93₂.trans h93₁,hi₂.trans hi₁,ho₂.trans ho₁,hready₂,hkeys₂,hcount₂,?_,?_,?_,?_,hleft₂.trans hleft₁,?_⟩
    · simp only [packedHaloKeyLoopCost,List.map_cons,List.sum_cons] at hm₂ ⊢
      omega
    · have hstep := Exec.seq hpop (Exec.seq he₁ hpeek)
      exact (Exec.loop_true (by change v.flag = true; simpa using hflag) hstep he₂).cast (by omega) rfl
    · intro k hk hn126 hn127 hn128 hn157 hn132
      obtain ⟨hl₂,hr₂⟩ := hframe₂ k hk hn126 hn127 hn128 hn157 hn132
      obtain ⟨hl₁,hr₁⟩ := hframe₁ k hk hn126 hn128 hn157 hn132
      exact ⟨hl₂.trans hl₁,hr₂.trans (by simpa only [S₀,Function.update_of_ne hn127] using hr₁)⟩
    · intro M hM
      apply hall₂ M
      simp only [List.mem_append,List.mem_cons] at hM ⊢
      rcases hM with (he | hm) | hd
      · exact Or.inr (Or.inl he)
      · exact Or.inl hm
      · exact Or.inr (Or.inr hd)
    · exact fun h => hrange₂ (hrange₁ h)
    · simpa only [S₀,Function.update_of_ne (by decide : (132 : Fin 168) ≠ 127)] using hwords₂.trans hwords₁
    · intro bound _ hbound
      apply hlength₂ bound
      · rw [hlength₁]
        exact hbound L (by simp)
      · intro M hM
        exact hbound M (by simp [hM])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
