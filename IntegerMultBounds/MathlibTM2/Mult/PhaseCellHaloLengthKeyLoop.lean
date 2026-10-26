module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyLoop

/-! A single counted loop executes all selected length classes. Its invariant
keeps earlier classes' physical reads unchanged, so the final accuracy has no
key-count factor. The borrowed key/output suffixes remain outside loop ownership. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloLengthKeyLoopCost (p l s t u target rhsExp V a b : ℕ) (keys : List ℕ) : ℕ :=
  (keys.map (fun L => (6*L+19*V+14)+conditionalHaloClassCost p l L s t u target rhsExp a b+3)).sum+1

theorem haloLengthKeyLoop_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (keys : List ℕ) (hnodup : keys.Nodup)
    (hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^l+1 ∧ L < 2^V)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail keyTail : List (Fin (A+4)))
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hkeys : S.R 126 = lengthKeyPackets A V keys++keyTail)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) V
      (executionWidth p l target rhsExp) (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hflag : v.flag = keys.head?.isSome) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧
      n ≤ haloLengthKeyLoopCost p l s t u target rhsExp V a b keys ∧
      Exec (embTab groupReg body) (.loop (·.flag) (haloLengthKeyStep hR hQ)) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ E'.length = s*w ∧
      S'.R = keyLoopR S.R keyTail [] (E'++outputTail) ∧
      (∀ L ∈ keys, ∀ n : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
          (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target)) ∧
      ∀ K, K ∉ keys → ∀ n : Fin (haloLengthGroup s t band a b K).length, ∀ j ∈ publishedCellCore
        (haloGroupOrigin s t band a b K n) K,
        publishedCellRead q w (0 : ZMod s) (S'.R 132) j = publishedCellRead q w (0 : ZMod s) (S.R 132) j := by
  dsimp only
  induction keys generalizing v S E with
  | nil =>
    have hc : S.R 127 = [] := by simpa using hcount
    have hk : S.R 126 = keyTail := by simpa [lengthKeyPackets] using hkeys
    have he := Exec.loop_false (body := embTab groupReg body) (p := haloLengthKeyStep hR hQ) (s := mk v S)
      (by change v.flag = false; simpa using hflag)
    refine ⟨v,S,1,E,rfl,by simp [haloLengthKeyLoopCost],he,rfl,rfl,rfl,hE,?_,?_,?_⟩
    · have hf : keyLoopR S.R keyTail [] (E++outputTail) = S.R := by
        simpa only [hk,hc,hdst] using keyLoopR_self S.R
      exact hf.symm
    · intro L hL
      simp at hL
    · intro K _ n j hj
      rfl
  | cons L keys ih =>
    obtain ⟨hLnot,hnd⟩ := List.nodup_cons.mp hnodup
    obtain ⟨hL,hLs,hpad,hfit⟩ := hbounds L (by simp)
    obtain ⟨v₁,S₁,n₁,E₁,hu₁,hflag₁,hn₁,he₁,hi₁,ho₁,hl₁,hE₁,hframe₁,herror₁,hkeep₁⟩ :=
      haloLengthKeyStep_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hL hLs hpad C hC x hx
        v S borrowed E outputTail (lengthKeyPackets A V keys++keyTail) tick (List.replicate keys.length tick)
        (by simpa [List.replicate_succ] using hcount) hfit hready.keyWidth
        (by simpa [lengthKeyPackets,List.append_assoc] using hkeys) hE hdst hready.masters haMaster hbMaster hready.left hready.blank
        hready.source hready.countSaved hready.headerTemp hready.wordWidth hready.fresh
    have hready₁ := hready.of_frame (lengthKeyPackets A V keys++keyTail) (List.replicate keys.length tick)
      (E₁++outputTail) hl₁ hframe₁
    have hkeys₁ : S₁.R 126 = lengthKeyPackets A V keys++keyTail := by
      simpa [keyLoopR] using congrArg (fun R => R 126) hframe₁
    have hcount₁ : S₁.R 127 = List.replicate keys.length tick := by
      simpa [keyLoopR] using congrArg (fun R => R 127) hframe₁
    have hdst₁ : S₁.R 132 = E₁++outputTail := by
      simpa [keyLoopR] using congrArg (fun R => R 132) hframe₁
    obtain ⟨v₂,S₂,n₂,E₂,hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hE₂,hframe₂,herror₂,hkeep₂⟩ :=
      ih hnd (fun K hK => hbounds K (by simp [hK])) v₁ S₁ E₁ hE₁ hdst₁ hkeys₁ hcount₁ hready₁
        (by rw [hframe₁]; simpa [keyLoopR] using haMaster)
        (by rw [hframe₁]; simpa [keyLoopR] using hbMaster)
        (hflag₁.trans (count_head_isSome keys))
    refine ⟨v₂,S₂,n₁+n₂+1,E₂,hu₂.trans hu₁,?_,
      Exec.loop_true (by change v.flag = true; simpa using hflag) he₁ he₂,
      hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,hE₂,?_,?_,?_⟩
    · dsimp only [haloLengthKeyLoopCost] at hn₂ ⊢
      simp only [List.map_cons,List.sum_cons]
      omega
    · exact hframe₂.trans (by rw [hframe₁,keyLoopR_comp])
    · intro K hK n
      rcases List.mem_cons.mp hK with hEq | hK
      · subst K
        intro j hj
        have heq := hkeep₂ L hLnot n j hj
        change ‖publishedCellRead _ _ _ (S₂.R 132) j-x j‖ ≤ _
        rw [heq]
        exact herror₁ n j hj
      · exact herror₂ K hK n
    · intro K hK n j hj
      have hKL : K ≠ L := fun he => hK (List.mem_cons.mpr (Or.inl he))
      have hKtail : K ∉ keys := fun hk => hK (List.mem_cons.mpr (Or.inr hk))
      exact (hkeep₂ K hKtail n j hj).trans (hkeep₁ K hKL n j hj)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
