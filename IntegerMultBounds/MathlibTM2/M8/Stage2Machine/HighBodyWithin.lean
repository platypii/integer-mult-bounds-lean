module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PaddedCoreWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighSeparateSharedWithin

/-! Exchange, padded core and separation reuse one original-volume reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBodyWithin
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open RevMachine HighBody
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

def coefficient (k cutoff : ℕ) : ℕ := max M8.Machine.ArbitraryWidthHighExchangeJoinWithin.coefficient
  (max (2*PaddedCoreWithin.coefficient k cutoff) (M8.Machine.RadixHighBlockSeparateRunWithin.coefficient prime))

theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) {K : ℕ} (hτ : Exponents K) :
    ∃ C' : ℝ, ∀ P e r G B : ℕ, r ≤ e → 0 < P → 0 < G → 0 < B →
      ∀ (hs : Fin 6 → List Bool) (rs ss op oe : List Bool),
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs → JoinCounters P e r G B rs ss op oe →
      ∀ (R' : ℕ) (ph : Fin 4 → List Bool), prime^(2*r) ≤ R' →
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers (joinedDescriptor prime P e r G B) R' ph →
      Fits K (withRows (joinedDescriptor prime P e r G B) R') →
      volume prime (withRows (joinedDescriptor prime P e r G B) R') ≤ 2*volume prime (originalDescriptor P e G B) →
      ∀ (f₀ : ℤ → Fin (prime+4)) (p₀ : ℤ) (node₀ scalar₀ : Tapes 1 prime) (st₀ : Tapes 2 prime),
      M8.Machine.CallReady.Ready f₀ p₀ node₀ scalar₀ st₀ →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t)
        (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∀ lo hi : ℤ,
      (∀ j, lo+(coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤
        (privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph
          (withRows (joinedDescriptor prime P e r G B) R') f p node st caller).head j ∧
        (privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph
          (withRows (joinedDescriptor prime P e r G B) R') f p node st caller).head j+
          (coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) → ∃ c : ℕ,
        (c : ℝ) ≤ ((M8.Machine.ArbitraryWidthHighExchangeJoin.coefficient +
            M8.Machine.RadixHighBlockSeparateRun.coefficient prime : ℕ) : ℝ) * (r + 1) *
              volume prime (originalDescriptor P e G B) +
          826 * volume prime (withRows (joinedDescriptor prime P e r G B) R') + 5 +
          C' * volume prime (withRows (joinedDescriptor prime P e r G B) R') * ((e - r : ℕ) : ℝ) ^ tau₂ K ∧
        HoareWithin (program capacity focus)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph
            (withRows (joinedDescriptor prime P e r G B) R') f p node st caller)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph
            (withRows (joinedDescriptor prime P e r G B) R') f p node st
            (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  obtain ⟨C', hC'⟩ := PaddedCoreWithin.shared_runs capacity cutoff hcut hτ
  refine ⟨C', fun P e r G B hfit hP hG hB hs rs ss op oe hv hj R' ph hR hph hfits hvolume
    f₀ p₀ node₀ scalar₀ st₀ ready₀ f p node st hready t caller focus x hf hh lo hi hmargin => ?_⟩
  let v := joinedDescriptor prime P e r G B
  let ex := M8.Machine.ArbitraryWidthHighExchangeShared.privateBank hs rs f₀ p₀ node₀ scalar₀ st₀
  let mv := M8.Machine.ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs
  let pd := privateBank capacity K ph (withRows v R') f p node st
  change ∀ j, lo+(coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤
    (((caller.append ex).append mv).append pd).head j ∧
    (((caller.append ex).append mv).append pd).head j+
      (coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi at hmargin
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP,(by change 0 < 1; decide),(by change 0 < 1; decide),hG,hB⟩
  let V := volume prime (originalDescriptor P e G B)
  have hEx := Nat.mul_le_mul_right V
    (show M8.Machine.ArbitraryWidthHighExchangeJoinWithin.coefficient ≤ (coefficient k cutoff) from le_max_left _ _)
  have hPd := Nat.mul_le_mul_right V
    (show 2*(PaddedCoreWithin.coefficient k cutoff) ≤ (coefficient k cutoff) from
      (le_max_left _ _).trans (le_max_right _ _))
  have hSep := Nat.mul_le_mul_right V
    (show M8.Machine.RadixHighBlockSeparateRunWithin.coefficient prime ≤ (coefficient k cutoff) from
      (le_max_right _ _).trans (le_max_right _ _))
  have hframe : ∀ j, lo ≤ pd.head j ∧ pd.head j ≤ hi := by
    intro j
    have hm := hmargin (Fin.natAdd (t+exchangeCount+movementCount) j)
    simp only [Tapes.append,Fin.addCases_right] at hm
    change lo ≤ pd.head j ∧ pd.head j ≤ hi
    omega
  have hsetHeads (source : ℤ → Fin (prime+4)) :
      (setTape caller focus source 0).head = caller.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [setTape,Function.update_self,hh]
    · simp only [setTape,Function.update_of_ne hj]
  have h1 := HoareWithin.extend_heads_eq pd lo hi
    (M8.Machine.ArbitraryWidthHighExchangeJoinWithin.realizes_within caller focus P e r G B hfit hP hG hB
      hs rs ss op oe hp hv hj.hr hj.cr hj.hss hj.css hj.hop hj.cop hj.hoe hj.coe f₀ p₀ node₀ scalar₀ st₀ ready₀ x hf hh lo hi (by
        intro j
        have hm := hmargin (Fin.castAdd (padCount capacity) j)
        simp only [Tapes.append,Fin.addCases_left] at hm
        dsimp only [V] at hEx
        simp only [Tapes.append]
        dsimp only [ex,mv] at hm
        omega)) hframe
  let joined := exchangeJoin P e r G B hfit x
  let mid := ((setTape caller focus (sourceWord joined) 0).append ex).append mv
  have hvp : v.Positive := ⟨hP,pow_pos Networks.Shared50ModularControl.prime_prime.pos _,
    (by change 0 < 1; decide),hG,hB⟩
  have hmidHeads : (mid.append pd).head = (((caller.append ex).append mv).append pd).head :=
    Tapes.append_head_congr _ _ pd pd
      (Tapes.append_head_congr _ _ mv mv (Tapes.append_head_congr _ _ ex ex (hsetHeads _) rfl) rfl) rfl
  have hPadded : (PaddedCoreWithin.coefficient k cutoff)*volume prime
      (RecursiveRowPadding.withRows v R') ≤ (coefficient k cutoff)*V := by
    have h := Nat.mul_le_mul_left (PaddedCoreWithin.coefficient k cutoff) hvolume
    change (PaddedCoreWithin.coefficient k cutoff)*volume prime
      (withRows v R') ≤ _ at h
    calc
      _ ≤ (PaddedCoreWithin.coefficient k cutoff)*(2*V) := h
      _ = (2*(PaddedCoreWithin.coefficient k cutoff))*V := by ring
      _ ≤ _ := hPd
  obtain ⟨c₂, hc₂, h2⟩ := hC' v R' ph hvp hR hph hfits f p node st hready mid
    (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus)) joined
    (by simp only [mid,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
    (by simp only [mid,Tapes.append,Fin.addCases_left,setTape,Function.update_self]) lo hi (by
      intro j
      change lo+_ ≤ (mid.append pd).head j ∧ (mid.append pd).head j+_ ≤ hi
      rw [hmidHeads]
      have hm := hmargin j
      dsimp only [V] at hPadded
      change lo+_ ≤ (((caller.append ex).append mv).append pd).head j ∧
        (((caller.append ex).append mv).append pd).head j+_ ≤ hi at hm
      omega)
  have hout2 : setTape mid (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus))
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0 =
      ((setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0).append ex).append mv := by
    dsimp only [mid]
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
      SharedPlacementAlphabet.setTape_setTape]
  rw [hout2] at h2
  let low := Shared50RecursiveNodeRows.transpose (one_dvd v.rows) joined
  let sepCaller := (setTape caller focus (sourceWord low) 0).append ex
  have hlowHeads : ((sepCaller.append mv).append pd).head =
      (((caller.append ex).append mv).append pd).head :=
    Tapes.append_head_congr _ _ pd pd
      (Tapes.append_head_congr _ _ mv mv (Tapes.append_head_congr _ _ ex ex (hsetHeads _) rfl) rfl) rfl
  have h3 := HoareWithin.extend_heads_eq pd lo hi
    (M8.Machine.ArbitraryWidthHighSeparateSharedWithin.realizes_within sepCaller (Fin.castAdd exchangeCount focus)
      P e r G B hfit hP hG hB rs ss op oe hj.hr hj.cr hj.hss hj.css hj.hop hj.cop hj.hoe hj.coe low
      (by simp only [sepCaller,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
      (by simp only [sepCaller,Tapes.append,Fin.addCases_left,setTape,Function.update_self]) lo hi (by
        intro j
        have hm := hmargin (Fin.castAdd (padCount capacity) j)
        have he := congrFun hlowHeads (Fin.castAdd (padCount capacity) j)
        simp only [Tapes.append,Fin.addCases_left] at hm he
        dsimp only [V] at hSep
        change lo+_ ≤ (sepCaller.append mv).head j ∧ (sepCaller.append mv).head j+_ ≤ hi
        simp only [Tapes.append]
        rw [he]
        dsimp only [ex,mv] at hm ⊢
        omega)) hframe
  have hout3 : setTape sepCaller (Fin.castAdd exchangeCount focus)
      (sourceWord (separateExchange P e r G B hfit low)) 0 =
      (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).append ex := by
    dsimp only [sepCaller,low,joined,v]
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_setTape,
      exchange_transpose_separate]
  rw [hout3] at h3
  have h := (h1.seq h2).seq h3
  refine ⟨M8.Machine.ArbitraryWidthHighExchangeJoin.coefficient*(r+1)*
    volume prime (originalDescriptor P e G B)+1+1+c₂+1+
    M8.Machine.RadixHighBlockSeparateRun.coefficient prime*(r+1)*
      volume prime (originalDescriptor P e G B), ?_, ?_⟩
  · have hw : v.width = e-r := rfl
    rw [hw] at hc₂
    push_cast
    dsimp only [v] at hc₂
    nlinarith only [hc₂]
  · simpa only [program,privateBanks] using h

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBodyWithin
