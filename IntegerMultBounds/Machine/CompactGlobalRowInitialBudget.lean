import IntegerMultBounds.Machine.CompactGlobalRowInitialRun
import IntegerMultBounds.Machine.CompactGlobalRowHeaderCost

/-! All global header synthesis, whole-row movement and descriptor erasure
are charged to original complete-record volume. The role and arity constants
are fixed; no factor depending on recursion depth enters the coefficient. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowInitialBudget
noncomputable section
open CompactGlobalRowPadding
open CompactGlobalRowHeaders (recordWidth)

def headerConstant (c m : ℕ) := RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+
  3*CompactGlobalRowHeaderPrimitives.logConstant m+FixedBasePowerDescriptor.constant c+
  2*FixedBasePowerDescriptor.constant 2+10000

theorem header_linear (c m d D K P V : ℕ) (hc : 0<c) (hV : 0<V)
    (hd : d≤V) (hD : D≤V) (hlc : Nat.clog 2 c≤V) (hlt : Nat.clog m (2*d)≤2*V)
    (hq : rowAxes c m d≤V) (he : rowAxes c m d*K≤V)
    (he' : (D-rowAxes c m d)*K≤V)
    (hdiv : c^depth m d≤V) (hr : originalRows c m d K≤V)
    (hs : 2^((D-rowAxes c m d)*K)≤V)
    (hl : recordWidth c m d D K P≤V) (hz : initialRows c m d K≤V) :
    CompactGlobalRowHeaders.cost c m d D K P≤headerConstant c m*V := by
  rw [CompactGlobalRowHeaderCost.cost_eq c m d D K P hc]
  have hleft : D-rowAxes c m d≤V := (Nat.sub_le _ _).trans hD
  have ht := Nat.mul_le_mul_left (CompactGlobalRowHeaderPrimitives.logConstant m) hd
  have hp := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant c) hdiv
  have hp2 := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hr
  have hp3 := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hs
  have hconst := Nat.le_mul_of_pos_right (RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)) hV
  unfold headerConstant
  nlinarith

theorem cost_linear (c m d D K P : ℕ) (hc : 2≤c) (hm : 2≤m) (hmc : m≤c)
    (hd : 0<d) (hK : 0<K) (hp : 0<P) (hDd : D≤d) :
    CompactGlobalRowInitialRun.cost c m d D K P ≤
      (headerConstant c m+2415)*(initialRows c m d K*recordWidth c m d D K P) := by
  let V := initialRows c m d K*recordWidth c m d D K P
  have hZpos := initial_positive c m d K (by omega) hK
  have hLpos : 0<recordWidth c m d D K P := Nat.mul_pos (pow_pos (by decide) _) hp
  have hV : 0<V := Nat.mul_pos hZpos hLpos
  have hZ : initialRows c m d K≤V := Nat.le_mul_of_pos_right _ hLpos
  have hL : recordWidth c m d D K P≤V := Nat.le_mul_of_pos_left _ hZpos
  have hR : originalRows c m d K≤V := (initial_bounds c m d K (by omega) hK).1.trans hZ
  have hDiv : c^depth m d≤V := (divisor_le_original c m d K hK).trans hR
  have hdV : d≤V := (Nat.le_pow_clog (by omega : 1<m) d).trans
    ((Nat.pow_le_pow_left hmc _).trans hDiv)
  have hDV : D≤V := hDd.trans hdV
  have he : rowAxes c m d*K≤V :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := rowAxes c m d*K))).trans hR
  have hq : rowAxes c m d≤V := (Nat.le_mul_of_pos_right _ hK).trans he
  have htpos : 0<Nat.clog m (2*d) := by
    have h := Nat.le_pow_clog (by omega : 1<m) (2*d)
    by_contra hn
    have hz : Nat.clog m (2*d)=0 := by omega
    rw [hz,pow_zero] at h
    omega
  have hlc : Nat.clog 2 c≤V := (Nat.le_mul_of_pos_right _ htpos).trans hq
  have ht : Nat.clog m (2*d)≤2*V :=
    (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by omega : 1<m)))).trans
      (Nat.mul_le_mul_left 2 hdV)
  have hdepth : depth m d≤V :=
    (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by omega : 1<m)))).trans hdV
  have hs : 2^((D-rowAxes c m d)*K)≤V := (Nat.le_mul_of_pos_right _ hp).trans hL
  have he' : (D-rowAxes c m d)*K≤V :=
    (Nat.le_of_lt (Nat.lt_two_pow_self)).trans hs
  have hh := header_linear c m d D K P V (by omega) hV hdV hDV hlc ht hq he he' hDiv hR hs hL hZ
  have hclean : CompactGlobalRowInitialCleanup.cost c m d D K P≤2000*V := by
    rw [CompactGlobalRowInitialCleanup.cost_eq]
    omega
  unfold CompactGlobalRowInitialRun.cost
  change CompactGlobalRowHeaders.cost c m d D K P+413*V+
    CompactGlobalRowInitialCleanup.cost c m d D K P+2≤(headerConstant c m+2415)*V
  nlinarith

/-- One global padding has at most twice the original literal volume. -/
theorem original_linear (c m d D K P : ℕ) (hc : 2≤c) (hm : 2≤m) (hmc : m≤c)
    (hd : 0<d) (hK : 0<K) (hp : 0<P) (hDd : D≤d) (hD : rowAxes c m d≤D) :
    CompactGlobalRowInitialRun.cost c m d D K P ≤
      (2*(headerConstant c m+2415))*(2^(D*K)*P) := by
  have hh := cost_linear c m d D K P hc hm hmc hd hK hp hDd
  have hb := Nat.mul_le_mul_right (recordWidth c m d D K P)
    (initial_bounds c m d K (by omega) hK).2.2.1
  have hv := CompactGlobalRowInitialRun.original_volume c m d D K P hD
  calc
    _ ≤ (headerConstant c m+2415)*(initialRows c m d K*recordWidth c m d D K P) := hh
    _ ≤ (headerConstant c m+2415)*((2*originalRows c m d K)*recordWidth c m d D K P) :=
      Nat.mul_le_mul_left _ hb
    _ = (2*(headerConstant c m+2415))*(originalRows c m d K*recordWidth c m d D K P) := by ring
    _ = _ := by rw [hv]

theorem runs_linear {a : ℕ} (c m d D K P : ℕ) (hc : 2≤c) (hm : 2≤m) (hmc : m≤c)
    (hd : 0<d) (hK : 0<K) (hp : 0<P) (hDd : D≤d) (hD : rowAxes c m d≤D)
    (source dest : ℤ → Fin 4) (p q : ℤ)
    (x : Fin (1*originalRows c m d K*recordWidth c m d D K P) → Bool) :
    HoareTime (CompactGlobalRowInitialRun.program (a := a) c m)
      (fun v => v=CompactGlobalRowInitialData.bank (CompactGlobalRowHeaders.initial K d D P)
        (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
        (RowPaddingConstructedAlphabet.mapTape dest) p q)
      (fun v => v=CompactGlobalRowInitialData.bank (CompactGlobalRowHeaders.initial K d D P)
        (RowPaddingConstructedAlphabet.erased
          (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun i => bitSymbol (x i))))
          p (1*originalRows c m d K*recordWidth c m d D K P))
        (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
          (List.ofFn (RecursiveRowPadding.pad (initialRows c m d K) (bitSymbol false) (fun i => bitSymbol (x i))))) p q)
      ((2*(headerConstant c m+2415))*(2^(D*K)*P)) :=
  (CompactGlobalRowInitialRun.runs c m d D K P hc hm hd hK hp hD source dest p q x).consequence
    (fun _ h => h) (fun _ h => h) (original_linear c m d D K P hc hm hmc hd hK hp hDd hD)

end
end IntegerMultBounds.Machine.CompactGlobalRowInitialBudget
