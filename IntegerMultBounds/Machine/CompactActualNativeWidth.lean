import IntegerMultBounds.Machine.CompactActualNativeStage
import IntegerMultBounds.Machine.ButterflyAxisSerialization

/-! Actual native stage capacity for the stored signed field width, including
arithmetic guard bits. Literal complex records contain two fields and two
separators. The fixed stage machine handles every such width above the actual
precision allowance; a linear stored-width bound gives a fixed-factor payload
bound. This does not assume that precision and stored width coincide. -/
namespace IntegerMultBounds.Machine.CompactActualNativeWidth
noncomputable section
open Sizes
open ActivePrefixStageParameters
open CompactActualStageAllowance CompactActualStageGeometry CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open ActivePrefixStageNative (cost)
open ButterflyStreamData (Coefficient encoded)

/-- Native symbols in one polynomial row, using its actual stored field width. -/
def symbols (n w : ℕ) := 2*(w+1)*2^ℓ n
def payload (n w : ℕ) := 3*symbols n w

theorem payload_allowance (n w : ℕ) (hw : b n≤w) :
    6*b n*2^ℓ n≤payload n w := by
  unfold payload symbols
  nlinarith [Nat.zero_le (2^ℓ n)]

theorem payload_linear (n w A : ℕ) (hb : 0<b n) (hw : w≤A*b n) :
    payload n w≤6*(A+1)*b n*2^ℓ n := by
  unfold payload symbols
  nlinarith [Nat.zero_le (2^ℓ n)]

theorem triple_capacity (n c m D w : ℕ) :
    (actualShape n c m D (payload n w)).payload=symbols n w*3+0 := by
  change 3*symbols n w=symbols n w*3+0
  omega

/-- The payload length is the literal serialization length, including both
record separators; no numerical-width-to-word-width identification is used. -/
theorem serialized_length (n w : ℕ) (xs : Fin (2^ℓ n) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    ((List.ofFn (fun i => encoded (xs i))).flatten).length=symbols n w := by
  have h := CyclicRowSplit.prefix_length (fun i => encoded (xs i)) (2*(w+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (hw i).1 (hw i).2) (2^ℓ n) le_rfl
  rw [CyclicRowCycle.prefix_all] at h
  simpa only [symbols,Nat.mul_comm] using h

/-- Explicit native payload symbols obtained from the actual coefficient words. -/
def nativeRow (n w : ℕ) (xs : Fin (2^ℓ n) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) : Fin (symbols n w) → Fin 6 :=
  fun k => ((List.ofFn (fun i => encoded (xs i))).flatten).get
    (Fin.cast (serialized_length n w xs hw).symm k)

theorem nativeRow_word (n w : ℕ) (xs : Fin (2^ℓ n) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    List.ofFn (nativeRow n w xs hw)=(List.ofFn (fun i => encoded (xs i))).flatten := by
  unfold nativeRow
  rw [←List.ofFn_congr (serialized_length n w xs hw),List.ofFn_get]

private theorem encoded_nonblank (a : Coefficient) (x : Fin 6) (hx : x∈encoded a) : x≠blank := by
  simp only [encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,
    List.mem_append,List.mem_map,List.mem_singleton] at hx
  rcases hx with (⟨d,_,rfl⟩|rfl)|(⟨d,_,rfl⟩|rfl)
  all_goals
    intro h
    have hv := congrArg Fin.val h
    dsimp only [RadixDigits.digitSymbol,separator,blank] at hv
    omega

/-- Literal digits and record separators meet the actual converter's sentinel
condition; a caller need not supply a codec or nonblank-word premise. -/
theorem nativeRow_nonblank (n w : ℕ) (xs : Fin (2^ℓ n) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) (k : Fin (symbols n w)) :
    nativeRow n w xs hw k≠blank := by
  have hmem : nativeRow n w xs hw k∈(List.ofFn (fun i => encoded (xs i))).flatten :=
    List.get_mem _ _
  rcases List.mem_flatten.mp hmem with ⟨ls,hls,hx⟩
  rcases List.mem_ofFn.mp hls with ⟨i,rfl⟩
  exact encoded_nonblank (xs i) _ hx

/-- One actual finite machine and uniform constant work at every stored width
satisfying the precision allowance, at all eventual nonfallback descendants.
Readiness and packed-cost premises are computed from original scalar choices. -/
theorem eventually_correct (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q Networks.Shared50ModularControl.prime,
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D j w : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hj : j≤depth m (d n)) (_hw : b n≤w)
      (v : Stage (actualShape n c m D (payload n w))),
      ∃ h : Ready (actualShape n c m D (payload n w)) v (rowsAt c m (d n) (K n) j),
        CompactActualNativeStage.BoundedSpec P C (symbols n w)
          (inputs v (rowsAt c m (d n) (K n) j) h) (triple_capacity n c m D w) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNative.exists_program
  obtain ⟨C,hC,hcost⟩ := ActivePrefixStageNative.uniform_bound 1
  refine ⟨q,P,C,hC,?_⟩
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,
    CompactActualStageRuntime.eventually_packed c m hc hm] with n hr hpacked
  intro D j w hcut hD hj hw v
  let h := hr D (payload n w) j hcut hD (payload_allowance n w hw) hj v
  let input := inputs v (rowsAt c m (d n) (K n) j) h
  let hp : 1 < input.stage.f → ActivePrefixStageRuntimeData.Packed input 1 := fun _ => hpacked D (payload n w) j hcut hD (payload_allowance n w hw) v h
  exact ⟨h,hp,hcost _ _ input (triple_capacity n c m D w) hp,
    fun xs hn => hP 1 _ _ input (triple_capacity n c m D w) xs hn hp⟩

end
end IntegerMultBounds.Machine.CompactActualNativeWidth
