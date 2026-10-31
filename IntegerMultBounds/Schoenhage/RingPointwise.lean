module

public import IntegerMultBounds.Schoenhage.RingRecord
public import IntegerMultBounds.Schoenhage.RingHeader
public import IntegerMultBounds.Schoenhage.Chunk
public import IntegerMultBounds.Schoenhage.RingBridgeMath
import IntegerMultBounds.Schoenhage.Wp
import IntegerMultBounds.Spec.SignedRingProductFacts
import Mathlib.Data.Nat.Size

/-! The pointwise-product step on word tapes: decode the header, build the
ring product's constants, cut both operand arrays into their component
words, multiply record by record, and clear everything but the output
string (`runs_pwCore`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-- `qR = ones 2`. -/
noncomputable def pwA : Cmd 𝕌 := .seq (emit [[true, true]] (ι qR)) (rewind (ι qR))

/-- `iW = ones (2r)`; `iP`, `iL` cleared. -/
noncomputable def pwB : Cmd 𝕌 :=
  .seq (clear iW) <| .seq (regMove (ι qR) iW (by decide)) <| .seq (clear iP) (clear iL)

/-- Cut both operands into words; start the output string. -/
noncomputable def pwC : Cmd 𝕌 :=
  .seq (chunkw zF kw iP (by decide) (by decide) (by decide)) <| .seq (rewind iP) <|
  .seq (chunkw zG kw iL (by decide) (by decide) (by decide)) <| .seq (rewind iL) (emit [[]] zO)

noncomputable def pwPrep : Cmd 𝕌 := .seq pwA <| .seq (ticksFrom iL (by decide)) <| .seq doubleT <| .seq pwB pwC

set_option maxHeartbeats 16000000 in
theorem runs_pwPrep {p l w : ℕ} (hw : 1 ≤ w) (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hP : τ iP = reg (ones p)) (hL : τ iL = reg (ones l)) (hW : τ iW = reg (ones w)) (hk : τ kw = reg (ones w))
    {F G : List Bool} (hF : τ zF = reg F) (hG : τ zG = reg G) (hO : τ zO = emp) :
    Runs pwPrep τ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ iW (reg (ones (2 * 2 ^ l)))) iP ⟨[], cut w F⟩) iL ⟨[], cut w G⟩)
      zF ⟨[F], []⟩) zG ⟨[G], []⟩) zO ⟨[[]], []⟩)
      (60 * 2 ^ l + 60 * l + 4 * (p + l + w) + 10 * (F.length + G.length) + 400 + 2 * (clen (cut w F) + clen (cut w G))) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have s1 : Runs pwA τ (· = Function.update τ (ι qR) (reg (ones 2))) 10 := by
    apply Runs.of_wp
    simp only [pwA, WP, wp_emit, wp_rewind]
    tsimp [hz, emp, reg, clen]
    funext y; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hz, emp, reg, ones])
  set τ₁ := Function.update τ (ι qR) (reg (ones 2))
  have s2 := runs_ticksFrom (show iL ≠ ι qT by decide) τ₁ (b := l) (by tsimp [τ₁, hL]) (by tsimp [τ₁, hz])
  set τ₂ := Function.update τ₁ (ι qT) ⟨[], List.replicate l []⟩
  have s3 := runs_doubleT (j := l) (r := 2) τ₂ (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, hz]) (by tsimp [τ₂, τ₁, hz])
    (by tsimp [τ₂])
  set τ₃ := Function.update (Function.update τ₂ (ι qR) (reg (ones (2 * 2 ^ l)))) (ι qT) emp
  have s4 : Runs pwB τ₃ (· = Function.update (Function.update (Function.update (Function.update τ₃
      iW (reg (ones (2 * 2 ^ l)))) (ι qR) emp) iP emp) iL emp) (4 * (p + l + w) + 8 * 2 ^ l + 60) := by
    apply Runs.of_wp
    simp only [pwB, regMove, regIn, cpy, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [τ₃, τ₂, τ₁, hW, hP, hL, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext y; simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, emp, reg])
    · simp [time_copy, clen, WTape.words]; omega
  set τ₄ := Function.update (Function.update (Function.update (Function.update τ₃
      iW (reg (ones (2 * 2 ^ l)))) (ι qR) emp) iP emp) iL emp
  have s5 := runs_chunkw (show zF ≠ kw by decide) (show zF ≠ iP by decide) (show kw ≠ iP by decide) τ₄
    (L := []) (R := []) (x := F) (w := w) (by tsimp [τ₄, τ₃, τ₂, τ₁, hF, reg]) (by tsimp [τ₄, τ₃, τ₂, τ₁, hk]) hw
    (by tsimp [τ₄])
  set τ₅ := Function.update (Function.update τ₄ zF ⟨[F], []⟩) iP ⟨(cut w F).reverse ++ (τ₄ iP).left, []⟩
  have s6 := runs_rewind iP τ₅
  set τ₆ := Function.update τ₅ iP ⟨[], (τ₅ iP).left.reverse ++ (τ₅ iP).right⟩
  have s7 := runs_chunkw (show zG ≠ kw by decide) (show zG ≠ iL by decide) (show kw ≠ iL by decide) τ₆
    (L := []) (R := []) (x := G) (w := w) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hG, reg])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hk]) hw (by tsimp [τ₆, τ₅, τ₄])
  set τ₇ := Function.update (Function.update τ₆ zG ⟨[G], []⟩) iL ⟨(cut w G).reverse ++ (τ₆ iL).left, []⟩
  have s8 := runs_rewind iL τ₇
  set τ₈ := Function.update τ₇ iL ⟨[], (τ₇ iL).left.reverse ++ (τ₇ iL).right⟩
  have s9 := runs_emit [[]] zO τ₈ (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hO, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 s9)))))))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5 s6 s7 s8 s9
    rw [h]; funext y
    by_cases hm : y ∈ [iW, iP, iL, zF, zG, zO, ι qR, ι qT]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁] <;> tsimp [hz, hO, emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hm
      simp only [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, ite_false]
  · clear s1 s2 s3 s4 s5 s6 s7 s8 s9
    tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hO, emp, clen_reverse]
    have : 2 * 2 ^ l - 2 ≤ 2 * 2 ^ l := Nat.sub_le _ _
    omega

/-! ### Arrays as words -/

theorem cut_flatten_words {w : ℕ} (hw : 1 ≤ w) : ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = w) →
    cut w cs.flatten = cs
  | [], _ => by simp
  | c :: cs, h => by
    have hc := h c (by simp)
    have hne : c ≠ [] := by intro e; rw [e] at hc; simp at hc; omega
    rw [List.flatten_cons, cut_cons (by simp [hne]) (by omega)]
    rw [show (c ++ cs.flatten).take w = c by rw [← hc]; simp,
      show (c ++ cs.flatten).drop w = cs.flatten by rw [← hc]; simp,
      cut_flatten_words hw cs (fun x hx => h x (by simp [hx]))]

theorem flat_lsbPairs {r : ℕ} (w : ℕ) (f : Rec r) :
    (flat (lsbPairs w f)).map List.reverse = recordWords w f.1 f.2 := by
  rw [lsbPairs_eq]
  have : ∀ l : List (Fin r), (flat (l.map fun j => (tw w (f.1 j), tw w (f.2 j)))).map List.reverse =
      l.flatMap fun j => [compWord w (f.1 j), compWord w (f.2 j)] := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => simp [flat_cons, ih, tw_reverse]
  rw [this]; rfl

theorem recordWords_lengths {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) : ∀ c ∈ recordWords w re im, c.length = w := by
  intro c hc
  simp only [recordWords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, -, rfl | rfl⟩ := hc <;> simp

theorem array_words {r : ℕ} (w : ℕ) (fs : List (Rec r)) :
    array w fs = (fs.map fun f => recordWords w f.1 f.2).flatten.flatten := by
  simp only [array, List.flatten_flatten, List.flatMap, List.map_map]
  congr 1; apply List.map_congr_left; intro f _
  simp [recordWords_flatten]

theorem cut_array {r w : ℕ} (hw : 1 ≤ w) (fs : List (Rec r)) :
    cut w (array w fs) = opWords (fs.map (lsbPairs w)) := by
  rw [array_words, cut_flatten_words hw]
  · simp only [opWords, List.map_map]
    congr 1; apply List.map_congr_left; intro f _
    simp [flat_lsbPairs]
  · intro c hc
    simp only [List.mem_flatten, List.mem_map] at hc
    obtain ⟨l, ⟨f, -, rfl⟩, hl⟩ := hc
    exact recordWords_lengths w f.1 f.2 c hl

/-! ### Ready for the records -/

theorem kOf_pow_dvd (e : ℕ) : 2 ^ kOf (2 ^ e) ∣ 2 ^ e := by
  apply Nat.pow_dvd_pow
  unfold kOf bitlen
  rw [Nat.size_pow]
  omega

theorem wOf_mul_pow (p l w : ℕ) : wOf p l w * 2 ^ l = 2 ^ (Nat.size (mW p l w) + l) := by
  rw [wOf, pow_add]

set_option maxHeartbeats 16000000 in
theorem recReady_of {p l w : ℕ} (hw : 1 ≤ w) (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hS : τ kS = reg (ones (p + l))) (hkw : τ kw = reg (ones w)) (hW : τ kW = reg (ones (wOf p l w)))
    (hN : τ kN = reg (ones (wOf p l w * 2 ^ l))) (hR : τ kR = reg (Rules.ruler (wOf p l w) (wOf p l w + 1) (2 ^ l)))
    (hH : τ kH = reg (bits (wOf p l w + 1) (2 ^ (wOf p l w - 1))))
    (hC : τ kC = reg (bits (wOf p l w + 1) (2 ^ (p + l) - 1)))
    (hO : τ kO = reg (rwd (wOf p l w * 2 ^ l) (wsum (wOf p l w) (List.replicate (2 ^ l) (2 ^ (wOf p l w - 1))))))
    (hI : τ kI = reg (rwd (wOf p l w * 2 ^ l) (wsum (wOf p l w) (List.replicate (2 ^ l) (2 ^ (w - 1))))))
    (hF : τ rF = emp) (hG : τ rG = emp) (hOo : τ rO = emp) (hA : τ xA = emp) (hB : τ xB = emp)
    (hC' : τ xC = emp) (hE : τ xE = emp) (hP : τ xP = emp) (hQ : τ xQ = emp) (hlR : τ lR = emp)
    (hlI : τ lI = emp) :
    RecReady (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) τ := by
  have hM := mW_lt_wOf p l w
  refine ⟨hF, hG, fun fs gs h1 h2 h3 h4 => ?_⟩
  exact ⟨Nat.one_le_two_pow, hw, by unfold mW at hM; omega, by unfold mW at hM; omega, rfl,
    by rw [wOf_mul_pow]; exact kOf_pow_dvd _, h1, h2, h3, h4,
    (hc.update (by unfold Own; decide) _).update (by unfold Own; decide) _,
    by tsimp, by tsimp, by tsimp [hOo], by tsimp [hW], by tsimp [hN], by tsimp [hR], by tsimp [hI],
    by tsimp [hO], by tsimp [hS], by tsimp [hH], by tsimp [hC], by tsimp [hkw], by tsimp [hA], by tsimp [hB],
    by tsimp [hC'], by tsimp [hE], by tsimp [hP], by tsimp [hQ], by tsimp [hlR], by tsimp [hlI]⟩

/-! ### The output -/

theorem lsbPairs_widths {r : ℕ} (w : ℕ) (f : Rec r) : ∀ q ∈ lsbPairs w f, q.1.length = w ∧ q.2.length = w := by
  intro q hq
  simp only [lsbPairs, List.mem_map] at hq
  obtain ⟨j, -, rfl⟩ := hq
  simp

theorem coeffs_bound {r p w : ℕ} (hw : p + 2 ≤ w) {f : Rec r} (hf : DiskGrid p f.1 f.2) :
    ∀ odd, ∀ x ∈ coeffs odd (lsbPairs w f), |x| ≤ (2 : ℤ) ^ p := by
  intro odd x hx
  rw [coeffs_lsbPairs hw hf] at hx
  simp only [List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  cases odd
  · exact (hf.abs_le j).1
  · exact (hf.abs_le j).2

theorem bound_wOf {p l w : ℕ} (hw : 1 ≤ w) :
    2 * 2 ^ l * ((2 : ℤ) ^ p * 2 ^ p) < 2 ^ (wOf p l w - 1) := by
  have hM := mW_lt_wOf p l w
  unfold mW at hM
  have e : (2 : ℤ) * 2 ^ l * (2 ^ p * 2 ^ p) = 2 ^ (1 + l + 2 * p) := by ring
  rw [e]
  exact pow_lt_pow_right₀ (by norm_num) (by omega)

/-- One record pair's output words, reversed and joined, are the paper's record of `Q_p(fg/r)`. -/
theorem ringWords_record {p l w : ℕ} (hw : p + 2 ≤ w) {τ : Fin 𝕌 → WTape}
    (hR : RecReady (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) τ) {f g : Rec (2 ^ l)}
    (hf : DiskGrid p f.1 f.2) (hg : DiskGrid p g.1 g.2) :
    ((ringWords (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) (lsbPairs w f) (lsbPairs w g)).map
      List.reverse).flatten = record w (prodRec p f g).1 (prodRec p f g).2 := by
  have hS := hR.2.2 (lsbPairs w f) (lsbPairs w g) (by simp [lsbPairs]) (by simp [lsbPairs])
    (lsbPairs_widths w f) (lsbPairs_widths w g)
  rw [ringWords, outs_eq hS (2 ^ p) (by positivity) (coeffs_bound hw hf) (coeffs_bound hw hg)
    (bound_wOf (by omega)), ringOut_records hw hf hg, recordWords_flatten]

/-! ### Cleanup -/

/-- Rewind the output and the operands; clear the words and constants. -/
noncomputable def pwFinish : Cmd 𝕌 :=
  .seq (rewind zO) <| .seq (clear iP) <| .seq (clear iL) <| .seq (clear iW) <| .seq (rewind zF) <|
  .seq (rewind zG) <| .seq (clear kS) <| .seq (clear kw) <| .seq (clear kW) <| .seq (clear kN) <|
  .seq (clear kR) <| .seq (clear kH) <| .seq (clear kC) <| .seq (clear kO) (clear kI)

/-- The tapes `pwFinish` clears. -/
def finTapes : List (Fin 𝕌) := [iP, iL, iW, kS, kw, kW, kN, kR, kH, kC, kO, kI]

set_option maxHeartbeats 16000000 in
theorem runs_pwFinish (τ : Fin 𝕌 → WTape) {out F G : List Bool} (hO : τ zO = ⟨[out], []⟩)
    (hF : τ zF = ⟨[F], []⟩) (hG : τ zG = ⟨[G], []⟩) :
    Runs pwFinish τ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update τ zO (reg out)) iP emp) iL emp)
      iW emp) zF (reg F)) zG (reg G)) kS emp) kw emp) kW emp) kN emp) kR emp) kH emp) kC emp) kO emp) kI emp)
      (2 * (finTapes.map fun x => clen (τ x).words).sum + 2 * (out.length + F.length + G.length) + 80) := by
  apply Runs.of_wp
  simp only [pwFinish, WP, wp_rewind, wp_clear]
  tsimp [hO, hF, hG, emp, reg]
  simp [finTapes, clen]; omega

/-! ### The whole step on word tapes -/

/-- Header decoding by `dec`, then constants, preparation, the records, cleanup. -/
noncomputable def pwCoreWith (dec : Cmd 𝕌) : Cmd 𝕌 :=
  .seq dec <| .seq constAll <| .seq pwPrep <| .seq recLoop pwFinish

/-- Header, constants, preparation, the records, cleanup. -/
noncomputable def pwCore : Cmd 𝕌 := pwCoreWith decodeHeader

/-- `dec` decodes the header `hdr` into `iP = ones p`, `iL = ones l`, `iW = ones w` within the
header bound. -/
def HdrDecodes (dec : Cmd 𝕌) (hdr : List Bool) (p l w : ℕ) : Prop :=
  ∀ τ : Fin 𝕌 → WTape, Clean τ → τ zH = reg hdr → τ iP = emp → τ iL = emp → τ iW = emp →
    Runs dec τ (· = Function.update (Function.update (Function.update τ iP (reg (ones p)))
      iL (reg (ones l))) iW (reg (ones w))) (headerCost p (2 ^ l) w hdr.length)

/-- The word bank at the start: header and operand strings, all else empty. -/
def startBank (hdr F G : List Bool) : Fin 𝕌 → WTape :=
  Function.update (Function.update (Function.update (fun _ => emp) zH (reg hdr)) zF (reg F)) zG (reg G)

theorem out_fold {p l w : ℕ} (hw : p + 2 ≤ w) {τ : Fin 𝕌 → WTape}
    (hR : RecReady (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) τ) :
    ∀ (fs gs : List (Rec (2 ^ l))), fs.length = gs.length → (∀ f ∈ fs, DiskGrid p f.1 f.2) →
      (∀ g ∈ gs, DiskGrid p g.1 g.2) →
      ((List.zip (fs.map (lsbPairs w)) (gs.map (lsbPairs w))).map fun q =>
        ((ringWords (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) q.1 q.2).map List.reverse).flatten).flatten
        = array w (List.zipWith (prodRec p) fs gs)
  | [], [], _, _, _ => rfl
  | f :: fs, g :: gs, hl, hf, hg => by
    simp only [List.map_cons, List.zip_cons_cons, List.flatten_cons, List.zipWith_cons_cons, array,
      List.flatMap_cons]
    rw [ringWords_record hw hR (hf f (by simp)) (hg g (by simp))]
    congr 1
    exact out_fold hw hR fs gs (by simpa using hl) (fun x hx => hf x (by simp [hx])) (fun x hx => hg x (by simp [hx]))
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem clen_cut_le (w : ℕ) (hw : 1 ≤ w) : ∀ (n : ℕ) (x : List Bool), x.length ≤ n → clen (cut w x) ≤ 2 * x.length
  | 0, x, h => by
    have : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp
  | n + 1, x, h => by
    by_cases hx : x = []
    · subst hx; simp
    · rw [cut_cons hx (by omega), clen_cons]
      have hp : 0 < x.length := List.length_pos_of_ne_nil hx
      have ih := clen_cut_le w hw n (x.drop w) (by simp; omega)
      simp only [List.length_take, List.length_drop] at ih ⊢
      have : min w x.length ≥ 1 := by omega
      omega

/-- A bound on the pointwise-product step on word tapes. -/
def pwCost (p _d l _K w H M X : ℕ) : ℕ :=
  headerCost p (2 ^ l) w H + constCost p l w +
    M * (2 ^ l * (56 * w + 400) + ringCost (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) + 204) +
    50 * X + 100 * 2 ^ l + 60 * l + 10 * (p + l + w) + 6 * (wOf p l w * 2 ^ l) + 4 * 2 ^ l * (wOf p l w + 2) +
    10 * wOf p l w + 1000

/-- The ordinary word bank immediately before the shared record loop. -/
def pwPreparedBank (p l w : ℕ) (hdr F G : List Bool) : Fin 𝕌 → WTape :=
  let τ₀ := startBank hdr F G
  let τ₁ := Function.update (Function.update (Function.update τ₀ iP (reg (ones p))) iL (reg (ones l)))
    iW (reg (ones w))
  let τ₂ := constBank p l w τ₁
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update τ₂ iW (reg (ones (2 * 2 ^ l)))) iP ⟨[], cut w F⟩) iL ⟨[], cut w G⟩)
    zF ⟨[F], []⟩) zG ⟨[G], []⟩) zO ⟨[[]], []⟩

set_option maxRecDepth 1000 in
/-- The three actual setup executions and the resulting record readiness share
one construction. Consumers need no supplied preparation execution. -/
theorem pwPreparation_spec {dec : Cmd 𝕌} {hdr : List Bool} {p l w : ℕ}
    (hdec : HdrDecodes dec hdr p l w) (hw1 : 1 ≤ w) (F G : List Bool) :
    let τ₀ := startBank hdr F G
    let τ₁ := Function.update (Function.update (Function.update τ₀ iP (reg (ones p))) iL (reg (ones l)))
      iW (reg (ones w))
    let τ₂ := constBank p l w τ₁
    let τ₃ := pwPreparedBank p l w hdr F G
    Runs dec τ₀ (· = τ₁) (headerCost p (2 ^ l) w hdr.length) ∧
    Runs constAll τ₁ (· = τ₂) (constCost p l w) ∧
    Runs pwPrep τ₂ (· = τ₃)
      (60 * 2 ^ l + 60 * l + 4 * (p + l + w) + 10 * (F.length + G.length) + 400 +
        2 * (clen (cut w F) + clen (cut w G))) ∧
    RecReady (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) τ₃ := by
  dsimp only
  set τ₀ := startBank hdr F G
  have hc₀ : Clean τ₀ := by
    unfold Clean; funext i
    simp only [Function.comp_apply, τ₀, startBank]
    rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
  have s1 := hdec τ₀ hc₀ (by tsimp [τ₀, startBank]) (by tsimp [τ₀, startBank])
    (by tsimp [τ₀, startBank]) (by tsimp [τ₀, startBank])
  set τ₁ := Function.update (Function.update (Function.update τ₀ iP (reg (ones p))) iL (reg (ones l)))
    iW (reg (ones w))
  have hc₁ : Clean τ₁ := ((hc₀.update (by unfold Own; decide) _).update (by unfold Own; decide) _).update
    (by unfold Own; decide) _
  have s2 := runs_constAll (p := p) (l := l) (w := w) hw1 τ₁ hc₁ (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁])
    (by tsimp [τ₁, τ₀, startBank]) (by tsimp [τ₁, τ₀, startBank]) (by tsimp [τ₁, τ₀, startBank])
    (by tsimp [τ₁, τ₀, startBank]) (by tsimp [τ₁, τ₀, startBank]) (by tsimp [τ₁, τ₀, startBank])
    (by tsimp [τ₁, τ₀, startBank]) (by tsimp [τ₁, τ₀, startBank]) (by tsimp [τ₁, τ₀, startBank])
  set τ₂ := constBank p l w τ₁
  have o : ∀ x : Fin 𝕌, 64 ≤ x.val → Own x := fun x h => h
  have hc₂ : Clean τ₂ := by
    simp only [τ₂, constBank]
    exact ((((((((hc₁.update (o kS (by decide)) _).update (o kw (by decide)) _).update (o kW (by decide)) _).update
      (o kN (by decide)) _).update (o kR (by decide)) _).update (o kH (by decide)) _).update (o kC (by decide)) _).update
      (o kO (by decide)) _).update (o kI (by decide)) _
  have s3 := runs_pwPrep (p := p) (l := l) (w := w) hw1 τ₂ hc₂ (by tsimp [τ₂, constBank, τ₁])
    (by tsimp [τ₂, constBank, τ₁]) (by tsimp [τ₂, constBank, τ₁]) (by tsimp [τ₂, constBank])
    (F := F) (G := G) (by tsimp [τ₂, constBank, τ₁, τ₀, startBank]) (by tsimp [τ₂, constBank, τ₁, τ₀, startBank])
    (by tsimp [τ₂, constBank, τ₁, τ₀, startBank])
  set τ₃ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ₂ iW (reg (ones (2 * 2 ^ l)))) iP ⟨[], cut w F⟩) iL ⟨[], cut w G⟩)
      zF ⟨[F], []⟩) zG ⟨[G], []⟩) zO ⟨[[]], []⟩
  have hc₃ : Clean τ₃ := (((((hc₂.update (o iW (by decide)) _).update (o iP (by decide)) _).update
    (o iL (by decide)) _).update (o zF (by decide)) _).update (o zG (by decide)) _).update (o zO (by decide)) _
  have hR₃ : RecReady (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) τ₃ :=
    recReady_of hw1 τ₃ hc₃ (by tsimp [τ₃, τ₂, constBank]) (by tsimp [τ₃, τ₂, constBank])
      (by tsimp [τ₃, τ₂, constBank]) (by tsimp [τ₃, τ₂, constBank]) (by tsimp [τ₃, τ₂, constBank])
      (by tsimp [τ₃, τ₂, constBank]) (by tsimp [τ₃, τ₂, constBank]) (by tsimp [τ₃, τ₂, constBank])
      (by tsimp [τ₃, τ₂, constBank]) (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank])
      (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank]) (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank])
      (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank]) (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank])
      (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank]) (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank])
      (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank]) (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank])
      (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank]) (by tsimp [τ₃, τ₂, constBank, τ₁, τ₀, startBank])
  exact ⟨s1,s2,s3,hR₃⟩

set_option maxHeartbeats 32000000 in
theorem runs_pwCoreWith {dec : Cmd 𝕌} {hdr : List Bool} {p l w : ℕ} {fs gs : List (Rec (2 ^ l))}
    (hdec : HdrDecodes dec hdr p l w) (hw : p + 2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    Runs (pwCoreWith dec) (startBank hdr (array w fs) (array w gs))
      (· = Function.update (startBank hdr (array w fs) (array w gs))
        zO (reg (array w (List.zipWith (prodRec p) fs gs))))
      (pwCost p 0 l 0 w hdr.length fs.length (array w fs).length) := by
  have hw1 : 1 ≤ w := by omega
  set F := array w fs
  set G := array w gs
  set τ₀ := startBank hdr F G
  set τ₁ := Function.update (Function.update (Function.update τ₀ iP (reg (ones p))) iL (reg (ones l)))
    iW (reg (ones w))
  set τ₂ := constBank p l w τ₁
  set τ₃ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ₂ iW (reg (ones (2 * 2 ^ l)))) iP ⟨[], cut w F⟩) iL ⟨[], cut w G⟩)
      zF ⟨[F], []⟩) zG ⟨[G], []⟩) zO ⟨[[]], []⟩
  obtain ⟨s1,s2,s3,hR₃⟩ := pwPreparation_spec hdec hw1 F G
  set ps := List.zip (fs.map (lsbPairs w)) (gs.map (lsbPairs w))
  have hpf : ps.map Prod.fst = fs.map (lsbPairs w) := by rw [List.map_fst_zip]; simp [hlen]
  have hpg : ps.map Prod.snd = gs.map (lsbPairs w) := by rw [List.map_snd_zip]; simp [hlen]
  have hq : ∀ q ∈ ps, q.1.length = 2 ^ l ∧ q.2.length = 2 ^ l ∧ (∀ x ∈ q.1, x.1.length = w ∧ x.2.length = w) ∧
      (∀ x ∈ q.2, x.1.length = w ∧ x.2.length = w) := by
    intro q hq
    have := List.of_mem_zip hq
    obtain ⟨f, -, hf1⟩ := List.mem_map.mp this.1
    obtain ⟨g, -, hg1⟩ := List.mem_map.mp this.2
    rw [← hf1, ← hg1]
    exact ⟨by simp [lsbPairs], by simp [lsbPairs], lsbPairs_widths w f, lsbPairs_widths w g⟩
  have s4 := runs_recLoop (Wd := wOf p l w) (s := p + l) (N := wOf p l w * 2 ^ l) Nat.one_le_two_pow ps τ₃
    [] [] [] hq hR₃ (by tsimp [τ₃]) (by tsimp [τ₃, hpf, F, cut_array hw1]) (by tsimp [τ₃, hpg, G, cut_array hw1])
    (by tsimp [τ₃])
  set out' := (ps.map fun q => ((ringWords (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) q.1 q.2).map
    List.reverse).flatten).flatten
  have hout : out' = array w (List.zipWith (prodRec p) fs gs) := out_fold hw hR₃ fs gs hlen hf hg
  set τ₄ := Function.update (Function.update (Function.update τ₃
    iP ⟨(opWords (ps.map Prod.fst)).reverse ++ [], []⟩) iL ⟨(opWords (ps.map Prod.snd)).reverse ++ [], []⟩)
    zO ⟨[[] ++ out'], []⟩
  have s5 := runs_pwFinish τ₄ (out := out') (F := F) (G := G) (by tsimp [τ₄]) (by tsimp [τ₄, τ₃]) (by tsimp [τ₄, τ₃])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5
    rw [h, ← hout]; funext y
    by_cases hm : y ∈ [zO, iP, iL, iW, zF, zG, kS, kw, kW, kN, kR, kH, kC, kO, kI]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₄, τ₃, τ₂, constBank, τ₁, τ₀, startBank] <;> tsimp [emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hm
      simp only [τ₄, τ₃, τ₂, constBank, τ₁, τ₀, startBank, Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8,
        n9, n10, n11, n12, n13, n14, n15, ite_false]
  · clear s1 s2 s3 s4 s5
    simp only [finTapes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    tsimp [τ₄, τ₃, τ₂, constBank, reg, WTape.words, clen_cons, clen_nil, clen_reverse, clen_append]
    have lFG : G.length = F.length := by simp only [F, G, length_array, hlen]
    have cF := clen_cut_le w hw1 _ F le_rfl
    have cG := clen_cut_le w hw1 _ G le_rfl
    have oF : clen (opWords (List.map Prod.fst ps)) = clen (cut w F) := by rw [hpf, ← cut_array hw1]
    have oG : clen (opWords (List.map Prod.snd ps)) = clen (cut w G) := by rw [hpg, ← cut_array hw1]
    have lO : out'.length ≤ F.length := by
      rw [hout]; simp only [F, length_array, List.length_zipWith, hlen, min_self]; rfl
    have hRl := length_ruler (show wOf p l w + 1 ≤ wOf p l w + 1 from le_rfl) (2 ^ l)
    have lps : ps.length = fs.length := by simp [ps, hlen]
    rw [oF, oG, lps, rwd_length, rwd_length]
    unfold pwCost
    generalize headerCost p (2 ^ l) w hdr.length = A1 at *
    generalize constCost p l w = A2 at *
    generalize ringCost (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) = A3 at *
    clear_value F G out' ps
    rw [lFG] at cG ⊢
    nlinarith

theorem runs_pwCore {p d l K w : ℕ} {ts : List ℕ} {fs gs : List (Rec (2 ^ l))}
    (hp : 2 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : p + 2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    Runs pwCore (startBank (transformHeader p d (2 ^ l) K w ts) (array w fs) (array w gs))
      (· = Function.update (startBank (transformHeader p d (2 ^ l) K w ts) (array w fs) (array w gs))
        zO (reg (array w (List.zipWith (prodRec p) fs gs))))
      (pwCost p d l K w (transformHeader p d (2 ^ l) K w ts).length fs.length (array w fs).length) :=
  runs_pwCoreWith (fun τ hc hH hP hL hW => runs_decodeHeader (by omega) hd hK (by omega) τ hc hH hP hL hW)
    hw hlen hf hg

end IntegerMultBounds.Schoenhage
