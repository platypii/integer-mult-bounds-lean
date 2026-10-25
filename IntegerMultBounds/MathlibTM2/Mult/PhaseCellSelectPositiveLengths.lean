module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDistinctLengthsCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords

/-! Consume four binary candidates and replace them with their positive distinct
subsequence. The small table is initialized and released; arbitrary suffixes and
all registers outside the packet destination are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Layer

def fourLengthHeaders (a b c d : ℕ) : List (Fin 16 × ℕ) := [(0,a), (1,b), (2,c), (3,d)]

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def selectPositiveLengths : Pr P 117 Q A U :=
  .seq initializeOriginBank (.seq (loadBinaryHeaders originReg 87 [0,1,2,3])
    (.seq (tblCompile originReg (distinctLengthsCode 12 [0,1,2,3]))
      (.seq (countWords (originReg .wn) (originReg .acc) 86 104 106)
        (.seq (moveR (originReg .acc) 87 (fun sym => bitSymbol (pairRe sym))) releaseOriginBank))))

theorem selectPositiveLengths_exec (V a b c d : ℕ) (hVpos : 0 < V)
    (ha : a < 2^V) (hb : b < 2^V) (hc : c < 2^V) (hd : d < 2^V) (hA : 4 ≤ A)
    (suffix : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (h106 : S.R 106 = []) (h104 : S.R 104 = []) (h86 : S.R 86 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hsrc : S.R 87 = ([a,b,c,d].flatMap (binSyms V)) ++ suffix) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ 21*tblC V V+230*V+263 ∧
      Exec body selectPositiveLengths (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update S.R 87
        ((([a,b,c,d].dedup.filter (fun L => decide (0 < L))).flatMap (binSyms V)) ++ suffix))
        86 (List.replicate ([a,b,c,d].dedup.filter (fun L => decide (0 < L))).length tick) := by
  let keys := [a,b,c,d].dedup.filter (fun L => decide (0 < L))
  have hkeys : keys.Sublist [a,b,c,d] := List.filter_sublist.trans (List.dedup_sublist _)
  have hkeysLength : keys.length ≤ 4 := by simpa using hkeys.length_le
  have hkeyFit : ∀ L ∈ keys, L < 2^V := by
    intro L hL
    have hh := hkeys.subset hL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl <;> assumption
  have hhigh (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106
    (fun r => hblank _ (originReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    exact fun r => (hhigh k hk r).symm
  obtain ⟨v₂, S₂, hu₂, he₂, hh₂, hs₂, hi₂, ho₂, hl₂, hf₂⟩ := loadBinaryHeaders_exec (body := body)
    originReg_injective 87 (hhigh 87 (by decide)) (fourLengthHeaders a b c d) V
    (List.replicate V tick) (List.replicate V tick) (by simp) ⟨fun _ => 0, []⟩ suffix v₁ S₁ hh₁
    (by rw [hoff₁ 87 (by decide)]; simpa [fourLengthHeaders] using hsrc)
  have he₂' : Exec body (loadBinaryHeaders originReg 87 [0,1,2,3]) (mk v₁ S₁) (32*V+33) (mk v₂ S₂) := by
    exact he₂.cast (by simp [fourLengthHeaders]; ring) rfl
  have hh₂' : tblHolds originReg S₂ (tblRho V (List.replicate V tick) (List.replicate V tick)
      (originRawState A a b c d)) := by
    simpa [loadedBinaryState, fourLengthHeaders, originRawState] using hh₂
  have hbound : ∀ i, (originRawState A a b c d).val i < 2^V := by
    intro i
    simp only [originRawState, Function.update_apply]
    split_ifs <;> first | assumption | positivity
  have hdo := distinctLengthsCode_do (A := A) (W := V) (e := V) 12 [0,1,2,3]
    (originRawState A a b c d) (by simp [originRawState])
  obtain ⟨st₃, ⟨⟨hv₃, ha₃⟩, hb₃⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hdo.bounded hbound) hbound
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hh₃, hf₃⟩ := hr v₂ S₂ hh₂'
  have hsym : S₃.R (originReg .acc) = (keys.flatMap (fun L => tblPairs A V L 0)).reverse := by
    rw [hh₃ .acc]
    simpa [tblRho, keys, originRawState] using ha₃
  have h87₃ : S₃.R 87 = suffix := (hf₃.2.2.2 87 (hhigh 87 (by decide))).trans hs₂
  have hlen : (S₃.R (originReg .acc)).length = keys.length*V := by
    rw [hsym]
    simp [List.length_flatMap, tblPairs]
  have hbits : (keys.flatMap (fun L => tblPairs A V L 0)).map
      (fun sym => bitSymbol (pairRe sym)) = keys.flatMap (binSyms (A := A) V) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro L hL
    exact tblPairs_real_bits hA (hkeyFit L hL)
  have hoff₃ (k : Fin 117) (hk : 31 ≤ k.val) (hk87 : k ≠ 87) : S₃.R k = S.R k :=
    (hf₃.2.2.2 k (hhigh k hk)).trans ((hf₂ k hk87 (hhigh k hk)).trans (hoff₁ k hk))
  let words := ((keys.map (fun L => (tblPairs A V L 0).reverse)).reverse)
  have hwords : words.flatten = S₃.R (originReg .acc) := by
    rw [hsym]
    simp [words, List.flatten_reverse, List.flatMap_def, List.map_map, Function.comp_def]
  have hwordlen : ∀ xs ∈ words, xs.length = V := by
    intro xs hx
    simp only [words, List.mem_reverse, List.mem_map] at hx
    obtain ⟨L, _, rfl⟩ := hx
    simp [tblPairs]
  obtain ⟨vc, huc, hec⟩ := countWords_exec (body := body)
    (width := originReg .wn) (src := originReg .acc) (dst := 86) (saved := 104) (tmp := 106)
    (by decide) V hVpos words hwordlen v₃ S₃
    (by rw [hh₃ .wn]; simp [tblRho]) hwords.symm
    (by rw [hoff₃ 104 (by decide) (by decide)]; exact h104)
    (by rw [hoff₃ 106 (by decide) (by decide)]; exact h106)
  let Sc : Stacks 117 A := { S₃ with R := (Function.update S₃.R 86 (List.replicate keys.length tick)) }
  have hec' : Exec body (countWords (originReg .wn) (originReg .acc) 86 104 106)
      (mk v₃ S₃) (keys.length*(6*V+6)+4) (mk vc Sc) := by
    simpa [Sc, words, hoff₃ 86 (by decide) (by decide), h86] using hec
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body (originReg .acc) 87 (by decide)
    (fun sym => bitSymbol (pairRe sym)) vc Sc
  let S₄ : Stacks 117 A := { Sc with R := (movedR Sc.R (originReg .acc) 87
    (fun sym => bitSymbol (pairRe sym)) (Sc.R (originReg .acc))) }
  have hh₄ : tblHolds originReg S₄ (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st₃.val, []⟩) := by
    intro r
    have h87r := hhigh 87 (by decide) r
    have h86r := hhigh 86 (by decide) r
    simp only [S₄, Sc, movedR, Function.update_apply, ite_eq_right h86r]
    rw [ite_eq_right h87r]
    by_cases hracc : r = .acc
    · subst r; simp [tblRho]
    · rw [ite_eq_right (originReg_injective.ne hracc), hh₃ r]
      cases r <;> simp_all [tblRho]
  obtain ⟨v₅, n₅, hu₅, hn₅, he₅⟩ := releaseOriginBank_exec (body := body) V st₃.val v₄ S₄ hh₄
  let S₅ : Stacks 117 A := { S₄ with R := fun k => if k.val < 31 then [] else S₄.R k }
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) (hk87 : k ≠ 87) (hk86 : k ≠ 86) : S₅.R k = S.R k := by
    have hacc : k ≠ originReg .acc := (hhigh k hk .acc).symm
    simp [S₅, S₄, Sc, movedR, show ¬ k.val < 31 by omega, hk87, hk86, hacc,
      hf₃.2.2.2 k (hhigh k hk), hf₂ k hk87 (hhigh k hk), hoff₁ k hk]
  refine ⟨v₅, S₅, (104*V+137)+((32*V+33)+(n₃+((keys.length*(6*V+6)+4)+((2*(keys.length*V)+2)+n₅)))),
    hu₅.trans (hu₄.trans (huc.trans (hu₃.trans (hu₂.trans hu₁)))), ?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq hec' (Exec.seq he₄ he₅))))).cast
      (by simp [Sc, show originReg .acc ≠ (86 : Fin 117) by decide, hlen]) rfl,
    hf₃.1.trans hi₂, hf₃.2.1.trans ho₂, hf₃.2.2.1.trans hl₂, ?_⟩
  · have hkV := Nat.mul_le_mul_right V hkeysLength
    change n₃ ≤ 21*tblC V V at hn₃
    nlinarith only [hn₃, hn₅, hkV, hkeysLength]
  · funext k
    by_cases hk87 : k = 87
    · subst k
      simp [S₅, S₄, Sc, movedR, hsym, h87₃, List.map_reverse, hbits, keys,
        show originReg .acc ≠ (86 : Fin 117) by decide]
    by_cases hk86 : k = 86
    · subst k; simp [S₅, S₄, Sc, movedR, originReg, keys]
    by_cases hlo : k.val < 31
    · simp [S₅, hlo, hk87, hk86, hblank k hlo]
    simp [hk87, hk86, hoff k (by omega) hk87 hk86]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
