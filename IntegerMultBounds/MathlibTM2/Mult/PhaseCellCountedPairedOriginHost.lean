module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTablePacketHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedOriginBits
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush

/-! Publish paired ambient/local binary origins and one shared count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- Count paired packets once, then project both coordinates without decoding. -/
def countedPairedOriginHost (code : TblCode 16) : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg code)
    (.seq (countWords (originReg .wn) (originReg .acc) 116 106 104)
      (.seq (copyR (originReg .acc) 113 104 (fun sym => bitSymbol (pairRe sym)))
        (moveR (originReg .acc) 109 (fun sym => bitSymbol (pairIm sym)))))

theorem countedPairedOriginHost_native (code : TblCode 16) :
    mnNativePushBound 3 (countedPairedOriginHost (P₀ := P₀) (Q := Q) (A := A) (U := U) code) := by
  simp only [countedPairedOriginHost,mnNativePushBound]
  refine ⟨tblCompile_native _ _,?_,?_,?_⟩
  all_goals simp [countWords,countWordsBody,copyR,copyStep,moveR,moveStep,whileR,peekR,
    transfer,transferAct,scanR,drainR,popDo,keepIn,pushN,mnNativePushBound,mnActPush]

theorem countedPairedOriginHost_exec {W V steps : ℕ} (xs : List (ℕ × ℕ))
    (code : TblCode 16) (st : TblSt 16 A)
    (hc : TblDo A W V code st (fun st' =>
      st'.acc = (xs.flatMap (fun x => tblPairs A V x.1 x.2)).reverse ++ st.acc) steps)
    (hpacket : ∀ x ∈ xs, x.1 < 2^V ∧ x.2 < 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hV : 0 < V) (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ steps*tblC W V + xs.length*(12*V+6)+10 ∧
      Exec body (countedPairedOriginHost code) (mk v S) m (mk v' S') ∧
      S'.R 113 = xs.flatMap (fun x => binSyms V x.1) ++ S.R 113 ∧
      S'.R 109 = xs.flatMap (fun x => binSyms V x.2) ++ S.R 109 ∧
      S'.R 116 = List.replicate xs.length tick ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 113 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hbits : (xs.flatMap (fun x => tblPairs A V x.1 x.2)).map
      (fun sym => bitSymbol (pairRe sym)) = xs.flatMap (fun x => binSyms (A := A) V x.1) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro x hx
    exact tblPairs_fst_bits hA (hpacket x hx).1
  have hlocal : (xs.flatMap (fun x => tblPairs A V x.1 x.2)).map
      (fun sym => bitSymbol (pairIm sym)) = xs.flatMap (fun x => binSyms (A := A) V x.2) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro x hx
    exact tblPairs_snd_bits hA (hpacket x hx).2
  obtain ⟨st', ⟨ha, hb⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate W tick) (List.replicate V tick) (by simp) (by simp) hw (hc.bounded hbound) hbound
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  have hsym : S₁.R (originReg .acc) = (xs.flatMap (fun x => tblPairs A V x.1 x.2)).reverse := by
    rw [hh₁ .acc]
    simpa [tblRho, hacc] using ha
  let words := (xs.map
    (fun x => (tblPairs A V x.1 x.2).reverse)).reverse
  have hwords : words.flatten = S₁.R (originReg .acc) := by
    rw [hsym]
    simp [words, List.flatten_reverse, List.flatMap_def, List.map_map, Function.comp_def]
  have hwordlen : ∀ xs ∈ words, xs.length = V := by
    intro xs hx
    simp only [words, List.mem_reverse, List.mem_map] at hx
    obtain ⟨phase, _, rfl⟩ := hx
    simp [tblPairs]
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k :=
    hf₁.2.2.2 k (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)
  obtain ⟨vc, huc, hec⟩ := countWords_exec (body := body)
    (width := originReg .wn) (src := originReg .acc) (dst := 116) (saved := 106) (tmp := 104)
    (by decide) V hV words hwordlen v₁ S₁
    (by rw [hh₁ .wn]; simp [tblRho]) hwords.symm
    (by rw [hoff 106 (by decide), h106]) (by rw [hoff 104 (by decide), h104])
  let Sc : Stacks 117 A := { S₁ with R := (Function.update S₁.R 116
    (List.replicate xs.length tick)) }
  have hec' : Exec body (countWords (originReg .wn) (originReg .acc) 116 106 104)
      (mk v₁ S₁) (xs.length*(6*V+6)+4) (mk vc Sc) := by
    simpa [Sc, words, hoff 116 (by decide), h116] using hec
  obtain ⟨vp,hup,hep⟩ := copyR_exec (body := body) (originReg .acc) 113 104
    (by decide) (by decide) (by decide) (fun sym => bitSymbol (pairRe sym)) vc Sc
    (by simp [Sc,hoff 104 (by decide),h104])
  let Sp : Stacks 117 A := {Sc with R := (Function.update Sc.R 113
    (((Sc.R (originReg .acc)).map (fun sym => bitSymbol (pairRe sym))).reverse++Sc.R 113))}
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (originReg .acc) 109 (by decide)
    (fun sym => bitSymbol (pairIm sym)) vp Sp
  let S₂ : Stacks 117 A := { Sp with R := (movedR Sp.R (originReg .acc) 109
    (fun sym => bitSymbol (pairIm sym)) (Sp.R (originReg .acc))) }
  have h109 : S₁.R 109 = S.R 109 := hf₁.2.2.2 109 (fun r he => by
    have hh := originReg_range r; rw [he] at hh; omega)
  have hlen : (S₁.R (originReg .acc)).length = xs.length*V := by
    rw [hsym]
    simp [List.length_flatMap, tblPairs]
  have hsym18 : S₁.R 18 = (xs.flatMap (fun x => tblPairs A V x.1 x.2)).reverse := hsym
  refine ⟨v₂, S₂, m₁+(xs.length*(6*V+6)+4)+(4*(xs.length*V)+4)+(2*(xs.length*V)+2), st', hu₂.trans (hup.trans (huc.trans hu₁)),
    by nlinarith only [hm₁], (Exec.seq he₁ (Exec.seq hec' (Exec.seq hep he₂))).cast (by simp [Sp,Sc,show originReg .acc ≠ (116 : Fin 117) by decide,show originReg .acc ≠ (113 : Fin 117) by decide,hlen]; ring) rfl, ?_, ?_, ?_, ?_, hb,
    hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · simp [S₂,Sp,Sc,movedR,hsym18,hoff 113 (by decide),List.map_reverse,hbits,originReg]
  · simp [S₂,Sp,Sc,movedR,hsym18,h109,List.map_reverse,hlocal,originReg]
  · simp [S₂,Sp,Sc,movedR,originReg]
  · intro r
    have hout : originReg r ≠ (109 : Fin 117) := by intro he; have hh := originReg_range r; rw [he] at hh; omega
    have h116r : originReg r ≠ (116 : Fin 117) := by
      intro he; have hh := originReg_range r; rw [he] at hh; omega
    simp only [S₂, Sp, Sc, movedR, Function.update_apply]
    simp only [ite_eq_right h116r]
    have h113r : originReg r ≠ (113 : Fin 117) := by
      intro he; have hh := originReg_range r; rw [he] at hh; omega
    simp only [ite_eq_right h113r]
    rw [ite_eq_right hout]
    by_cases hracc : r = .acc
    · subst r; simp [tblRho]
    · rw [ite_eq_right (originReg_injective.ne hracc), hh₁ r]
      cases r <;> simp_all [tblRho]
  · intro k hk109 hk113 hk116 hk
    have h18 : k ≠ originReg .acc := (hk .acc).symm
    simp [S₂, Sp, Sc, movedR, hk109, hk113, hk116, h18, hf₁.2.2.2 k hk]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
