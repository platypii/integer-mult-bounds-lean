module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedOriginHost
public import IntegerMultBounds.MathlibTM2.Fast.TableCompileStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Arbitrary origin enumerations share one table reserve. Publication and
counting are charged by emitted volume, independently of scan length. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def countedOriginWorkspace (W V B : ℕ) : ℕ :=
  B*V+3*tblC W V+(3*(B*(6*V+6)+4)+(2*(B*V)+2))

theorem countedOriginWorkspace_eq (W V B : ℕ) :
    countedOriginWorkspace W V B = B*(21*V+18)+3*tblC W V+14 := by
  unfold countedOriginWorkspace
  ring

theorem countedOriginListHost_exec_within {W V steps : ℕ} (xs : List ℕ)
    (code : TblCode 16) (st : TblSt 16 A)
    (hc : TblDo A W V code st (fun st' =>
      st'.acc = (xs.flatMap (fun x => tblPairs A V x 0)).reverse ++ st.acc) steps)
    (hpacket : ∀ x ∈ xs, x < 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hV : 0 < V) (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ steps*tblC W V + xs.length*(8*V+6)+6 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+countedOriginWorkspace W V xs.length)
        depth (countedOriginHost code) (mk v S) m (mk v' S')) ∧
      S'.R 109 = xs.flatMap (binSyms V) ++ S.R 109 ∧
      S'.R 116 = List.replicate xs.length tick ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hbits : (xs.flatMap (fun x => tblPairs A V x 0)).map
      (fun sym => bitSymbol (pairRe sym)) = xs.flatMap (binSyms (A := A) V) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro x hx
    exact tblPairs_real_bits hA (hpacket x hx)
  obtain ⟨st',k,hbig,⟨ha,hb⟩,hk⟩ := hc.bounded hbound
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ :=
    tblCompile_runs_within (body := body) originReg_injective
      (List.replicate W tick) (List.replicate V tick) (by simp) (by simp) hw hbig hbound v S hS
  have hm₁ := hm₁.trans (Nat.mul_le_mul_right (tblC W V) hk)
  have hsym : S₁.R (originReg .acc) = (xs.flatMap (fun x => tblPairs A V x 0)).reverse := by
    rw [hh₁ .acc]
    simpa [tblRho, hacc] using ha
  let words := (xs.map
    (fun x => (tblPairs A V x 0).reverse)).reverse
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
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (originReg .acc) 109 (by decide)
    (fun sym => bitSymbol (pairRe sym)) vc Sc
  let S₂ : Stacks 117 A := { Sc with R := (movedR Sc.R (originReg .acc) 109
    (fun sym => bitSymbol (pairRe sym)) (Sc.R (originReg .acc))) }
  have h109 : S₁.R 109 = S.R 109 := hf₁.2.2.2 109 (fun r he => by
    have hh := originReg_range r; rw [he] at hh; omega)
  have hlen : (S₁.R (originReg .acc)).length = xs.length*V := by
    rw [hsym]
    simp [List.length_flatMap, tblPairs]
  refine ⟨v₂, S₂, m₁+(xs.length*(6*V+6)+4)+(2*(xs.length*V)+2), st', hu₂.trans (huc.trans hu₁),
    by nlinarith only [hm₁], ?_, ?_, ?_, ?_, hb,
    hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · intro depth
    have ht₁ : ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(xs.length*V+3*tblC W V))
        depth (tblCompile originReg code) (mk v S) m₁ (mk v₁ S₁) := by
      apply (he₁ depth).mono
      intro d z hz
      have haLen : st'.acc.length = xs.length*V := by
        rw [ha,hacc]
        simp [List.length_flatMap,tblPairs]
      rw [haLen,hacc] at hz
      simpa only [List.length_nil,Nat.sub_zero,Nat.add_assoc] using hz
    have hcount : mnNativePushBound 3
        (countWords (P := P₀) (Q := Q) (A := A) (U := U) (originReg .wn) (originReg .acc) 116 106 104) := by
      simp [countWords,countWordsBody,transfer,transferAct,scanR,drainR,popDo,keepIn,
        pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
    have hmove : mnNativePushBound 1
        (moveR (P := P₀) (Q := Q) (A := A) (U := U) (originReg .acc) 109
          (fun sym => bitSymbol (pairRe sym))) := by
      simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
    have ht₂ := mn_native_exec_within hec' 3 hcount depth _ (Nat.le_refl _)
    have ht₃ := mn_native_exec_within he₂ 1 hmove depth _ (Nat.le_refl _)
    have ht := mn_seq_within_add ht₁ (mn_seq_within_add ht₂ ht₃)
    have ht' := ht.mono (J := fun d z => mnSize z+d ≤
        mnSize (mk v S)+depth+countedOriginWorkspace W V xs.length) (by
      intro d z hz
      simp only [Sc,Function.update_of_ne (show originReg .acc ≠ (116 : Fin 117) by decide),hlen] at hz
      unfold countedOriginWorkspace
      omega)
    exact ht'.cast (by simp [Sc,show originReg .acc ≠ (116 : Fin 117) by decide,hlen]; ring) rfl
  · simp [S₂, Sc, movedR, hsym, h109, List.map_reverse, hbits, show originReg .acc ≠ (116 : Fin 117) by decide]
  · simp [S₂, Sc, movedR, originReg]
  · intro r
    have hout : originReg r ≠ (109 : Fin 117) := by intro he; have hh := originReg_range r; rw [he] at hh; omega
    have h116r : originReg r ≠ (116 : Fin 117) := by
      intro he; have hh := originReg_range r; rw [he] at hh; omega
    simp only [S₂, Sc, movedR, Function.update_apply]
    simp only [ite_eq_right h116r]
    rw [ite_eq_right hout]
    by_cases hracc : r = .acc
    · subst r; simp [tblRho]
    · rw [ite_eq_right (originReg_injective.ne hracc), hh₁ r]
      cases r <;> simp_all [tblRho]
  · intro k hk109 hk116 hk
    have h18 : k ≠ originReg .acc := (hk .acc).symm
    simp [S₂, Sc, movedR, hk109, hk116, h18, hf₁.2.2.2 k hk]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
