module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalSelectionHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowControls
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Generate a local selection controller once from ordinary headers, before
replaying the restoring gather over the replica bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 117 Q A U}

def prepareLocalRowControls : Pr P 117 Q A U := .seq loadLocalRowHeaders generatedLocalRowControls

theorem prepareLocalRowControls_native :
    mnNativePushBound 3 (prepareLocalRowControls (P := P) (Q := Q) (A := A) (U := U)) := by
  simp only [prepareLocalRowControls,loadLocalRowHeaders,generatedLocalRowControls,
    generatedOriginControls,countedOriginHost,releaseOriginBank,preparedNaturalAdvanceControls,
    initializeAdvanceBank,releaseAdvanceBank,mnNativePushBound]
  refine ⟨chirpBankLoad_native ..,⟨⟨tblCompile_native ..,?_,?_⟩,clearWords_native_three _,
    chirpBankLoad_native ..,?_,?_,clearWords_native_three _⟩⟩
  all_goals simp [originAdvanceControls,originAdvanceLoopBody,originAdvanceNext,chirpControlEmit,
    countWords,countWordsBody,tblLoad1,toBinary,toUnary,hornerIter,udbl,eachSym,zeroBits,countIter,
    incrField,incStep,setCarry,bclear,bzero,copyPrefix,copyR,copyStep,transfer,transferAct,umulSym,popPush,scanR,drainR,popDo,
    keepIn,pushN,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush,tblCompile_native]

theorem prepareLocalRowControls_exec {W V t a origin span w n : ℕ}
    (hn : 0 < n) (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (h : LocalSelectionHeaders A W V s t a origin w n S) :
    ∃ v' B m, v'.user = v.user ∧ m ≤ (110*W+4*V+137)+localRowControlsCost W V span w n ∧
      Exec body prepareLocalRowControls (Host.mk v S) m (Host.mk v' B) ∧
      B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
      ∀ k, B.R k = if k = 91 then localRowControls A s t a n origin w else
        if k = 109 then (localRowOrigins s t a n origin 1).flatMap (binSyms V)++S.R 109 else
        if k = 116 then List.replicate n tick else S.R k := by
  have hleft := (hwindow 0 hn).1
  simp only [Nat.add_zero] at hleft
  obtain ⟨v₁,hu₁,he₁,htable,hframe⟩ := loadLocalRowHeaders_exec (body := body)
    W V s t a origin n hn hleft hwide v S h.width h.movementWidth h.sourceSize h.targetSize
    h.sourceOrigin h.targetOrigin h.rowCount h.zero h.table
  let H : Stacks 117 A := {S with R := (chirpBankLoadR originReg localRowSource W V
    (localRowValue s t a origin n) S.R)}
  change ∀ k, 31 ≤ k.val → H.R k = S.R k at hframe
  let st := localRowTable A s t a origin n
  have hbound : ∀ i, st.val i < 2^W := by
    intro i
    apply (localRowHeader_fit s t a origin n W hn hleft hwide i).trans_le
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    simp [localRowBits]; split_ifs <;> omega
  obtain ⟨v₂,B,m,hu₂,hm,he₂,hi,ho,hl,hR⟩ := generatedLocalRowControls_exec (body := body) st
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (by simp [st,localRowTable,localRowSource,localRowValue])
    (NeZero.pos s) hn (by omega) hwide hwindow hwV hspan hvol hVW hA hVpos hbound rfl
    v₁ H htable
    (by rw [hframe 115 (by decide)]; exact h.movementWidth)
    (by rw [hframe 94 (by decide)]; exact h.word)
    (by rw [hframe 104 (by decide)]; exact h.zero104)
    (by rw [hframe 106 (by decide)]; exact h.zero106)
    (by rw [hframe 116 (by decide)]; exact h.zero116)
    (by
      intro k hk
      have hk' : 31 ≤ k.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
      rw [hframe k hk']
      exact h.fresh k hk)
  refine ⟨v₂,B,(110*W+4*V+137)+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,Exec.seq he₁ he₂,hi,ho,hl,?_⟩
  intro k
  rw [hR]
  by_cases hk : k.val < 31
  · have hne : k ≠ 91 ∧ k ≠ 109 ∧ k ≠ 116 := by
      constructor
      · intro he; subst k; omega
      · constructor <;> intro he <;> subst k <;> omega
    simp only [hk,ite_true,hne.1,hne.2.1,hne.2.2,ite_false]
    exact (h.table k hk).symm
  · simp only [hk,ite_false]
    by_cases hk91 : k = 91
    · subst k
      simp only [ite_true,hframe 91 (by decide),h.control,List.append_nil]
    · simp only [hk91,ite_false]
      by_cases hk109 : k = 109
      · subst k; simp only [ite_true,hframe 109 (by decide)]
      · simp only [hk109,ite_false]
        by_cases hk116 : k = 116
        · subst k; simp only [ite_true]
        · simp only [hk116,ite_false]
          exact hframe k (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
