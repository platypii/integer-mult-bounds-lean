module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedGeneratedBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank

/-! A raw same-origin replica bank carries one unary origin, not one binary
origin packet per RHS. Setup reaches the existing exact numerical batch ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def repeatedBatchInputBank {A : ℕ} (P N q l s t u band L lo B : ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := batchInputBank P N q l s t u band L B (fun _ => lo) rhs borrowed outTail inp out
  { S with R := (Function.update (Function.update S.R 109 (List.replicate l tick)) 111 (List.replicate lo tick)) }

theorem generatedBatchBank_update109 {A : ℕ} (S : Stacks 117 A)
    (P s t u band L q N l B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed control packet : List (Fin (A+4))) :
    generatedBatchBank { S with R := Function.update S.R 109 packet }
      P s t u band L q N l B lo rhs borrowed control =
      generatedBatchBank S P s t u band L q N l B lo rhs borrowed control := by
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = 109
  · subst k; simp [generatedBatchBank,batchHeaderBank]
  simp [generatedBatchBank,batchHeaderBank,batchWeightedBank,batchInverseBank,
    batchWeightedBase,consumedGeometryBank,Function.update_apply,hk]

theorem repeatedGeneratedBatchBank_eq {A : ℕ} (P N q l s t u band L lo B : ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := repeatedBatchInputBank P N q l s t u band L lo B rhs borrowed outTail inp out
    generatedBatchBank { S with R := Function.update S.R 111 [] }
      P s t u band L q N l B (fun _ => lo) rhs borrowed (List.replicate l tick) =
    inputSourceBank q l (2*q+8) B L 0
      (fun _ => columnWords P s t u band L q (N+1))
      (fun _ => reversedColumnWords P s t u band L q (N+1)) [] [] outTail
      (csyms A (2*q+8) (reciprocalWord P s t u band L q (N+1)) ++
        (List.range B).flatMap (fun _ => outputWeightRow A (2*q+8) q P s t u L lo) ++ rhs ++
        (List.range B).flatMap (fun _ => inputWeightRow A (2*q+8) q P s t u L lo) ++ borrowed) inp out := by
  dsimp only
  let S := batchInputBank (A := A) P N q l s t u band L B (fun _ => lo) rhs borrowed outTail inp out
  have hclear : { repeatedBatchInputBank P N q l s t u band L lo B rhs borrowed outTail inp out with
      R := Function.update (repeatedBatchInputBank P N q l s t u band L lo B rhs borrowed outTail inp out).R 111 [] } =
      { S with R := Function.update S.R 109 (List.replicate l tick) } := by
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = 111
    · subst k; simp [S,batchInputBank]
    simp [repeatedBatchInputBank,S,Function.update_apply,hk]
  rw [hclear,generatedBatchBank_update109]
  exact generatedBatchBank_eq_inputSourceBank P N q l s t u band L B (fun _ => lo) rhs borrowed outTail inp out

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem repeatedBatchInputBank_setup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (P N q l s t u band L lo B : ℕ) (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L) (hLs : L ≤ s) (hlo : lo < s)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 117 Q A U) (hrhs : rhs.length = B*L*(2*q+8)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ repeatedGeneratedBatchSetupCost P N q s t u band l L lo B ∧
      Exec body (repeatedGeneratedBatchSetup hQ)
        (mk v (repeatedBatchInputBank P N q l s t u band L lo B rhs borrowed outTail inp out)) n
        (mk v' (inputSourceBank q l (2*q+8) B L 0
          (fun _ => columnWords P s t u band L q (N+1))
          (fun _ => reversedColumnWords P s t u band L q (N+1)) [] [] outTail
          (csyms A (2*q+8) (reciprocalWord P s t u band L q (N+1)) ++
            (List.range B).flatMap (fun _ => outputWeightRow A (2*q+8) q P s t u L lo) ++ rhs ++
            (List.range B).flatMap (fun _ => inputWeightRow A (2*q+8) q P s t u L lo) ++ borrowed) inp out)) := by
  let S := repeatedBatchInputBank (A := A) P N q l s t u band L lo B rhs borrowed outTail inp out
  have hlow (k : Fin 117) (hk : k.val < 93) : S.R k = [] := by
    have hn (n : ℕ) (h : 93 ≤ n) : k.val ≠ n := by omega
    simp [S,repeatedBatchInputBank,batchInputBank,Fin.ext_iff,hn 101 (by decide),hn 102 (by decide),
      hn 103 (by decide),hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),hn 100 (by decide),
      hn 109 (by decide),hn 111 (by decide),hn 112 (by decide),hn 114 (by decide),
      hn 116 (by decide),hn 110 (by decide),hn 93 (by decide)]
  have hc : CClean mul S := by
    intro i
    refine ⟨rfl,hlow (mul i) ?_⟩
    have hi := i.isLt
    dsimp [mul]
    omega
  have hb : ∀ r, S.R (cr r) = [] := by
    intro r
    obtain ⟨_,hhi,h93,_⟩ := cr_range r
    have hn (n : ℕ) (h : 97 ≤ n) : (cr r).val ≠ n := by omega
    simp [S,repeatedBatchInputBank,batchInputBank,Fin.ext_iff,hn 101 (by decide),hn 102 (by decide),
      hn 103 (by decide),hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),hn 100 (by decide),
      hn 109 (by decide),hn 111 (by decide),hn 112 (by decide),hn 114 (by decide),
      hn 116 (by decide),hn 110 (by decide),h93]
  obtain ⟨v',n,hu',hn,he⟩ := repeatedGeneratedBatchSetup_exec (body := body) (band := band) (l := l) (B := B)
    hQ hA hP hqMax hs hst hu hL hLs hlo v S rhs borrowed
    (by simp [S,repeatedBatchInputBank,batchInputBank]) (by simp [S,repeatedBatchInputBank,batchInputBank])
    (by simp [S,repeatedBatchInputBank,batchInputBank]) (by simp [S,repeatedBatchInputBank,batchInputBank])
    (by simp [S,repeatedBatchInputBank,batchInputBank]) (by simp [S,repeatedBatchInputBank,batchInputBank])
    (by simp [S,repeatedBatchInputBank,batchInputBank]) (by simp [S,repeatedBatchInputBank,batchInputBank])
    (by simp [S,repeatedBatchInputBank,batchInputBank]) (by simp [S,repeatedBatchInputBank,batchInputBank])
    (by simp [S,repeatedBatchInputBank,batchInputBank]) (by simp [S,repeatedBatchInputBank,batchInputBank])
    (by simp [S,repeatedBatchInputBank,batchInputBank]) hrhs hc hb (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S,repeatedBatchInputBank,batchInputBank])
  refine ⟨v',n,hu',hn,he.cast rfl ?_⟩
  simpa only [S,show S.R 109 = List.replicate l tick by simp [S,repeatedBatchInputBank]] using
    congrArg (mk v') (repeatedGeneratedBatchBank_eq P N q l s t u band L lo B rhs borrowed outTail inp out)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
