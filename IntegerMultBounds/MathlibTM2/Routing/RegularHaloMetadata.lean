module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountHost
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadUnaryDimension

/-! Load retained binary geometry, generate exact halo metadata and the pair
clock, then release the arithmetic bank and decoder scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloMetadata
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz RegularHaloCountHost RegularHaloCountCode
  RegularHaloLayout HaloIntervalLayout
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def source (i : Fin 16) : Fin 117 :=
  if i = 0 then 97 else if i = 1 then 98 else if i = 2 then 100 else 116

def bits (V : ℕ) (i : Fin 117) : ℕ := if i = 116 then 0 else V

def value (N L B : ℕ) (i : Fin 117) : ℕ := if i = 97 then N else if i = 98 then L else if i = 100 then B else 0

def load : Pr P 117 Q A U := .seq (chirpBankLoad originReg source 115 115) generateCounts

theorem load_cost (V : ℕ) : chirpBankLoadCost originReg source V V (bits V) = 110*V+137 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,source,bits,List.ofFn_succ]
  ring

theorem load_exec {V L H N : ℕ} (hgap : 2*H ≤ L) (hwide : N+2 < 2^V) (hsize : L+2*H < 2^V)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hN : S.R 97 = binSyms V N)
    (hL : S.R 98 = binSyms V L) (hB : S.R 100 = binSyms V (2*H)) (hz : S.R 116 = [])
    (hblank : ∀ i : Fin 117, i.val < 31 → S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (10*paddedCount N+13)*tblC V V+(4*paddedCount N+174)*V+202 ∧
      Exec body load (mk v S) n (mk vf {S with R := (Function.update S.R 109
        (binSyms V (pairs L H 0 N).length++metadata V 0 (pairs L H 0 N)++S.R 109))}) := by
  have hoff (i : Fin 117) (hi : 31 ≤ i.val) : ∀ r, originReg r ≠ i := by
    intro r he
    have hh := originReg_range r
    rw [he] at hh
    omega
  have hinput : ∀ i r, originReg r ≠ source i := by
    intro i
    apply hoff
    simp only [source]; split_ifs <;> decide
  have hfit : ∀ i, value N L (2*H) (source i) < 2^(bits V (source i)) := by
    intro i
    simp only [source]
    split_ifs <;> simp [value,bits] <;> omega
  have hbits : ∀ i, bits V (source i) ≤ V := by
    intro i
    simp only [bits]; split_ifs <;> omega
  have hsrc : ∀ i, S.R (source i) = binSyms (bits V (source i)) (value N L (2*H) (source i)) := by
    intro i
    simp only [source]
    split_ifs <;> simp [bits,value,hN,hL,hB,hz,binSyms]
  have hb : ∀ r, S.R (originReg r) = [] := fun r => hblank _ (originReg_range r)
  obtain ⟨v₁,hu₁,he₁⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective source
    115 115 (hoff 115 (by decide)) (hoff 115 (by decide)) hinput V V (bits V) (value N L (2*H))
    hfit hbits v S hV hV hsrc hb
  let F : Stacks 117 A := {S with R := chirpBankLoadR originReg source V V (value N L (2*H)) S.R}
  have hh := chirpBankLoad_holds originReg originReg_injective source V V (value N L (2*H)) S hb
  let st : TblSt 16 A := ⟨fun i => value N L (2*H) (source i),[]⟩
  have hbound : ∀ i, st.val i < 2^V := by
    intro i
    exact (hfit i).trans_le (Nat.pow_le_pow_right (by decide) (hbits i))
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateCounts_exec (body := body) st
    (by simp [st,source,value]) (by simp [st,source,value]) (by simp [st,source,value])
    hgap hwide hsize hbound rfl hA v₁ F hh
  have hframe (i : Fin 117) (hi : 31 ≤ i.val) : F.R i = S.R i :=
    chirpBankLoad_off originReg source V V (value N L (2*H)) S.R i (fun r => (hoff i hi r).symm)
  refine ⟨v₂,110*V+137+n₂,hu₂.trans hu₁,by nlinarith only [hn₂],
    (Exec.seq (he₁.cast (load_cost V) rfl) he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i.val < 31
  · have hn : i ≠ 109 := by intro he; subst i; norm_num at hi
    simp [hi,hn,hblank i hi]
  · have hge : 31 ≤ i.val := by omega
    by_cases h109 : i = 109
    · subst i; simp [hframe 109 (by decide)]
    · simp [hi,h109,hframe i hge]

def prepare : Pr P 117 Q A U :=
  .seq load (readUnaryDimension 115 116 109 96 114 95 94 93 92)

def prepareCost (N V : ℕ) : ℕ :=
  (10*paddedCount N+13)*tblC V V+(4*paddedCount N+193)*V+6*paddedCount N+226

theorem prepare_exec {V L H N : ℕ} (hgap : 2*H ≤ L) (hwide : N+2 < 2^V) (hsize : L+2*H < 2^V)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hN : S.R 97 = binSyms V N)
    (hL : S.R 98 = binSyms V L) (hB : S.R 100 = binSyms V (2*H)) (hz : S.R 116 = [])
    (hblank : ∀ i : Fin 117, i.val < 31 → S.R i = [])
    (hfresh : ∀ i ∈ [(96 : Fin 117),114,95,94,93,92], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ prepareCost N V ∧
      Exec body prepare (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R 109
        (metadata V 0 (pairs L H 0 N)++S.R 109)) 114 (List.replicate (pairs L H 0 N).length tick))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := load_exec (body := body) hgap hwide hsize hA v S hV hN hL hB hz hblank
  let F : Stacks 117 A := {S with R := (Function.update S.R 109
    (binSyms V (pairs L H 0 N).length++metadata V 0 (pairs L H 0 N)++S.R 109))}
  have hfit : (pairs L H 0 N).length < 2^V := by
    have hh := RegularHaloCountLayout.pairs_count L H 0 N
    unfold paddedCount at hh
    omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := readUnaryDimension_exec (body := body) 115 116 109 96 114 95 94 93 92
    (by decide) V (pairs L H 0 N).length hfit (metadata V 0 (pairs L H 0 N)++S.R 109) v₁ F
    (by simpa [F] using hV) (by simpa [F] using hz) (by simp [F,List.append_assoc]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F,hfresh])
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · unfold readUnaryDimensionCost at hn₂
    have hh := RegularHaloCountLayout.pairs_count L H 0 N
    unfold prepareCost
    nlinarith only [hn₁,hn₂,hh]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 114
    · subst i; simp
    by_cases hq : i = 109
    · subst i; simp
    · simp [F,hi,hq]

theorem load_native : mnNativePushBound 3 (load (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨chirpBankLoad_native _ _ _ _,tblCompile_native _ _,?_,clearWords_native_three _⟩
  simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem prepare_native : mnNativePushBound 3 (prepare (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨load_native,readUnaryDimension_native _ _ _ _ _ _ _ _ _⟩

theorem prepare_within_stock {v vf : HS 117 Q A U} {S F : Stacks 117 A} {n C : ℕ}
    (hex : Exec body prepare (mk v S) n (mk vf F)) (hn : n ≤ C) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*C) depth prepare
      (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 3 prepare_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloMetadata
