module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedHeaderList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherReady

/-! Generate the three padded binary routing headers from retained unary
exponents and packet width, sharing one restored arithmetic workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {Q K : ℕ} {P U : Type}

def headerReg (i : Fin 117) : Fin tapeCount := base (callerGenerator i)

theorem headerReg_injective : Function.Injective headerReg :=
  base_injective.comp (TransposeRegisterPlacement.generator_injective _)

def gatherHeaderFields : List (Fin tapeCount × Fin tapeCount) :=
  [(headerReg 84,headerReg 97),(headerReg 85,headerReg 98),(packetWidth,headerReg 102)]

def gatherHeadersProgram : Pr P tapeCount Q (prime+K) U :=
  paddedHeaderList (headerReg 115) (headerReg 40) (headerReg 41) (headerReg 42)
    (headerReg 43) (headerReg 44) (headerReg 45) gatherHeaderFields

theorem gatherHeaders_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (a b C V : ℕ) (ha : Nat.size a ≤ V) (hb : Nat.size b ≤ V) (hC : Nat.size C ≤ V)
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hwidth : (S.R (headerReg 115)).length = V)
    (hsourceA : (S.R (headerReg 84)).length = a)
    (hsourceB : (S.R (headerReg 85)).length = b)
    (hsourceC : (S.R packetWidth).length = C)
    (hblank : ∀ i ∈ [(97 : Fin 117),98,102,40,41,42,43,44,45], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 21*(a+b+C)+36*V+85 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(21*(a+b+C)+36*V+85)) depth gatherHeadersProgram (mk v S) n
        (mk v' {S with R := Function.update (Function.update (Function.update S.R
          (headerReg 97) (binSyms V a)) (headerReg 98) (binSyms V b)) (headerReg 102) (binSyms V C)}) := by
  have hi := headerReg_injective
  have hp : packetWidth = headerReg 82 := rfl
  obtain ⟨v',n,hu,hn,he⟩ := paddedHeaderList_exec (body := body)
    (headerReg 115) (headerReg 40) (headerReg 41) (headerReg 42)
    (headerReg 43) (headerReg 44) (headerReg 45) V (fun i => (S.R i).length) gatherHeaderFields
    (by
      intro r hr
      simp only [gatherHeaderFields,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa only [hsourceA] using ha
      · simpa only [hsourceB] using hb
      · simpa only [hsourceC] using hC)
    (by
      intro r hr
      simp only [gatherHeaderFields,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [hp,List.nodup_cons,hi.eq_iff])
    (by simp [gatherHeaderFields,List.nodup_cons,hi.eq_iff])
    (by
      intro r hr s hs
      simp only [gatherHeaderFields,List.mem_cons,List.not_mem_nil,or_false] at hr hs
      rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp [hp,hi.eq_iff])
    (by
      intro r hr
      simp only [gatherHeaderFields,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [hi.eq_iff]) v S hwidth (by intros; rfl)
    (by
      intro r hr
      simp only [gatherHeaderFields,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> apply hblank <;> simp)
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> simp)
  have hcost : (gatherHeaderFields.map (fun r => 21*(S.R r.1).length+12*V+28)).sum+1 =
      21*(a+b+C)+36*V+85 := by
    simp [gatherHeaderFields,hsourceA,hsourceB,hsourceC]
    omega
  rw [hcost] at hn
  have he' : Exec body gatherHeadersProgram (mk v S) n
      (mk v' {S with R := Function.update (Function.update (Function.update S.R
        (headerReg 97) (binSyms V a)) (headerReg 98) (binSyms V b)) (headerReg 102) (binSyms V C)}) := by
    simpa only [gatherHeadersProgram,gatherHeaderFields,paddedHeaderListR,hsourceA,hsourceB,hsourceC] using he
  exact ⟨v',n,hu,hn,mn_native_exec_within he' 2
    (paddedHeaderList_native _ _ _ _ _ _ _ _) depth _ (by omega)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
