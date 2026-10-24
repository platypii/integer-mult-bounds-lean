module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderScalarGenerate
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankTrace

/-! The complete inner-header bank has two generated words and a shared blank
source. Serialize every role in auxiliary-bank order, preserving copy scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def headerOperandSource : HeaderWorkRole → Fin 120
  | .binary i => if i = 0 then 118 else 119
  | _ => 39

def headerOperandRoles : List HeaderWorkRole :=
  (List.finRange (Fintype.card HeaderWorkRole)).map (Fintype.equivFin _).symm

theorem headerScalarBank_operands (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (wc : ℕ) (hblank : R (rg 39) = []) :
    (fun r => headerScalarBank R (rg ∘ canonicalHeaderScalarSlot) wc (rg (headerOperandSource r))) =
      canonicalHeaderOperands (canonicalScalarWidth 1) (canonicalScalarWidth wc) 1 wc := by
  funext r
  cases r with
  | binary i =>
    fin_cases i
    · exact headerScalarBank_binary R (rg ∘ canonicalHeaderScalarSlot)
        (hrg.comp canonicalHeaderScalarSlot_injective) wc 0
    · exact headerScalarBank_binary R (rg ∘ canonicalHeaderScalarSlot)
        (hrg.comp canonicalHeaderScalarSlot_injective) wc 1
  | _ => simp [headerOperandSource,headerScalarBank,canonicalHeaderScalarSlot,
      canonicalHeaderOperands,hrg.eq_iff,hblank]

def headerOperandFrameJobs (rg : Fin 120 → Fin T) (words : HeaderWorkRole → List (Fin (A + 4))) :=
  headerOperandRoles.map (fun r => (rg (headerOperandSource r),words r))

def headerOperandFrame (delimiter : Fin (A + 4)) (rg : Fin 120 → Fin T)
    (words : HeaderWorkRole → List (Fin (A + 4))) :=
  delimitedBankFrames delimiter (headerOperandFrameJobs rg words)

def headerOperandCopy (rg : Fin 120 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 40) (rg 41) delimiter
    (headerOperandRoles.map (fun r => rg (headerOperandSource r)))

theorem headerOperandSource_scratch (r : HeaderWorkRole) :
    headerOperandSource r ≠ 40 ∧ headerOperandSource r ≠ 41 := by
  cases r with
  | binary i => fin_cases i <;> decide
  | _ => change (39 : Fin 120) ≠ 40 ∧ (39 : Fin 120) ≠ 41; decide

theorem headerOperandCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4))
    (words : HeaderWorkRole → List (Fin (A + 4))) (B : ℕ) (hwords : ∀ r, (words r).length ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ r, S.R (rg (headerOperandSource r)) = words r)
    (htmp : S.R (rg 40) = []) (hwork : S.R (rg 41) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ Fintype.card HeaderWorkRole * (6 * B + 7) + 1 ∧
      Exec body (headerOperandCopy rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (headerOperandFrame delimiter rg words ++ S.R dst)) }) := by
  have hreg : [dst,rg 40,rg 41].Nodup := by
    simp [List.nodup_cons,(hoff 40).symm,(hoff 41).symm,hrg.ne (by decide : (40 : Fin 120) ≠ 41)]
  obtain ⟨v',hu,he⟩ := delimitedBankCopy_exec body dst (rg 40) (rg 41) hreg delimiter
    (headerOperandFrameJobs rg words) (by
      intro j hj
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj
      exact ⟨hoff _,hrg.ne (headerOperandSource_scratch r).1,hrg.ne (headerOperandSource_scratch r).2⟩) v S
    (by intro j hj; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj; exact hbank r) htmp hwork
  have hl : (headerOperandFrameJobs rg words).length = Fintype.card HeaderWorkRole := by
    simp [headerOperandFrameJobs,headerOperandRoles]
  have hf := delimitedBankFrames_length_le delimiter (headerOperandFrameJobs rg words) B (by
    intro j hj
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hj
    exact hwords r)
  have hc : delimitedBankCopyCost (headerOperandFrameJobs rg words) ≤
      Fintype.card HeaderWorkRole * (6 * B + 7) + 1 := by
    rw [delimitedBankCopyCost_eq delimiter,hl]
    rw [hl] at hf
    nlinarith only [hf]
  refine ⟨v',delimitedBankCopyCost (headerOperandFrameJobs rg words),hu,hc,?_⟩
  simpa only [headerOperandCopy,headerOperandFrame,headerOperandFrameJobs,List.map_map,Function.comp_def] using he

end
end IntegerMultBounds.MathlibTM2.Routing
