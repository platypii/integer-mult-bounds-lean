module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeOriginHeaders

/-! Shared loading of the five ordinary halo geometry headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def haloRunHeaders : List (Fin 117 × Fin 16) :=
  [(97,0),(98,1),(100,2),(101,13),(103,14)]

def haloRunRawState (A s t band a b : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 0 s) 1 t) 2 band) 13 a) 14 b,[]⟩

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem initializeHaloRunHeaders_exec (W s t band a b : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hW : (S.R 115).length = W) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (104*W+137)+((s+t+band+a+b)*(4*W+10)+30*W+51) ∧
      Exec body (initializeOriginHeaders haloRunHeaders) (mk v S) n (mk v' S') ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate W tick)
        (haloRunRawState A s t band a b)) ∧ tblFr originReg S S' := by
  let value := fun r : Fin 117 => (S.R r).length
  have hsep : ∀ r ∈ haloRunHeaders, ∀ x, originReg x ≠ r.1 := by
    intro r hr x he
    have hv : 31 ≤ r.1.val := by
      simp only [haloRunHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    have hx := originReg_range x
    have hh := congrArg Fin.val he
    omega
  obtain ⟨v',S',n,hu,hn,he,hh,hf⟩ := initializeOriginHeaders_exec (body := body)
    haloRunHeaders hsep W value v S (by intros; rfl) hW h106 hblank
  have hstate : loadedOriginState value haloRunHeaders ⟨fun _ => 0,[]⟩ = haloRunRawState A s t band a b := by
    simp [loadedOriginState,haloRunHeaders,haloRunRawState,value,hs,ht,hband,ha,hb]
  have hcost : loadOriginListCost W value haloRunHeaders =
      (s+t+band+a+b)*(4*W+10)+30*W+51 := by
    simp [loadOriginListCost,haloRunHeaders,value,hs,ht,hband,ha,hb]
    ring
  exact ⟨v',S',n,hu,by simpa [hcost] using hn,he,by simpa only [hstate] using hh,hf⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
