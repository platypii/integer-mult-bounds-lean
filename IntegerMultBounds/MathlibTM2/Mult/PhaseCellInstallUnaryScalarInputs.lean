module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderQueue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeScalarBank

/-! Generate scalar input words from retained unary rulers, then install them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def installUnaryScalarInputs (rg : TblR n → Fin T) (header word saved tmp carry : Fin T)
    (ports : List (Fin n × Fin T)) : Pr P T Q A U :=
  .seq (binaryHeaderQueue (rg .wr) word saved tmp header carry (ports.map Prod.snd))
    (installScalarInputs rg header (ports.map Prod.fst))

theorem installUnaryScalarInputs_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry : Fin T) (hheader : ∀ r, rg r ≠ header)
    (ports : List (Fin n × Fin T))
    (hregs : ∀ src ∈ ports.map Prod.snd, [src,rg .wr,word,saved,tmp,header].Nodup)
    (B : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .wr) = wl)
    (hblank : ∀ r : TblR n, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) :
    ∃ v' F steps, v'.user = v.user ∧
      steps ≤ binaryHeaderQueueCost S.R B (ports.map Prod.snd)+n*(4*B+4)+ports.length*(8*B+8)+2 ∧
      Exec body (installUnaryScalarInputs rg header word saved tmp carry ports) (Host.mk v S) steps (Host.mk v' F) ∧
      tblHolds rg F (tblRho B wl [] (loadedBinaryState
        (ports.map (fun a => (a.1,(S.R a.2).length))) ⟨fun _ => 0,[]⟩)) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k, (∀ r, rg r ≠ k) → F.R k = S.R k) := by
  obtain ⟨v₁,steps₁,hu₁,hn₁,ht₁⟩ := binaryHeaderQueue_exec (body := body) (rg .wr) word saved tmp header carry
    (ports.map Prod.snd) hregs v S hwork 0
  let M : Stacks T A := {S with R := (Function.update S.R header
    (((ports.map Prod.snd).flatMap (fun k => binSyms B (S.R k).length))++S.R header))}
  have hB : (S.R (rg .wr)).length = B := by rw [hwidth,hwl]
  rw [hB] at hn₁ ht₁
  have he₁ : Exec body (binaryHeaderQueue (rg .wr) word saved tmp header carry (ports.map Prod.snd))
      (Host.mk v S) steps₁ (Host.mk v₁ M) := ht₁.toExec
  let rs := ports.map (fun a => (a.1,(S.R a.2).length))
  have hpacket : M.R header = rs.flatMap (fun a => binSyms B a.2)++S.R header := by
    simp only [M,rs,Function.update_self,List.flatMap_map]
  obtain ⟨v₂,F,hu₂,he₂,hh₂,hhead,hin,hout,hL,hframe⟩ := installScalarInputs_exec (body := body) rg hrg header hheader
    rs B wl hwl (S.R header) v₁ M
    (by simpa only [M,Function.update_of_ne (hheader .wr)] using hwidth)
    (by intro r hr; simpa only [M,Function.update_of_ne (hheader r)] using hblank r hr) hpacket
  refine ⟨v₂,F,steps₁+(n*(4*B+4)+rs.length*(8*B+8)+2),hu₂.trans hu₁,?_,?_,hh₂,hin,hout,hL,?_⟩
  · simp only [rs,List.length_map]
    omega
  · simpa only [installUnaryScalarInputs,rs,List.map_map,Function.comp_def] using Exec.seq he₁ he₂
  · intro k hoff
    by_cases hk : k = header
    · subst k; exact hhead
    · exact (hframe k hk hoff).trans (Function.update_of_ne hk _ _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
