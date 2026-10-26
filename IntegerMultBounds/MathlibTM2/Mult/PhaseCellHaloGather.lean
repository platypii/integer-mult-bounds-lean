module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGatherData
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! One restoring ambient-line sweep constructs the clipped group's exact RHS.
The row-symbol count is generated from retained dimensions. Delimited advance
controls are explicit inputs here; their generation remains an outer stage. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloGatherControls (A s t band a b L w : ℕ) : List (Fin (A+4)) :=
  match haloSymbolOrigins s t band a b L w with
  | [] => []
  | p::ps => gatherControls A (p::windowAdvances p ps)

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem haloGather_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp,
      initialControl, initialSource, rowCount, wordR].Nodup)
    {s : ℕ} [NeZero s] (t band a b L w : ℕ) (C : ZMod s → GaussianInt)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = haloGatherControls A s t band a b L w)
    (hs : S.R src = cstream A w (chirpLine s C))
    (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl, advance, window, acc, current, savedSource, buf, tmp,
      initialControl, initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (haloLengthGroup s t band a b L).length*(14*L*w+25)+12*s*w+6*L*w+9*L+29 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w ((List.range (haloLengthGroup s t band a b L).length).flatMap
            (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C))) ++ S.R dst)) }) := by
  have hnonempty : haloSymbolOrigins s t band a b L w ≠ [] := by
    intro he
    have hh : 0 < (haloSymbolOrigins s t band a b L w).length := by simpa [haloSymbolOrigins] using hgroup
    rw [he] at hh
    simp at hh
  obtain ⟨v',n,hu,hn,he⟩ := orderedGather_exec (body := body) hreg L w
    (haloSymbolOrigins s t band a b L w) (cstream A w (chirpLine s C)) hnonempty
    (haloSymbolOrigins_ordered s t band a b L w)
    (by simpa using haloSymbolOrigins_fit s t band a b L w) v S
    (by
      cases ho : haloSymbolOrigins s t band a b L w with
      | nil => simpa only [haloGatherControls,ho] using hc
      | cons p ps => simpa only [haloGatherControls,ho] using hc) hs hrow hw hclean
  refine ⟨v',n,hu,by simpa [haloSymbolOrigins,Nat.mul_assoc] using hn,?_⟩
  change Exec body _ _ n (mk v' { S with R := (Function.update S.R dst
    (haloGatherRows t band a b L w C ++ S.R dst)) }) at he
  simpa only [haloGatherRows_eq_rhs] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
