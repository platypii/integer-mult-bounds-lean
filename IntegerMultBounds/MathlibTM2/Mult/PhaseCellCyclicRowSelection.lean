module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowSelection

/-! Unwrapped nearest-row offsets read cyclic storage in original ambient
coordinates. Crossing a period changes storage indices, not matrix entries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem nearestNatural_period (s t j m : ℕ) (hs : 0 < s) :
    nearestNatural s t (j+m*s) = nearestNatural s t j+m*t := by
  unfold nearestNatural
  rw [show 2*t*(j+m*s)+s = (2*t*j+s)+(m*t)*(2*s) by ring,
    Nat.add_mul_div_right _ _ (by omega)]

theorem rowIndex_natCast {s t : ℕ} [NeZero s] (j : ℕ) :
    rowIndex s t (j : ZMod s) = (nearestNatural s t j : ZMod t) := by
  have hj : j%s+(j/s)*s = j := by simpa only [Nat.mul_comm] using Nat.mod_add_div j s
  have hperiod := nearestNatural_period s t (j%s) (j/s) (NeZero.pos s)
  rw [hj] at hperiod
  unfold rowIndex
  rw [←nearestNatural_rowIndexNat]
  simp only [ZMod.val_natCast]
  rw [hperiod]
  simp

theorem cyclicRowOrigins_payload {s t : ℕ} [NeZero s] (A w a n origin span : ℕ)
    (F : ZMod t → GaussianInt)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span) :
    (localRowOrigins s t a n origin w).flatMap
      (fun p => ((cstream A w (cyclicInterval origin span F)).drop p).take w) =
      cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j))) := by
  have hp : cyclicInterval a n (fun j => F (rowIndex s t j)) =
      (List.range n).map (fun j => F ((nearestNatural s t (a+j) : ℕ) : ZMod t)) := by
    simp only [cyclicInterval,rowIndex_natCast]
  rw [hp]
  simp only [localRowOrigins,List.flatMap_map,cstream,List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  have hh := hwindow j (List.mem_range.mp hj)
  have hindex : nearestNatural s t (a+j)-origin < span := by omega
  have hread := cstream_word (A := A) w (cyclicInterval origin span F) []
    (nearestNatural s t (a+j)-origin) (by simpa using hindex)
  simp only [List.append_nil] at hread
  rw [cyclicInterval_get F hindex,Nat.add_sub_of_le hh.1] at hread
  simpa only [cstream] using hread

theorem cyclicRowSelection_exec {T Q A s t : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P T Q A U}
    (dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR : Fin T)
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    (w a n origin span : ℕ) (F : ZMod t → GaussianInt)
    (hn : 0 < n)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = (match localRowOrigins s t a n origin w with
      | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps)))
    (hs : S.R src = cstream A w (cyclicInterval origin span F))
    (hrow : (S.R rowCount).length = 1) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n*(14*w+25)+12*(span*w)+6*w+38 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))++S.R dst))}) := by
  have hnonempty : localRowOrigins s t a n origin w ≠ [] := by
    intro hh
    have hl := congrArg List.length hh
    simp only [localRowOrigins,List.length_map,List.length_range,List.length_nil] at hl
    omega
  have hfit : ∀ p ∈ localRowOrigins s t a n origin w,
      p+1*w ≤ (cstream A w (cyclicInterval origin span F)).length := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hh := hwindow j (List.mem_range.mp hj)
    rw [length_cstream,cyclicInterval_length origin span F]
    have hb : nearestNatural s t (a+j)-origin+1 ≤ span := by omega
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w hb
  obtain ⟨v',m,hu,hm,he⟩ := orderedGather_exec hreg 1 w (localRowOrigins s t a n origin w)
    (cstream A w (cyclicInterval origin span F)) hnonempty (localRowOrigins_ordered s t a n origin w)
    hfit v S hc hs hrow hw hclean
  refine ⟨v',m,hu,?_,?_⟩
  · simpa only [localRowOrigins,List.length_map,List.length_range,length_cstream,
      cyclicInterval_length origin span F,Nat.mul_one,Nat.one_mul] using hm
  · simpa only [Nat.one_mul,cyclicRowOrigins_payload A w a n origin span F hwindow] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
