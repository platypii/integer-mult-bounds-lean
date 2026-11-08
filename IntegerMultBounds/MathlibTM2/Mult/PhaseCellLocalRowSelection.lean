module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.NLogN.PhaseCellLatticeArgs

/-! The inverse's C is nearest-row selection. A restoring ordered sweep reads
it directly from a stored target window and emits the existing source RHS ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

/-- Integer division uses exactly the global row selector's upward tie rule. -/
theorem nearestNatural_rowIndexNat {s t : ℕ} [NeZero s] (j : ZMod s) :
    nearestNatural s t j.val = rowIndexNat s t j := by
  unfold rowIndexNat
  have he := nearestQ_eq s t (NeZero.pos s) (j.val : ℤ)
  simp only [Int.cast_natCast] at he
  rw [←he]
  rw [nearestNatural_cast]
  simp

theorem nearestNatural_mono (s t : ℕ) : Monotone (nearestNatural s t) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left (2*t) hij) s)

def localRowOrigins (s t a n origin w : ℕ) : List ℕ :=
  (List.range n).map fun j => (nearestNatural s t (a+j)-origin)*w

theorem localRowOrigins_ordered (s t a n origin w : ℕ) :
    (localRowOrigins s t a n origin w).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  apply (show (List.range n).Pairwise (· < ·) from List.pairwise_lt_range).imp
  intro i j hij
  exact Nat.mul_le_mul_right w (Nat.sub_le_sub_right (nearestNatural_mono s t (by omega)) origin)

theorem localRowOrigins_payload {s t : ℕ} [NeZero s] (A w a n origin span : ℕ)
    (F : ZMod t → GaussianInt) (hsource : a+n ≤ s) (htarget : origin+span ≤ t)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span) :
    (localRowOrigins s t a n origin w).flatMap
      (fun p => ((cstream A w (packedInterval origin span F)).drop p).take w) =
      cstream A w (packedInterval a n (fun j => F (rowIndex s t j))) := by
  have hp : packedInterval a n (fun j => F (rowIndex s t j)) =
      (List.range n).map (fun j => F ((nearestNatural s t (a+j) : ℕ) : ZMod t)) := by
    apply List.ext_getElem (by rw [packedInterval_length _ hsource]; simp)
    intro j hj hj'
    have hjn : j < n := by simpa using hj'
    rw [packedInterval_get _ hsource hjn]
    simp only [List.getElem_map,List.getElem_range,rowIndex]
    congr 1
    rw [←nearestNatural_rowIndexNat]
    rw [ZMod.val_natCast_of_lt (show a+j < s by omega)]
  rw [hp]
  simp only [localRowOrigins,List.flatMap_map,cstream,List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  have hjn := List.mem_range.mp hj
  have hwj := hwindow j hjn
  have hcrop : ((cstream A w (packedInterval origin span F)).drop
      ((nearestNatural s t (a+j)-origin)*w)).take w =
      csyms A w (F ((nearestNatural s t (a+j) : ℕ) : ZMod t)) := by
    rw [cstream_drop]
    have ht := cstream_take A w 1 ((packedInterval origin span F).drop (nearestNatural s t (a+j)-origin))
    simp only [Nat.one_mul] at ht
    rw [ht]
    rw [packedInterval_crop F (show nearestNatural s t (a+j)-origin+1 ≤ span by omega)]
    rw [Nat.add_sub_of_le hwj.1,packedInterval_singleton F (show nearestNatural s t (a+j) < t by omega)]
    simp [cstream]
  exact hcrop

/-- One real restoring tape sweep converts a target window to the source
interval expected by the principal solver. The source and all controls restore. -/
theorem localRowSelection_exec {T Q A s t : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P T Q A U}
    (dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR : Fin T)
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    (w a n origin span : ℕ) (F : ZMod t → GaussianInt)
    (hn : 0 < n) (hsource : a+n ≤ s) (htarget : origin+span ≤ t)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = (match localRowOrigins s t a n origin w with
      | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps)))
    (hs : S.R src = cstream A w (packedInterval origin span F))
    (hrow : (S.R rowCount).length = 1) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n*(14*w+25)+12*(span*w)+6*w+38 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (packedInterval a n (fun j => F (rowIndex s t j)))++S.R dst))}) := by
  have hnonempty : localRowOrigins s t a n origin w ≠ [] := by
    intro hh
    have hl := congrArg List.length hh
    simp only [localRowOrigins,List.length_map,List.length_range,List.length_nil] at hl
    omega
  have hfit : ∀ p ∈ localRowOrigins s t a n origin w,
      p+1*w ≤ (cstream A w (packedInterval origin span F)).length := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hh := hwindow j (List.mem_range.mp hj)
    rw [length_cstream,packedInterval_length F htarget]
    have hb : nearestNatural s t (a+j)-origin+1 ≤ span := by omega
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w hb
  obtain ⟨v',m,hu,hm,he⟩ := orderedGather_exec hreg 1 w (localRowOrigins s t a n origin w)
    (cstream A w (packedInterval origin span F)) hnonempty (localRowOrigins_ordered s t a n origin w)
    hfit v S hc hs hrow hw hclean
  refine ⟨v',m,hu,?_,?_⟩
  · simpa only [localRowOrigins,List.length_map,List.length_range,length_cstream,
      packedInterval_length F htarget,Nat.mul_one,Nat.one_mul] using hm
  · simpa only [Nat.one_mul,localRowOrigins_payload A w a n origin span F hsource htarget hwindow] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
