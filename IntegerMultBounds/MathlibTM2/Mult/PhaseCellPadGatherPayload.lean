module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixPadRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Pad each gathered replica to the same core capacity in one linear pass.
The physical RHS list order is retained, including the gather's reversal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def paddedCoreGatherPayload {s : ℕ} (capacity width radius L : ℕ)
    (Fs : List (ZMod s → GaussianInt)) : List GaussianInt :=
  Fs.flatMap (fun F => tilePrefixPad (capacity*L) 0 (coreGatherPayload width radius L [F]))

theorem paddedCoreGatherPayload_length {s : ℕ} (capacity width radius L : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) :
    (paddedCoreGatherPayload capacity width radius L Fs).length = Fs.length*capacity*L := by
  have hrow (F : ZMod s → GaussianInt) :
      (tilePrefixPad (capacity*L) 0 (coreGatherPayload width radius L [F])).length = capacity*L := by
    apply tilePrefixPad_length
    simpa only [coreGatherPayload_length,List.length_singleton,Nat.one_mul] using Nat.mul_le_mul_right L hcapacity
  simp only [paddedCoreGatherPayload,List.length_flatMap,hrow,List.map_const',List.sum_replicate,smul_eq_mul]
  exact (Nat.mul_assoc ..).symm

private theorem gatherSymbols_rows {s : ℕ} (A width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    cstream A w (coreGatherPayload width radius L Fs) =
      (Fs.map (fun F => cstream A w (coreGatherPayload width radius L [F]))).flatten := by
  simp only [coreGatherPayload,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    cstream,←List.flatMap_def,List.flatMap_assoc]

theorem paddedCoreGatherPayload_symbols {s : ℕ} (A capacity width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) :
    cstream A w (paddedCoreGatherPayload capacity width radius L Fs) =
      Fs.flatMap (fun F => List.replicate ((capacity-(coreGatherIndices s width radius L).length)*L*w)
        (pairSym A false false)++cstream A w (coreGatherPayload width radius L [F])) := by
  have hflat (f : (ZMod s → GaussianInt) → List GaussianInt) :
      cstream A w (Fs.flatMap f) = Fs.flatMap (fun F => cstream A w (f F)) := by
    simp only [cstream,List.flatMap_assoc]
  rw [paddedCoreGatherPayload,hflat]
  apply List.flatMap_congr
  intro F _
  rw [cstream_tilePrefixPad]
  simp only [tilePrefixPad,length_cstream,coreGatherPayload_length,
    List.length_singleton,Nat.one_mul,←Nat.sub_mul]

/-- Removing dummy cores recovers the original ambient windows exactly. -/
theorem paddedCoreGatherPayload_drop {s : ℕ} (capacity width radius L : ℕ)
    (F : ZMod s → GaussianInt) :
    (paddedCoreGatherPayload capacity width radius L [F]).drop
      ((capacity-(coreGatherIndices s width radius L).length)*L) = coreGatherPayload width radius L [F] := by
  simp only [paddedCoreGatherPayload,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    tilePrefixPad,coreGatherPayload_length,List.length_singleton,Nat.one_mul,←Nat.sub_mul]
  simp

/-- A real core retains its row at the shifted, padded core address. -/
theorem paddedCoreGatherPayload_slot {s : ℕ} (capacity width radius L : ℕ)
    (F : ZMod s → GaussianInt) (i : Fin (coreGatherIndices s width radius L).length) :
    ((paddedCoreGatherPayload capacity width radius L [F]).drop
      ((capacity-(coreGatherIndices s width radius L).length+i.val)*L)).take L =
        packedInterval (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L F := by
  rw [Nat.add_mul,←List.drop_drop,paddedCoreGatherPayload_drop]
  exact coreGatherPayload_slot width radius L F i

/-- Counter-driven physical padding of the actual gathered archive. Source
order and borrowed suffix survive, and every padding/control counter is restored. -/
theorem padCoreGatherPayload_exec_within {s : ℕ}
    (rowSymbols padSymbols src acc saved tmp rows savedRows : Fin T)
    (hreg : [rowSymbols,padSymbols,src,acc,saved,tmp,rows,savedRows].Nodup)
    (capacity width radius L w : ℕ) (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrow : (S.R rowSymbols).length = (coreGatherIndices s width radius L).length*L*w)
    (hpad : (S.R padSymbols).length = (capacity-(coreGatherIndices s width radius L).length)*L*w)
    (hsrc : S.R src = cstream A w (coreGatherPayload width radius L Fs)++tail)
    (hacc : S.R acc = []) (hrows : (S.R rows).length = Fs.length)
    (hsavedRows : S.R savedRows = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ Fs.length*(6*(capacity*L*w)+13)+6 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (Fs.length*((capacity-(coreGatherIndices s width radius L).length)*L*w)+2*(4*(capacity*L*w)+10))) depth
        (prefixPadRows rowSymbols padSymbols src acc saved tmp rows savedRows (pairSym A false false))
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R src
          (cstream A w (paddedCoreGatherPayload capacity width radius L Fs)++tail))}) := by
  let xs := Fs.map (fun F => cstream A w (coreGatherPayload width radius L [F]))
  have hlen : ∀ x ∈ xs, x.length = (coreGatherIndices s width radius L).length*L*w := by
    intro x hx
    obtain ⟨F,_,rfl⟩ := List.mem_map.mp hx
    simp only [length_cstream,coreGatherPayload_length,List.length_singleton,Nat.one_mul]
  have hvolume : (coreGatherIndices s width radius L).length*L*w+
      (capacity-(coreGatherIndices s width radius L).length)*L*w = capacity*L*w := by
    have hadd : (coreGatherIndices s width radius L).length+
        (capacity-(coreGatherIndices s width radius L).length) = capacity := by omega
    calc
      _ = ((coreGatherIndices s width radius L).length+(capacity-(coreGatherIndices s width radius L).length))*L*w := by ring
      _ = _ := by rw [hadd]
  obtain ⟨v',n,hu,hn,he⟩ := prefixPadRows_exec_within rowSymbols padSymbols src acc saved tmp rows savedRows hreg
    (pairSym A false false) _ _ xs hlen tail v S hrow hpad
    (by
      change S.R src = (Fs.map (fun F => cstream A w (coreGatherPayload width radius L [F]))).flatten++tail
      rw [←gatherSymbols_rows]
      exact hsrc) hacc (by simpa only [xs,List.length_map] using hrows)
    hsavedRows hsaved htmp depth
  have hout : xs.flatMap (fun x => List.replicate ((capacity-(coreGatherIndices s width radius L).length)*L*w)
      (pairSym A false false)++x) = cstream A w (paddedCoreGatherPayload capacity width radius L Fs) := by
    rw [paddedCoreGatherPayload_symbols]
    simp only [xs,List.flatMap_map]
  rw [hout] at he
  simp only [xs,List.length_map,hvolume] at hn he
  exact ⟨v',n,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
