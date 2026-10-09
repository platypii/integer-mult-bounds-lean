import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBlock

/-! One real pass through a packed table. Each runtime-width row is emitted
L times, and the source head is physically restored after the whole pass. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPass
open CountedCopyReuse (empty binary)
open BinaryAddressOffsetRepeatData
noncomputable section

def bank (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns : List Bool) :=
  CountedLoopReuse.bank (BinaryAddressOffsetRepeatBlock.bank f g (fun _ => blank) p q 0 ws ls)
    empty (binary ns) 1 1

def state (blocks : List (List Bool)) (W L : ℕ) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool) (i : ℕ) :=
  BinaryAddressOffsetRepeatBlock.bank (putWord f p (blocks.flatten.map bitSymbol))
    (putWord g q ((expanded (blocks.take i) L).map bitSymbol)) (fun _ => blank)
    (p+(i*W : ℕ)) (q+(i*(L*W) : ℕ)) 0 ws ls

theorem source_block (blocks : List (List Bool)) (W : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f : ℤ → Fin 4) (p : ℤ) (i : ℕ) (hi : i<blocks.length) :
    putWord (putWord f p (blocks.flatten.map bitSymbol)) (p+(i*W : ℕ)) (blocks[i].map bitSymbol)=
      putWord f p (blocks.flatten.map bitSymbol) := by
  have hu' : BlockRotationData.Uniform W (blocks.map (List.map (bitSymbol (a := 0)))) := by
    intro xs hx; obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx; simpa using hu ys hy
  have hh := FiberShift.source_fiber f p (blocks.map (List.map bitSymbol)) W i hu' (by simpa using hi)
  simpa only [List.getElem_map,List.map_flatten] using hh

theorem body_hoare (blocks : List (List Bool)) (W L : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool) (hw : Counter.value ws=W) (hl : Counter.value ls=L)
    (i : ℕ) (hi : i<blocks.length) :
    HoareTime BinaryAddressOffsetRepeatBlock.program (fun z => z=state blocks W L f g p q ws ls i)
      (fun z => z=state blocks W L f g p q ws ls (i+1))
      (L*(2*W+9)+8*W+7*ws.length+7*ls.length+40) := by
  have hrow := hu blocks[i] (List.getElem_mem hi)
  have hh := BinaryAddressOffsetRepeatBlock.runs blocks[i]
    (putWord f p (blocks.flatten.map bitSymbol)) (putWord g q ((expanded (blocks.take i) L).map bitSymbol))
    (p+(i*W : ℕ)) (q+(i*(L*W) : ℕ)) ws ls L (by omega) hl
  rw [source_block blocks W hu f p i hi,hrow] at hh
  have hlength : (expanded (blocks.take i) L).length=i*(L*W) := by
    rw [expanded_length _ W L (fun xs hx => hu xs (List.mem_of_mem_take hx)),List.length_take,Nat.min_eq_left (by omega)]
  have ho : putWord (putWord g q ((expanded (blocks.take i) L).map bitSymbol))
      (q+(i*(L*W) : ℕ)) ((copies blocks[i] L).map bitSymbol) =
      putWord g q ((expanded (blocks.take (i+1)) L).map bitSymbol) := by
    rw [expanded_succ blocks L i hi,List.map_append]
    simpa only [List.length_map,hlength] using putWord_append_forward g q
      ((expanded (blocks.take i) L).map bitSymbol) ((copies blocks[i] L).map bitSymbol)
  have hp : p+(i*W : ℕ)+W=p+((i+1)*W : ℕ) := by push_cast; ring
  have hq : q+(i*(L*W) : ℕ)+(L*W : ℕ)=q+((i+1)*(L*W) : ℕ) := by push_cast; ring
  simpa only [state,ho,hp,hq] using hh

def loop := CountedLoopReuse.program BinaryAddressOffsetRepeatBlock.program

def loopCost (W L N : ℕ) (ws ls ns : List Bool) :=
  N*(L*(2*W+9)+8*W+7*ws.length+7*ls.length+46)+7*ns.length+16

theorem loop_hoare (blocks : List (List Bool)) (W L : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns : List Bool)
    (hw : Counter.value ws=W) (hl : Counter.value ls=L) (hn : Counter.value ns=blocks.length) :
    HoareTime loop (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol)) g p q ws ls ns)
      (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol))
        (putWord g q ((expanded blocks L).map bitSymbol))
        (p+(blocks.length*W : ℕ)) (q+(blocks.length*(L*W) : ℕ)) ws ls ns)
      (loopCost W L blocks.length ws ls ns) := by
  have hh := CountedLoopReuse.loop_hoare BinaryAddressOffsetRepeatBlock.program ns blocks.length
    (state blocks W L f g p q ws ls) (fun _ => L*(2*W+9)+8*W+7*ws.length+7*ls.length+40) hn
    (body_hoare blocks W L hu f g p q ws ls hw hl)
  apply hh.consequence
  · intro z hz; simpa only [state,bank,List.take_zero,expanded,List.map_nil,List.flatten_nil,putWord,Nat.zero_mul,Nat.cast_zero,add_zero] using hz
  · intro z hz; simpa only [state,bank,List.take_length] using hz
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,loopCost]; nlinarith

def rewind := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (0 : Fin 9))
def program := seq loop rewind

theorem rewind_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns : List Bool)
    (hf : f (p-1)=blank) :
    HoareTime rewind (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (p+xs.length) q ws ls ns)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) g p q ws ls ns) (xs.length+2) := by
  have hr := ReturnOrigin.return_hoare_at f p (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs) hf
  simp only [List.length_map] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (0 : Fin 9))
      (bank (putWord f p (xs.map bitSymbol)) g (p+xs.length) q ws ls ns)=
      (ReturnOrigin.cfg (putWord f p (xs.map bitSymbol)) (p+xs.length) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at hr (FiniteReturnStackAt.placement (0 : Fin 9)) _ ha).consequence
    (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (putWord f p (xs.map bitSymbol)) p)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (W L N : ℕ) (ws ls ns : List Bool) := loopCost W L N ws ls ns+N*W+3

theorem runs (blocks : List (List Bool)) (W L : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns : List Bool)
    (hw : Counter.value ws=W) (hl : Counter.value ls=L) (hn : Counter.value ns=blocks.length)
    (hf : f (p-1)=blank) :
    HoareTime program (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol)) g p q ws ls ns)
      (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol))
        (putWord g q ((expanded blocks L).map bitSymbol)) p (q+(blocks.length*(L*W) : ℕ)) ws ls ns)
      (cost W L blocks.length ws ls ns) := by
  have h0 := loop_hoare blocks W L hu f g p q ws ls ns hw hl hn
  have h1 := rewind_hoare blocks.flatten f (putWord g q ((expanded blocks L).map bitSymbol)) p
    (q+(blocks.length*(L*W) : ℕ)) ws ls ns hf
  rw [BlockRotationData.uniform_volume W blocks hu] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPass
