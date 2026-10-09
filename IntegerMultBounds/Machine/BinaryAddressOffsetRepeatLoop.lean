import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPass

/-! Runtime-counted replay of the whole expanded table. Every pass rereads
and rewinds the actual base table; output copies occupy consecutive cells. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatLoop
open CountedCopyReuse (empty binary)
open BinaryAddressOffsetRepeatData
noncomputable section

def bank (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns ks : List Bool) :=
  CountedLoopReuse.bank (BinaryAddressOffsetRepeatPass.bank f g p q ws ls ns) empty (binary ks) 1 1

def state (blocks : List (List Bool)) (L : ℕ) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns : List Bool) (i : ℕ) :=
  BinaryAddressOffsetRepeatPass.bank (putWord f p (blocks.flatten.map bitSymbol))
    (putWord g q ((copies (expanded blocks L) i).map bitSymbol))
    p (q+(i*(expanded blocks L).length : ℕ)) ws ls ns

def program := CountedLoopReuse.program BinaryAddressOffsetRepeatPass.program

def cost (W L N K : ℕ) (ws ls ns ks : List Bool) :=
  K*(BinaryAddressOffsetRepeatPass.cost W L N ws ls ns+6)+7*ks.length+16

theorem step (blocks : List (List Bool)) (W L : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns : List Bool)
    (hw : Counter.value ws=W) (hl : Counter.value ls=L) (hn : Counter.value ns=blocks.length)
    (hf : f (p-1)=blank) (i : ℕ) :
    HoareTime BinaryAddressOffsetRepeatPass.program
      (fun z => z=state blocks L f g p q ws ls ns i)
      (fun z => z=state blocks L f g p q ws ls ns (i+1))
      (BinaryAddressOffsetRepeatPass.cost W L blocks.length ws ls ns) := by
  have hh := BinaryAddressOffsetRepeatPass.runs blocks W L hu f
    (putWord g q ((copies (expanded blocks L) i).map bitSymbol)) p
    (q+(i*(expanded blocks L).length : ℕ)) ws ls ns hw hl hn hf
  have he : putWord (putWord g q ((copies (expanded blocks L) i).map bitSymbol))
      (q+(i*(expanded blocks L).length : ℕ)) ((expanded blocks L).map bitSymbol) =
      putWord g q ((copies (expanded blocks L) (i+1)).map bitSymbol) := by
    rw [copies_succ,List.map_append]
    simpa only [List.length_map,copies_length] using putWord_append_forward g q
      ((copies (expanded blocks L) i).map bitSymbol) ((expanded blocks L).map bitSymbol)
  have hp : q+(i*(expanded blocks L).length : ℕ)+(blocks.length*(L*W) : ℕ)=
      q+((i+1)*(expanded blocks L).length : ℕ) := by
    rw [expanded_length blocks W L hu]; push_cast; ring
  simpa only [state,he,hp] using hh

theorem runs (blocks : List (List Bool)) (W L K : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (f g : ℤ → Fin 4) (p q : ℤ) (ws ls ns ks : List Bool)
    (hw : Counter.value ws=W) (hl : Counter.value ls=L) (hn : Counter.value ns=blocks.length)
    (hk : Counter.value ks=K) (hf : f (p-1)=blank) :
    HoareTime program (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol)) g p q ws ls ns ks)
      (fun z => z=bank (putWord f p (blocks.flatten.map bitSymbol))
        (putWord g q ((copies (expanded blocks L) K).map bitSymbol))
        p (q+(K*(expanded blocks L).length : ℕ)) ws ls ns ks)
      (cost W L blocks.length K ws ls ns ks) := by
  have hh := CountedLoopReuse.loop_hoare BinaryAddressOffsetRepeatPass.program ks K
    (state blocks L f g p q ws ls ns) (fun _ => BinaryAddressOffsetRepeatPass.cost W L blocks.length ws ls ns)
    hk (fun i _ => step blocks W L hu f g p q ws ls ns hw hl hn hf i)
  apply hh.consequence
  · intro z hz; simpa only [state,bank,copies_zero,List.map_nil,putWord,Nat.zero_mul,Nat.cast_zero,add_zero] using hz
  · intro z hz; exact hz
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,cost]; nlinarith

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatLoop
