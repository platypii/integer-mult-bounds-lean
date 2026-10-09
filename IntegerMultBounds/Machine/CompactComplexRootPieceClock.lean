import IntegerMultBounds.Machine.CompactComplexRootPieceQueue
import IntegerMultBounds.Machine.LoopChain

/-! A fixed runtime digit-clock loop invokes its callback once per generated
root piece and advances the generated left boundary using paid arithmetic.
The callback interface frames every numeric/queue cell; its own execution
and cost remain explicit hypotheses until the recursive controller is wired. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceClock
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open CompactComplexRootPieceNumbers
open RecursiveChildQuotientsConstant (bits)
variable {a t q : ℕ}

def clock (st : State) (left count : ℕ) := put (put st 2 left) 4 count

def input (st : State) (left count : ℕ) (queue : Tapes 1 a) (tail : Tapes t a) : Tapes (43+(1+t)) a :=
  (bank (clock st left count)).append (queue.append tail)

def body (callback : Program (43+(1+t)) q a) :=
  seq callback (extend (CompactChildHeadersArithmetic.compile (a := a) piece).2 (1+t))
def test (sy : Fin (43+(1+t)) → Fin (a+4)) : Bool := decide (sy (Fin.castAdd (1+t) (Fin.castAdd 15 (4 : Fin 28)))≠blank)
def program (callback : Program (43+(1+t)) q a) := whileLoop (body callback) test

private theorem bits_nil_iff (n : ℕ) : bits n=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := RecursiveChildQuotientsConstant.bits_value n
    rw [h] at hv
    exact hv.symm
  · rintro rfl; rfl

private theorem descriptor_head_blank (xs : List Bool) :
    BinaryDescriptorStack.descriptor (a := a) xs 1=blank ↔ xs=[] := by
  cases xs with
  | nil => simp [BinaryDescriptorStack.descriptor,BinaryDescriptorStack.empty,putWord]
  | cons b bs =>
    rw [BinaryDescriptorStack.descriptor,List.map_cons,putWord_head]
    cases b <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem test_input (st : State) (left count : ℕ) (queue : Tapes 1 a) (tail : Tapes t a) :
    test (input st left count queue tail).reads=decide (count≠0) := by
  have hr : (input st left count queue tail).reads (Fin.castAdd (1+t) (Fin.castAdd 15 (4 : Fin 28)))=RadixZeroFill.encodedBinary (bits count) 1 := by
    simp only [input,Tapes.reads,bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    simp [ActiveRepairRankHeadersCommands.caller,clock,put]
  unfold test
  rw [hr,← BinaryDescriptorStackRoundtrip.descriptor_encoded]
  simp only [ne_eq,descriptor_head_blank,bits_nil_iff]

/-- The callback is run at the literal generated boundaries left+j*width.
The loop uses the physical clock, and its bound includes every callback,
scalar update and loop-control transition. -/
theorem runs (callback : Program (43+(1+t)) q a) (st : State)
    (left width count : ℕ) (h3 : st 3=some width) (h22 : st 22=none) (h23 : st 23=none)
    (queue : Tapes 1 a) (tails : ℕ → Tapes t a) (callbackCost : ℕ → ℕ)
    (hc : ∀ j<count, HoareTime callback
      (fun v => v=input st (left+j*width) (count-j) queue (tails j))
      (fun v => v=input st (left+j*width) (count-j) queue (tails (j+1))) (callbackCost j)) :
    HoareTime (program callback)
      (fun v => v=input st left count queue (tails 0))
      (fun v => v=input st (left+count*width) 0 queue (tails count))
      (∑ j ∈ Finset.range count,
        (callbackCost j+CompactChildHeadersArithmetic.scheduleCost piece
          (clock st (left+j*width) (count-j))+3)) := by
  have hp : ∀ j<count, HoareTime (body callback)
      (fun v => v=input st (left+j*width) (count-j) queue (tails j))
      (fun v => v=input st (left+(j+1)*width) (count-(j+1)) queue (tails (j+1)))
      (callbackCost j+CompactChildHeadersArithmetic.scheduleCost piece
        (clock st (left+j*width) (count-j))+1) := by
    intro j hj
    have hs := piece_runs (a := a) (clock st (left+j*width) (count-j))
      (left+j*width) width (count-j) (by omega)
      (by simp [clock,put]) (by simp [clock,put,h3]) (by simp [clock,put])
      (by simp [clock,put,h22]) (by simp [clock,put,h23])
    have he : pieceDone (clock st (left+j*width) (count-j)) (left+j*width) width (count-j)=
        clock st (left+(j+1)*width) (count-(j+1)) := by
      simp only [pieceDone,clock,put]
      have hl : left+j*width+width=left+(j+1)*width := by ring
      have hn : count-j-1=count-(j+1) := by omega
      rw [hl,hn]
      funext i
      by_cases h2 : i=2
      · subst i; simp
      by_cases h4 : i=4
      · subst i; simp
      simp [Function.update,h2,h4]
    rw [he] at hs
    simpa only [body,input,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (hc j hj).seq (hoare_extend_eq hs (queue.append (tails (j+1))))
  have h := while_chain_hoare (body callback) test
    (fun j => input st (left+j*width) (count-j) queue (tails j))
    (fun j => callbackCost j+CompactChildHeadersArithmetic.scheduleCost piece
      (clock st (left+j*width) (count-j))+1) count hp
    (by intro j hj; rw [test_input]; simp; omega)
    (by rw [test_input]; simp)
  simpa only [program,Nat.zero_mul,Nat.add_zero,Nat.sub_zero,Nat.sub_self,Nat.add_assoc,
    show (1 : ℕ)+2=3 by rfl] using h

end
end IntegerMultBounds.Machine.CompactComplexRootPieceClock
