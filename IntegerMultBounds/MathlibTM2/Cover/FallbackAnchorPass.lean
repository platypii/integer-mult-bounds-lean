module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordLoop

/-! Generate the class signs, run the anchor over the queued records, and restore tape order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8 ActualAffineScaling RecursiveInterchangeLayout
variable {T n m f b W : ℕ} {P U : Type}
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

def signedInputs (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod prime))
    (w N : ℕ) (a : ℕ → Array n f b W) :=
  (List.range N).map fun j =>
    let M := table (LabelStock.residue m w 1 j)
    (negativeAnchor (classPivots M) M,a j)

/-- The program is fixed before the descriptor and payloads are supplied. The same queue
holds its output in forward order, followed by the original caller suffix. -/
theorem anchorPass (r : Fin 6 ↪ Fin T)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod prime))
    (body : P → Pr P (size n+T) ((anchorProgram n true).1+(anchorProgram n false).1+1) prime U)
    (rs : List (Pair (size n+T))) (hk : rs.length = m*m) (parents saved : Fin (size n+T))
    (layout : (parents :: saved :: (slots rs ++ [port n r 4])).Nodup) :
    ∃ prog, ∀ (v : Descriptor) (w B : ℕ), 0 < w → v.beforeH = B*prime^(m*(w*m)) →
      ∀ (f b W : ℕ), 0 < f → 0 < b → 0 < W → ∀ (a : ℕ → Array n f b W)
      (u : HS _ _ prime U) (S : Stacks _ prime) (tail : List (Fin (prime+4))),
      let inputs := signedInputs table w (LabelMask.records v) a
      Ready n f b W S → ready (prime^(w-1)) S.R rs → S.R saved = [] →
      (S.R parents).length = v.beforeRows*v.rows*B →
      (S.R (port n r 0)).length = (modulus b)^((n+1)*f)*W →
      S.R (port n r 1) = inputs.flatMap (fun a => payloadWord a.2) ++ tail →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), S.R (port n r i) = []) →
      ∃ outs z F t, inputs.Forall₂ Correct outs ∧ Exec body prog (mk u S) t (mk z F) ∧
        t ≤ (v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4 +
          ((inputs.map (fun a => cost n T f b W a.1 + 2)).sum + 2) +
          (2*(LabelMask.records v*((modulus b)^((n+1)*f)*W))+2) ∧
        Ready n f b W F ∧ z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
        ∀ j : Fin T, F.R (Fin.natAdd (size n) j) =
          if j = r 1 then outs.flatMap payloadWord ++ tail else S.R (Fin.natAdd (size n) j) := by
  obtain ⟨writer,write⟩ := signStream_writes body table rs hk (port n r 4) parents saved layout
  refine ⟨.seq writer (.seq (scan n r) (moveR (port n r 5) (port n r 1) id)),?_⟩
  intro v w B hw hv f b W hf hb hW a u S tail inputs neutral radix clean nparents width queue fresh
  obtain ⟨u',c,hu,hc,emit⟩ := write v w B hw hv u S ⟨radix,clean,nparents⟩
  have cleared (i : Fin 6) (hi : i ∈ ([2,3,4,5] : List (Fin 6))) := fresh i hi
  let M : Stacks _ prime := {S with R := Function.update S.R (port n r 4) (signStream table w (LabelMask.records v) ++ S.R (port n r 4))}
  have disjoint (i : Fin (size n)) (j : Fin T) : Fin.castAdd T i ≠ Fin.natAdd _ j := by
    intro h
    have e := congrArg Fin.val h
    simp at e
    omega
  obtain ⟨outs,z,F,t,hout,run,ht,readyF,zu,zi,zo,frame⟩ := scan_runs r hf hb hW body inputs u' M tail
    (by simpa [Ready,M,port,disjoint] using neutral)
    (by simpa [M,port,r.injective.eq_iff] using width)
    (by simpa [M,port,r.injective.eq_iff] using queue)
    (by simpa [M,port,r.injective.eq_iff] using cleared 2 (by decide))
    (by simpa [M,port,r.injective.eq_iff] using cleared 3 (by decide))
    (by simp [M,cleared 4 (by decide),inputs,signedInputs,signStream,List.map_map,Function.comp_def])
  obtain ⟨y,yu,restore⟩ := moveR_exec body (port n r 5) (port n r 1)
    (by simp [port,r.injective.eq_iff]) id z F
  have archive : F.R (port n r 5) = (outs.flatMap payloadWord).reverse := by
    simpa [M,port,r.injective.eq_iff,show S.R (Fin.natAdd (size n) (r 5)) = [] from cleared 5 (by decide)] using frame (r 5)
  have suffix : F.R (port n r 1) = tail := by simpa [r.injective.eq_iff] using frame (r 1)
  refine ⟨outs,y,_,_,hout,.seq emit (.seq run restore),?_,?_,yu.trans (zu.trans hu),zi,zo,?_⟩
  · have volume (l : List (Array n f b W)) :
        (l.flatMap payloadWord).length = l.length * ((modulus b)^((n+1)*f)*W) := by
      induction l with
      | nil => simp
      | cons a l ih => simp [ih,payloadWord,Nat.add_mul,Nat.add_comm]
    have records : outs.length = LabelMask.records v := by
      simpa [inputs,signedInputs] using hout.length_eq.symm
    rw [archive,List.length_reverse,volume,records]
    omega
  · simpa [Ready,movedR,port,disjoint] using readyF
  · intro j
    simp only [movedR,Function.update_apply,archive,List.map_id_fun,suffix]
    by_cases h : j = r 1 <;> by_cases h' : j = r 5 <;> by_cases h'' : j = r 4 <;>
      simp_all [M,port,r.injective.eq_iff]

/-- At a physical label address, the returned payload uses the sign of the full-width
elimination diagonal for that label. -/
theorem output_at {w N : ℕ} (hw : 0 < w)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod prime))
    (g : LabelPadding.Label m w) (G : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod (prime^w)))
    (hg : G.det = 1 ∨ G.det = -1)
    (lift : (LabelRing.res prime w hw).mapMatrix G = table ((LabelRing.res prime w hw).mapMatrix g))
    (a : ℕ → Array n f b W) (outs : List (Array n f b W))
    (result : (signedInputs table w N a).Forall₂ Correct outs) (p : ℕ)
    (index : p*(prime^w)^(m*m)+(LabelAddress.address g).val < N) :
    let j := p*(prime^w)^(m*m)+(LabelAddress.address g).val
    let pivots := classPivots (table ((LabelRing.res prime w hw).mapMatrix g))
    ∃ negative out, outs[j]? = some out ∧ Correct (negative,a j) out ∧
      (signStream (A := prime) table w N)[j]? = some (bitSymbol negative) ∧
      Itinerary.Valid pivots G (n+1) ∧ (Itinerary.run pivots G (n+1)).det = if negative then -1 else 1 := by
  let j := p*(prime^w)^(m*m)+(LabelAddress.address g).val
  have lo : j < (signedInputs table w N a).length := by simpa [signedInputs,j] using index
  have hi : j < outs.length := result.length_eq ▸ lo
  obtain ⟨negative,bit,valid,det⟩ := signStream_at (A := prime) table hw g G p N hg lift index
  refine ⟨negative,outs[j],List.getElem?_eq_getElem hi,?_,bit,valid,det⟩
  have bitEq := congrArg (Option.map symBit) bit
  simp [signStream,index] at bitEq
  simpa [signedInputs,List.get_eq_getElem,j,bitEq] using result.get lo hi

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
