module

public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal
public import IntegerMultBounds.MathlibTM2.Host.GatherRecords

/-! Stable partition of fixed-width label records by the retained residue-class mask. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelSplit
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Gather the rejected records first, then prepend the accepted records to them. -/
def program (src mask width symbols ts tm acc out : Fin T) : Pr P T Q A U :=
  .seq (gatherRecords src mask width symbols ts tm acc out src (fun x => !(symBit x)))
    (gatherRecords src mask width symbols ts tm acc out src symBit)

theorem split_exec {src mask width symbols ts tm acc out : Fin T}
    (hr : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (xs : List ℕ) (keep : ℕ → Bool) (word : ℕ → List (Fin (A+4))) (w : ℕ)
    (hw : ∀ i ∈ xs, (word i).length = w)
    (u : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hs : S.R src = xs.flatMap word ++ tail)
    (hm : S.R mask = (xs.map keep).map bitSymbol) (hlen : (S.R width).length = w)
    (hf : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ u' n, u'.user = u.user ∧ n ≤ 2*(xs.length*(16*w+10)+16) ∧
      Exec body (program src mask width symbols ts tm acc out) (mk u S) n
        (mk u' {S with R := Function.update S.R out ((xs.filter keep).flatMap word ++ (xs.filter (fun i => !(keep i))).flatMap word ++ S.R out)}) := by
  let pass (f : Bool → Bool) := gatherRecords (A := A) (P := P) (Q := Q) (U := U)
    src mask width symbols ts tm acc out src (fun x => f (symBit x))
  have run (f : Bool → Bool) (v : HS T Q A U) (M : Stacks T A)
      (same : ∀ k, k ≠ out → M.R k = S.R k) :
      ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(16*w+10)+16 ∧
        Exec body (pass f) (mk v M) n (mk v' {M with R := Function.update M.R out ((xs.filter (fun i => f (keep i))).flatMap word ++ M.R out)}) := by
    have h := hr
    regs_ne h
    obtain ⟨v',n,hu,hn,he⟩ := gatherRecords_exec (body := body) (cs := src) hr
      ((xs.map keep).map bitSymbol) (xs.map word) w (fun x => f (symBit x))
      (by simp) (by simpa using hw) tail v M
      (by simpa [same src (by assumption), List.flatMap_def] using hs)
      ((same mask (by assumption)).trans hm) (by rwa [same width (by assumption)])
      (by intro k hk; rw [same k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> assumption)]; exact hf k hk)
    refine ⟨v',n,hu,by simpa using hn,?_⟩
    simpa [pass,List.map_map,Function.comp_def,symBit_bitSymbol,gatherSymbols_filter,List.flatMap_def] using he
  obtain ⟨v,n,hu,hn,he⟩ := run Bool.not u S (fun _ _ => rfl)
  obtain ⟨v',n',hu',hn',he'⟩ := run id v {S with R := Function.update S.R out ((xs.filter (fun i => !(keep i))).flatMap word ++ S.R out)} (fun k hk => Function.update_of_ne hk _ _)
  refine ⟨v',n+n',hu'.trans hu,by omega,?_⟩
  simpa [program,pass,List.append_assoc] using Exec.seq he he'

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open LabelTraversal

/-- Generate the residue mask and stably split the padded records, retaining the mask. -/
theorem realizes (m : ℕ) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (rs : List (Pair T)) (hk : rs.length = m*m) (count saved src mask width symbols ts tm acc out : Fin T)
    (ht : (count :: saved :: (slots rs ++ [mask])).Nodup)
    (hr : [src,mask,width,symbols,ts,tm,acc,out].Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      let xs := List.range (LabelMask.records v)
      let keep := fun j => branch (LabelStock.residue m w 1 j)
      let W := LabelTransport.payload v
      ∀ (word : ℕ → List (Fin (A+4))) (tail : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A),
      (∀ i ∈ xs, (word i).length = W) → ready (prime^(w-1)) S.R rs → S.R saved = [] →
      (S.R count).length = v.beforeRows*v.rows*B → S.R src = xs.flatMap word ++ tail →
      S.R mask = [] → (S.R width).length = W → (∀ k ∈ [symbols,ts,tm,acc], S.R k = []) →
      let R := Function.update S.R mask ((xs.map keep).map bitSymbol)
      ∃ u' n, u'.user = u.user ∧ n ≤ (v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4
        + 2*(xs.length*(16*W+10)+16) ∧ Exec body p (mk u S) n
          (mk u' {S with R := Function.update R out ((xs.filter keep).flatMap word ++
            (xs.filter (fun i => !(keep i))).flatMap word ++ S.R out)}) := by
  obtain ⟨gen,hgen⟩ := class_writes (body := body) m branch rs hk mask count saved ht
  refine ⟨.seq gen (program src mask width symbols ts tm acc out), ?_⟩
  intro v w B hw hv xs keep W word tail u S hword ready hsaved hcount hsrc hmask hwidth hf R
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := hgen v w B hw hv u S ⟨ready,hsaved,hcount⟩
  simp only [hmask,List.append_nil] at he₁
  let M : Stacks T A := {S with R := R}
  have h := hr
  regs_ne h
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := split_exec (body := body) hr xs keep word W hword v₁ M tail
    (by simpa [M,R,‹src ≠ mask›] using hsrc) (by simp [M,R])
    (by simpa [M,R,‹mask ≠ width›.symm] using hwidth) (by
      intro k hk
      have ne : k ≠ mask := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
      simpa [M,R,ne] using hf k hk)
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,by
    simpa only [M,R,Function.update_of_ne ‹mask ≠ out›.symm] using Exec.seq he₁ he₂⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelSplit
