module

public import IntegerMultBounds.MathlibTM2.M6.BitAllocatedStageTargets

/-! Execute the nine PR589 stages with a shared owner bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

private theorem splitStacks {m n A : ℕ} (S : Stacks (m+n) A) :
    adjacentStageStacks (embStk (Fin.castAdd n) S) (embStk (Fin.natAdd m) S) = S := by
  cases S with
  | mk inp out L R =>
    simp only [adjacentStageStacks,embStk]
    congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.comp_def]

/-- A piece carries one unpacked owner array to the next, through a single
physical label row and its privately prepared tapes. -/
abbrev OwnerArray (w B tail : ℕ) := Fin 142081 → Fin ((prime^w)^16*(B*((prime^w)^112*tail))) → ZMod 2

def PieceHandoff {P U : Type} {t q : ℕ} (w B tail : ℕ)
    (effect : OwnerArray w B tail → OwnerArray w B tail → Prop)
    (body : P → Pr P t q prime U) (code : Pr P t q prime U)
    (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime) (price : ℕ) : Prop :=
  let entry := singleLabelBank (B := B) (K := (prime^w)^112*tail) (firstRowLabel w)
  ∀ x u S, HelperFan src (entry x) S →
    (∀ j, (∀ h, src h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F steps y, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ price ∧
      z.user = u.user ∧ HelperFan dst (entry y) F ∧ effect x y

def sweepEffect (i : Fin 9) (w B tail : ℕ) (x y : OwnerArray w B tail) : Prop :=
  ∃ packed out, StageTrace i w B tail
    (singleLabelBank (B := B) (K := (prime^w)^112*tail) (firstRowLabel w) x) packed out ∧
    y = Function.update (collapseLabelBank out) (Fin.last 142080) (fun _ => 0)

theorem StageHandoffExec.toPiece {P U : Type} {t q : ℕ} {i w B tail}
    {body : P → Pr P t q prime U} {code src dst prepared price post}
    (run : StageHandoffExec i w B tail body code src dst prepared price post) :
    PieceHandoff w B tail (sweepEffect i w B tail) body code src dst prepared price := by
  intro x u S live frame
  obtain ⟨z,F,t,p,out,ran,cost,user,rep,trace,_⟩ := run x u S live frame
  exact ⟨z,F,t,_,ran,cost,user,rep,p,out,trace,rfl⟩

private theorem handoffList {U : Type} {q : ℕ} (w B tail : ℕ)
    (effect : Piece → OwnerArray w B tail → OwnerArray w B tail → Prop)
    (price : Piece → ℕ) (stages : List Piece) (last : Piece)
    (available : ∀ i ∈ stages++[last], ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (effect i) body code src dst prepared (price i)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
    let K := (prime^w)^112*tail
    let entry := singleLabelBank (B := B) (K := K) (firstRowLabel w)
    ∀ x u S, HelperFan src (entry x) S →
      (∀ j, (∀ h, src h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F steps y, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ ((stages++[last]).map price).sum ∧
        z.user = u.user ∧ HelperFan dst (entry y) F ∧ (stages++[last]).foldr (fun i cont a => ∃ b, effect i a b ∧ cont b) (fun a => a = y) x := by
  induction stages with
  | nil =>
    obtain ⟨P,t,body,code,src,dst,D,run⟩ := available last (by simp)
    refine ⟨P,t,body,code,src,dst,D,?_⟩
    intro K entry x u S live frame
    obtain ⟨z,F,steps,y,ran,cost,user,rep,trace⟩ := run x u S live frame
    exact ⟨z,F,steps,_,ran,by simpa using cost,user,rep,y,trace,rfl⟩
  | cons i stages ih =>
    obtain ⟨P,m,left,a,src,mid,L,firstRun⟩ := available i (by simp)
    obtain ⟨R,n,right,b,input,dst,D,nextRun⟩ := ih (fun j hj => available j (List.mem_cons_of_mem _ hj))
    obtain ⟨bank,compose⟩ := runAdjacentHelperFans (P := P) (R := R) (U := U) (q := q)
      (V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*tail))) mid input
    let front := Fin.castAddEmb n (n := m)
    refine ⟨P ⊕ R,m+n,Sum.elim (fun g => embProg front Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g)),
      (embProg front Sum.inl a).seq (embProg bank Sum.inr b),src.trans front,dst.trans bank,adjacentStageStacks L D,?_⟩
    intro K entry x u S live frame
    have priv (j : Fin m) (off : ∀ h, src h ≠ j) := frame (front j)
      (fun h eq => off h (front.injective eq))
    obtain ⟨v,C,t,y,ran,paid,same,ready,trace⟩ :=
      firstRun x (embDn front u) (embStk front S) live (fun j off => by
        simpa [front,adjacentStageStacks,embStk] using priv j off)
    let post := fun (user : U) (F : Stacks n prime) => user = u.user ∧
      ∃ z, HelperFan dst (entry z) F ∧ (stages++[last]).foldr (fun i cont a => ∃ b, effect i a b ∧ cont b) (fun a => a = z) y
    obtain ⟨z,F,steps,done,bill,user,r,rep,rest⟩ :=
      compose left right a b u (embStk front S) (embStk (Fin.natAdd m) S) v C t
        ((stages++[last]).map price).sum (entry y) post ran ready (by
          intro v' C' user live frame'
          obtain ⟨z,F,s,r,run,cost,preserved,rep,rest⟩ := nextRun y v' C' live (by
            intro j off
            have outside (h) : (src.trans front) h ≠ j.natAdd m := by
              intro eq
              have hv := congrArg Fin.val eq
              change (src h).val = m+j.val at hv
              omega
            have atJ := frame (j.natAdd m) outside
            simp only [adjacentStageStacks,Fin.addCases_right] at atJ
            exact ⟨(frame' j off).1.trans atJ.1,(frame' j off).2.trans atJ.2⟩)
          exact ⟨z,F,s,run,cost,preserved.trans (user.trans same),r,rep,rest⟩)
    have split : adjacentStageStacks (embStk front S) (embStk (Fin.natAdd m) S) = S := splitStacks S
    rw [split] at done
    exact ⟨z,F,steps,r,done,bill.trans (Nat.add_le_add_right paid _),user,rep,y,trace,rest⟩

/-- Place and execute the 29 pieces in the certified node order. Sweeps,
remainders, bridges, and the final side exchange each contribute their bill once. -/
theorem nodeHandoffs {U : Type} {q : ℕ} (w B tail : ℕ)
    (effect : Piece → OwnerArray w B tail → OwnerArray w B tail → Prop) (price : Piece → ℕ)
    (available : ∀ i ∈ nodeProgram, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U)
      (code : Pr P t q prime U) (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (effect i) body code src dst prepared (price i)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (fun x y => nodeProgram.foldr (fun i cont a => ∃ b, effect i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared (nodeProgram.map price).sum := by
  have schedule : nodeProgram = nodeProgram.dropLast ++ [.exchangeSides] := by decide +kernel
  rw [schedule] at available ⊢
  exact handoffList w B tail effect price _ _ available

end IntegerMultBounds.MathlibTM2.M6.BitNode
