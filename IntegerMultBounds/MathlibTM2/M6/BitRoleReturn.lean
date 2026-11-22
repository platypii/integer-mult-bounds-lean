module

public import IntegerMultBounds.MathlibTM2.M6.BitRoleCutoff

/-! Return either branch's owner words to the same downstream tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)

private theorem counterRead (bits : List Bool) (z : ℤ) :
    CountedLoopReuseAlphabet.binary bits z =
      readAt (blank : Fin (prime+4)) [separator] (bits.map bitSymbol) (z-1) := by
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  change RadixZeroFill.encodedBinary _ z = _
  rw [encodedBinary_eq,readAt_single]

private theorem returnBank (V : ℕ) :
    ∃ D : Stacks ((142081+2)+1) prime,
      (∀ i : Fin 142081, D.L ((i.castAdd 2).castAdd 1) = [] ∧ D.R ((i.castAdd 2).castAdd 1) = []) ∧
      D.L (Fin.last _) = [] ∧ D.R (Fin.last _) = [] ∧ StageControls (Fin.castAddEmb 1) V D := by
  let L : Fin (142081+2) → List (Fin (prime+4)) := Fin.addCases (fun _ => []) (fun _ => [separator])
  let R : Fin (142081+2) → List (Fin (prime+4)) := Fin.addCases (fun _ => []) (fun j : Fin 2 =>
    if j = 0 then [] else (FlatCoordinateSchedule.bits V).map bitSymbol)
  refine ⟨⟨[],[],Fin.lastCases [] L,Fin.lastCases [] R⟩,?_,by change Fin.lastCases [] L (Fin.last _) = []; rw [Fin.lastCases_last],by change Fin.lastCases [] R (Fin.last _) = []; rw [Fin.lastCases_last],?_⟩
  · intro i
    simp [L,R,show (i.castAdd 2).castAdd 1 = (i.castAdd 2).castSucc from rfl]
  · intro j z
    simp only [Fin.castAddEmb_apply,show (j.natAdd 142081).castAdd 1 = (j.natAdd 142081).castSucc from rfl,
      Fin.lastCases_castSucc,L,R,Fin.addCases_right]
    split_ifs
    · exact counterRead [] z
    · exact counterRead _ z

/-- Materialize a branch result on ports determined solely by the host size.
The extra seed is common to all branches at the given volume. -/
theorem commonRoleReturn {T Q V : ℕ} {P U : Type} (body : P → Pr P T Q prime U) :
    let B := (142081+2)+1
    let base := Fin.castAddEmb B (n := T)
    let extra := Fin.natAddEmb T (m := B)
    let output := (Fin.castAddEmb 1).trans extra
    let host := fun f => embProg base id (body f)
    ∃ reserve : Stacks B prime, ∀ dst : Fin (142081+2) ↪ Fin T, ∃ copy,
    ∀ src seed effect price code, PackedPieceHandoff V effect body code src dst seed price →
      PackedPieceHandoff V effect host ((embProg base id code).seq copy)
        (src.trans base) output (adjacentStageStacks seed reserve) (price+(142081*(8*V+10)+1)) := by
  intro B base extra output host
  obtain ⟨reserve,empty,tmpL,tmpR,controls⟩ := returnBank V
  refine ⟨reserve,?_⟩
  intro dst
  let source := (Fin.castAddEmb 2).trans (dst.trans base)
  let dest := (Fin.castAddEmb 2).trans output
  let tmp := extra (Fin.last (142081+2))
  have apart (i : Fin T) (j : Fin B) : base i ≠ extra j := by
    intro e
    have h := congrArg Fin.val e
    change i.val = T+j.val at h
    omega
  obtain ⟨copy,materialize⟩ := materializeOwners_exec host source dest tmp
    (fun i j => apart _ _) (fun i => apart _ _) (fun i => extra.injective.ne (Fin.castSucc_ne_last _))
  refine ⟨copy,?_⟩
  intro src seed effect price code branch x u S words fresh
  obtain ⟨v,D,n,y,ran,cost,user,out,act⟩ := branch x (embDn base u) (embStk base S)
    ⟨words.left,words.right,words.controls⟩ (by
      intro j away
      have keep := fresh (base j) (fun i e => away i (base.injective e))
      simpa [base,embStk,adjacentStageStacks] using keep)
  obtain ⟨v',F,exec,_,same,view,off⟩ := exec_emb (body' := host) (ι := id) base.injective (fun _ => rfl) ran u rfl S rfl
  rw [← view] at out
  have stock j : F.L (extra j) = reserve.L j ∧ F.R (extra j) = reserve.R j := by
    have frame := off (extra j) (fun i => apart i j)
    have initial := fresh (extra j) (fun i => apart (src i) j)
    simpa [extra,adjacentStageStacks] using And.intro (frame.1.trans initial.1) (frame.2.trans initial.2)
  have represented : RepT (phaseOwners y) (embStk source F).L (embStk source F).R := by
    intro i z
    have h := fanPayload out.helperFan i z
    rw [encodedOwnerCell,sub_zero] at h
    simpa only [source,Function.Embedding.trans_apply,Fin.castAddEmb_apply,phaseOwners,embStk,
      Function.comp_apply,sub_zero] using h.symm
  obtain ⟨z,R,k,copied,paid,hz,written,keep⟩ := materialize y v' F represented
    ((stock _).1.trans tmpL) ((stock _).2.trans tmpR) (fun i => (stock _).2.trans (empty i).2)
  refine ⟨z,_,n+k,y,Exec.seq exec copied,Nat.add_le_add cost paid,hz.trans (same.trans user),
    ⟨fun i => (stock _).1.trans (empty i).1,written,?_⟩,act⟩
  intro j h
  have retained := keep (output (j.natAdd 142081)) (fun i => output.injective.ne (by
    intro e; have eq := congrArg Fin.val e; change i.val = 142081+j.val at eq; omega))
  change _ = readAt blank (F.L _) (R _) _
  rw [retained]
  change _ = readAt blank (F.L (extra ((j.natAdd 142081).castAdd 1))) (F.R (extra ((j.natAdd 142081).castAdd 1))) _
  rw [(stock _).1,(stock _).2]
  exact controls j h

/-- The selected branch returns on a common bank after a single comparison
and a single copy, regardless of the original branch output locations. -/
theorem fixedRoleCutoff {m n Q V : ℕ} {P R U : Type}
    (left : P → Pr P m Q prime U) (right : R → Pr R n Q prime U)
    (large : Pr P m Q prime U) (leaf : Pr R n Q prime U)
    (src dst : Fin (142081+2) ↪ Fin m) (input output : Fin (142081+2) ↪ Fin n) (rank : ℕ) :
    let T := (m+n)+((142081+2)+1)
    ∃ (host : P ⊕ R → Pr (P ⊕ R) (T+10) Q prime U), ∃ program common result,
    ∀ w L cutoff, cutoff < 2^L → ((w+1)*rank).size ≤ L → ∀ effect price A B,
    (cutoff < (w+1)*rank → PackedPieceHandoff V effect left large src dst A price) →
    ((w+1)*rank ≤ cutoff → PackedPieceHandoff V effect right leaf input output B price) →
    ∃ seed, PackedPieceHandoff V effect host program common result seed
      ((4*w+23*((w+1)*rank)+22*L+51)+(price+(142081*(8*V+10)+1))) := by
  intro T
  obtain ⟨bank,shared,privateTape⟩ := adjacentStagePlacement src input
  let front := Fin.castAddEmb n (n := m)
  let joined := Sum.elim (fun f => embProg front Sum.inl (left f)) (fun f => embProg bank Sum.inr (right f))
  obtain ⟨reserve,copy⟩ := commonRoleReturn (V := V) joined
  obtain ⟨copyA,returnA⟩ := copy (dst.trans front)
  obtain ⟨copyB,returnB⟩ := copy (output.trans bank)
  let extra := (142081+2)+1
  let base := Fin.castAddEmb extra (n := m+n)
  let result := (Fin.castAddEmb 1).trans (Fin.natAddEmb (m+n) (m := extra))
  let host := fun f => embProg base id (joined f)
  let a := (embProg base id (embProg front Sum.inl large)).seq copyA
  let b := (embProg base id (embProg bank Sum.inr leaf)).seq copyB
  let common := (src.trans front).trans base
  let prefixBank := Fin.castAddEmb 10 (n := T)
  let cmp := Fin.natAddEmb T (m := 10)
  let program := (ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7)))
    (embProg prefixBank id a) (embProg prefixBank id b))
  refine ⟨fun f => embProg prefixBank id (host f),program,common.trans prefixBank,result.trans prefixBank,?_⟩
  intro w L cutoff cutFits fits effect price A B active stopped
  obtain ⟨seed,run⟩ := packedCutoff_exec host a b common result result rank w L cutoff cutFits fits
    effect (price+(142081*(8*V+10)+1)) (adjacentStageStacks (adjacentStageStacks A B) reserve)
    (fun h => returnA _ _ _ _ _ (placeHandoff front Sum.inl left joined (fun _ => rfl)
      src dst _ (fun _ => rfl) A _ (by intro j _; simp [front,adjacentStageStacks]) (active h)))
    (fun h => returnB _ _ _ _ _ (placeHandoff bank Sum.inr right joined (fun _ => rfl)
      input output _ shared B _ (by intro j away; simp [privateTape j away,adjacentStageStacks]) (stopped h)))
  exact ⟨seed,by simpa only [ite_self] using run⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
