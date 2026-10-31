module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaWeightFactoryBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedHeaderCopies
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime

/-! Ordinary replica-factory headers copied from retained gather metadata.
The origin page is a separate packet tape installed after the unary level. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- The retained level uses 108; local origin packets retain gather tape 109. -/
def replicaFactoryHeaderCopies : List (Fin 126 × Fin 117) :=
  [(114,114),(101,101),(112,112),(108,109),(97,97),(98,98),(99,99),(100,100),
    (102,102),(102,103),(121,113),(116,116),(94,94)]

def replicaFactoryHeaderValue (P stage q l s t u band N B L w : ℕ) (k : Fin 126) :=
  if k.val = 114 then P else if k.val = 101 then stage else if k.val = 112 then q else
  if k.val = 108 then l else if k.val = 97 then s else if k.val = 98 then t else
  if k.val = 99 then u else if k.val = 100 then band else if k.val = 102 then L else
  if k.val = 121 then N else if k.val = 116 then B else if k.val = 94 then w else 0

def replicaFactoryUnaryBank (A P stage q l s t u band N B L w : ℕ)
    (borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := releasedCellBank [] borrowed output inp out
  {S with R := unaryCopiesR (replicaFactoryHeaderValue P stage q l s t u band N B L w) S.R replicaFactoryHeaderCopies}

def replicaFactoryHeaderCost (P stage q l s t u band N B L w : ℕ) :=
  4*(P+stage+q+l+s+t+u+band+2*L+N+B+w)+53

theorem replicaFactoryHeaderCopies_cost (P stage q l s t u band N B L w : ℕ) :
    (replicaFactoryHeaderCopies.map (fun r => 4*replicaFactoryHeaderValue P stage q l s t u band N B L w r.1+4)).sum+1 =
      replicaFactoryHeaderCost P stage q l s t u band N B L w := by
  simp [replicaFactoryHeaderCopies,replicaFactoryHeaderValue,replicaFactoryHeaderCost]
  ring

theorem replicaFactoryUnaryBank_level (A P stage q l s t u band N B L w : ℕ)
    (borrowed output : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    (replicaFactoryUnaryBank A P stage q l s t u band N B L w borrowed output inp out).R 109 = List.replicate l tick := by
  simp [replicaFactoryUnaryBank,replicaFactoryHeaderCopies,replicaFactoryHeaderValue,unaryCopiesR,releasedCellBank]

theorem replicaFactoryUnaryBank_packets (A P stage q l s t u band N B L w : ℕ)
    (hw : w = 2*q+8) (lo : ℕ → ℕ) (borrowed output : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let V := weightWorkspaceWidth P q w t u
    let page := (List.range B).flatMap (fun i => binSyms V (lo i))
    let S := replicaFactoryUnaryBank A P stage q l s t u band N B L w borrowed output inp out
    {S with R := (Function.update S.R 109
      (page++((List.replicate N page).flatten++List.replicate l tick)))} =
      replicaWeightFactoryInputBank A P stage q l s t u band N B L w lo [] borrowed output inp out := by
  dsimp only
  rw [←range_mod_flatMap_eq_replicate N B (fun i => binSyms (weightWorkspaceWidth P q w t u) (lo i))]
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k.val ∈ [94,97,98,99,100,101,102,103,109,112,113,114,115,116]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals simp [replicaFactoryUnaryBank,replicaFactoryHeaderCopies,replicaFactoryHeaderValue,
        unaryCopiesR,replicaWeightFactoryInputBank,batchInputBank,releasedCellBank,
        Function.update_apply,Fin.ext_iff,h,hw]
    · have hn (n : ℕ) (h : n ∈ [94,97,98,99,100,101,102,103,109,112,113,114,115,116]) : k.val ≠ n := by
        intro he
        exact hk (he ▸ h)
      simp [replicaFactoryUnaryBank,replicaFactoryHeaderCopies,replicaFactoryHeaderValue,
        unaryCopiesR,replicaWeightFactoryInputBank,batchInputBank,releasedCellBank,Fin.ext_iff,
        hn 94 (by simp),hn 97 (by simp),hn 98 (by simp),hn 99 (by simp),hn 100 (by simp),hn 101 (by simp),
        hn 102 (by simp),hn 103 (by simp),hn 109 (by simp),hn 112 (by simp),hn 113 (by simp),hn 114 (by simp),
        hn 115 (by simp),hn 116 (by simp)]
      split_ifs <;> first | rfl | omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
