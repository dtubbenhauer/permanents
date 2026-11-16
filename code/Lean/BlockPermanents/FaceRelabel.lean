import BlockPermanents.FaceMeans

/-! Relabel the two open exits of the fixed marked cap before averaging.
Their remainder packets are invariant under permutations of their columns. -/
namespace BlockPermanents.FaceRelabel
open MatchingCoarse Closures FaceMeans FaceSampling
noncomputable section

private def omitted {n : ℕ} (i : Fin (n+1)) : Fin n ↪ Fin (n+1) :=
  (Fin.succEmb n).trans (Equiv.swap 0 i).toEmbedding

private theorem mem_omitted {n : ℕ} (i k : Fin (n+1)) :
    k ∈ Set.range (omitted i) ↔ k ≠ i := by
  let s := Equiv.swap 0 i
  constructor
  · rintro ⟨t,rfl⟩ h
    exact Fin.succ_ne_zero t (s.injective (show s t.succ = s 0 by simpa [s] using h))
  · intro h
    have hn : s k ≠ 0 := by
      intro he
      apply h
      have hj : s k = s i := by simp [s,he]
      exact s.injective hj
    obtain ⟨t,ht⟩ := Fin.exists_succ_eq.mpr hn
    exact ⟨t, by change s t.succ = k; rw [ht]; simp [s]⟩

private theorem perm_omitted {n : ℕ} (p : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    ∃ q : Equiv.Perm (Fin n), ∀ j, p (omitSlot i j) = omitSlot (p i) (q j) := by
  let a := (omitted i).trans p.toEmbedding
  let b := omitted (p i)
  have h : Set.range a = Set.range b := by
    ext k
    rw [show Set.range b = Set.range (omitted (p i)) from rfl, mem_omitted]
    constructor
    · rintro ⟨j,rfl⟩ he
      exact ((mem_omitted i _).1 ⟨j,rfl⟩) (p.injective he)
    · intro hk
      have h' : p.symm k ≠ i := fun he => hk (by rw [← he]; simp)
      obtain ⟨j,hj⟩ := (mem_omitted i _).2 h'
      exact ⟨j, by change p (omitted i j) = k; rw [hj]; simp⟩
  let c := a.toEquivRange.trans (Equiv.setCongr h)
  refine ⟨c.trans b.toEquivRange.symm, fun j => ?_⟩
  exact (congrArg Subtype.val (b.toEquivRange.apply_symm_apply (c j))).symm

private theorem packet_perm {I T : Type*} [Fintype I] [DecidableEq I] (x : I → T → ℂ) (p : Equiv.Perm I) :
    packet (x ∘ p) = packet x := by
  funext w
  unfold packet
  congr 1
  exact (Group.mulLeft_bijective p).sum_comp (fun σ => pureWord (x ∘ σ) w)

/-- Extend a permutation of partners to a permutation fixing the marked label. -/
def fixMark {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  ((finSuccEquiv n).trans p.optionCongr).trans (finSuccEquiv n).symm

@[simp] theorem fixMark_zero {n : ℕ} (p : Equiv.Perm (Fin n)) : fixMark p 0 = 0 := by simp [fixMark]
@[simp] theorem fixMark_succ {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    fixMark p i.succ = (p i).succ := by simp [fixMark]

/-- The relabeling permutes the exits themselves, even before squaring them. -/
theorem exit_perm {n d : ℕ} (p : Equiv.Perm (Fin (n+1))) (x : Input (n+2) d) (i : Fin (n+1)) :
    exit (x ∘ fixMark p) i = exit x (p i) := by
  obtain ⟨q,hq⟩ := perm_omitted p i
  have h : remainder (x ∘ fixMark p) i = remainder x (p i) ∘ q := by
    funext j
    simp only [remainder, Function.comp_apply, fixMark_succ, hq]
  funext w
  simp only [exit,h, Function.comp_apply, fixMark_zero, fixMark_succ, packet_perm]

def pairExit {q d : ℕ} (i j : Fin (q+1)) (x : Input (q+2) d) : ℝ :=
  Bend.energy fun w => exit x i w - exit x j w

private theorem canonical {n d : ℕ} (x : Input (n+3) d) :
    fullExit x = pairExit 0 (0 : Fin (n+1)).succ x := by
  have h : FaceExit.marked (x 0) (x (0 : Fin (n+2)).succ) (x (0 : Fin (n+1)).succ.succ)
    (fun i : Fin n => x i.succ.succ.succ) = x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [FaceExit.marked]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [FaceExit.marked]
    refine Fin.cases ?_ (fun l => ?_) k <;>
      simp only [FaceExit.marked, Fin.cons_succ, Fin.cons_zero]
  simp only [fullExit, FaceExit.exitEnergy, h, pairExit]

private def two {a : Type*} (i j : a) (h : i ≠ j) : Fin 2 ↪ a where
  toFun := ![i,j]
  inj' := by intro k l; fin_cases k <;> fin_cases l <;> simp_all [Ne.symm h]

/-- All ordered distinct exit pairs give the same mean, also in the
presence of an arbitrary matching of spectator labels. -/
theorem mean_exit {m d n r : ℕ} (x : Input m d) (fit : 2*r+(n+3) ≤ m)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    mean x r (n+3) (pairExit i j) = mean x r (n+3) fullExit := by
  let one := (0 : Fin (n+1)).succ
  let a := two (0 : Fin (n+2)) one (Fin.succ_ne_zero _).symm
  obtain ⟨p,hp⟩ := perm_between a (two i j hij)
  have h₀ : p 0 = i := hp 0
  have h₁ : p (0 : Fin (n+1)).succ = j := hp 1
  rw [← mean_restrict x fit (fixMark p).toEmbedding fullExit]
  congr 1
  funext y
  simp only [canonical, pairExit, Equiv.coe_toEmbedding, exit_perm, h₀, h₁]

end
end BlockPermanents.FaceRelabel
