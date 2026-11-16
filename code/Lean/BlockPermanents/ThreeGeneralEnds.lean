import BlockPermanents.ThreeGeneralOpen

/-! Literal straight and fully contracted ends of both three-packet Schur openings. -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend ThreeTransfer Equiv
open scoped Matrix BigOperators
noncomputable section
variable {I J S : Type*}

def emptyCut (p k : ℕ) : CutIndex p k := ⟨0,by omega⟩
def lastCut (p k : ℕ) (h : k≤p) : CutIndex p k := ⟨k,by omega⟩
def middle (p k : ℕ) (h : k≤p) := (Finset.univ.erase (emptyCut p k)).erase (lastCut p k h)

theorem ends_sum {V : Type*} [AddCommMonoid V] {p k : ℕ} (hk : 0<k) (hp : k≤p)
    (f : CutIndex p k → V) :
    ∑ r, f r = f (emptyCut p k) + f (lastCut p k hp) + ∑ r ∈ middle p k hp, f r := by
  have hn : lastCut p k hp ≠ emptyCut p k := fun h => hk.ne' (congrArg Fin.val h)
  have hl := Finset.mem_erase.mpr ⟨hn,Finset.mem_univ (lastCut p k hp)⟩
  rw [← Finset.sum_erase_add _ f (Finset.mem_univ (emptyCut p k)),← Finset.sum_erase_add _ f hl]
  unfold middle; abel

def straight {d p k : ℕ} [Fintype S] (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ) :=
  ∑ s, Support.reflected (legs (M s) N)

private theorem bend_gram {A B : Type*} [Fintype A] [Fintype B]
    (M : Matrix A I ℂ) (N : Matrix B J ℂ) :
    partialTranspose (Support.reflected (legs M N)) = Support.reflected (legs M (dual N)) := by
  ext ⟨i,j⟩ ⟨i',j'⟩
  simp only [Support.reflected,partialTranspose,legs,dual,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,star_mul',star_star]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  ring

theorem routed_zero {d p k : ℕ} (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hM : ∀ s i, Symmetric (fun w => M s w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    (s : S) : routed M N (emptyCut p k) s = legs (M s) (dual N) := by
  ext ⟨a,b⟩ ⟨i,j⟩
  rw [routed_entry M N hM hN]
  simp [emptyCut,Fin.append_right_nil _ _ rfl,Function.comp_def,legs,dual]

theorem zero_straight {d p k : ℕ} [Fintype S] (M : S → Matrix (Word d p) I ℂ)
    (N : Matrix (Word d k) J ℂ) (hM : ∀ s i, Symmetric (fun w => M s w i))
    (hN : ∀ j, Symmetric (fun w => N w j)) :
    ∑ s, Support.reflected (routed M N (emptyCut p k) s) = partialTranspose (straight M N) := by
  simp only [routed_zero M N hM hN,← bend_gram]
  ext a b; simp only [partialTranspose,straight,Matrix.sum_apply]

abbrev K (d k : ℕ) := Word d k
def stack {d k : ℕ} (M : K d k → Matrix (K d k) I ℂ) : Matrix (K d k × K d k) I ℂ :=
  fun a i => M a.1 a.2 i
def stackedFine {d k : ℕ} (N : Matrix (K d (k+k)) I ℂ) : Matrix (K d k × K d k) I ℂ :=
  fun a i => N (Fin.append a.1 a.2) i

def terminal {d k : ℕ} (M : Matrix (K d k × K d k) I ℂ) (N : Matrix (K d k) J ℂ) :
    Matrix (K d k) (I×J) ℂ := fun s x => ∑ t, M (s,t) x.1 * star (N t x.2)

def mixed {d k : ℕ} (P Q : Matrix (K d k × K d k) I ℂ) (N : Matrix (K d k) J ℂ) :
    Matrix (I×J) (I×J) ℂ := (legs P N)ᴴ * ThreeTransfer.cross * legs Q N

theorem bend_mixed {d k : ℕ} (P Q : Matrix (K d k × K d k) I ℂ) (N : Matrix (K d k) J ℂ) :
    partialTranspose (mixed P Q N) = (terminal P N)ᴴ * terminal Q N := by
  ext ⟨i,j⟩ ⟨i',j'⟩
  simp only [mixed,partialTranspose,legs,ThreeTransfer.cross,terminal,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,star_mul',star_sum,star_star,Finset.sum_mul,Finset.mul_sum]
  simp [mul_ite,Prod.ext_iff,ite_and]
  apply Finset.sum_congr rfl;intro s _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  ring

theorem small_terminal {d k : ℕ} (M : K d k → Matrix (K d k) I ℂ) (N : Matrix (K d k) J ℂ)
    (hM : ∀ s i, Symmetric (fun w => M s w i)) (hN : ∀ j, Symmetric (fun w => N w j)) :
    ∑ s, Support.reflected (routed M N (lastCut k k le_rfl) s) = Support.reflected (terminal (stack M) N) := by
  have h (s : K d k) (a b : Word d (k-k)) (i : I) (j : J) :
      routed M N (lastCut k k le_rfl) s (a,b) (i,j) = terminal (stack M) N s (i,j) := by
    rw [routed_entry M N hM hN]
    simp [lastCut,Fin.append_left_nil _ _ (Nat.sub_self k),Function.comp_def,terminal,stack]
  ext ⟨i,j⟩ ⟨i',j'⟩
  simp only [Support.reflected,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,h]
  apply Finset.sum_congr rfl;intro s _
  simp [lastCut,Fintype.card_fun]

private def frontWord (d k : ℕ) : Word d (k+k-k) ≃ K d k :=
  (finCongr (Nat.add_sub_cancel k k)).arrowCongr (Equiv.refl _)

private theorem front_join {d k : ℕ} (a : Word d (k+k-k)) (t : K d k) :
    (fun i => Fin.append a t (Fin.cast (show k+k-k+k=k+k by omega).symm i)) =
      Fin.append (frontWord d k a) t := by
  funext i
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).surjective i
  cases i <;> simp [Fin.append,frontWord,finCongr,Fin.addCases,Fin.castLT,Fin.subNat,Fin.natAdd]
  all_goals first | apply congrArg a; apply Fin.ext; rfl | apply congrArg t; apply Fin.ext; omega

theorem big_terminal {d k : ℕ} (P : Matrix (K d (k+k)) I ℂ) (N : Matrix (K d k) J ℂ)
    (hP : ∀ i, Symmetric (fun w => P w i)) (hN : ∀ j, Symmetric (fun w => N w j)) :
    (∑ s : Unit, Support.reflected (routed (fun _ : Unit => P) N (lastCut (k+k) k (by omega)) s)) =
      Support.reflected (terminal (stackedFine P) N) := by
  have h (a : Word d (k+k-k)) (b : Word d (k-k)) (i : I) (j : J) :
      routed (fun _ : Unit => P) N (lastCut (k+k) k (by omega)) () (a,b) (i,j) =
        terminal (stackedFine P) N (frontWord d k a) (i,j) := by
    rw [routed_entry _ N (fun _ => hP) hN]
    simp only [lastCut,front_join,terminal,stackedFine]
    apply Finset.sum_congr rfl;intro t _
    simp [Fin.append_left_nil _ _ (Nat.sub_self k),Function.comp_def]
  ext ⟨i,j⟩ ⟨i',j'⟩
  simp only [Finset.univ_unique,Finset.sum_singleton,Support.reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,h]
  rw [← (frontWord d k).sum_comp]
  apply Finset.sum_congr rfl;intro a _
  simp [lastCut,Fintype.card_fun]

end
end BlockPermanents.ThreeGeneralOpen
