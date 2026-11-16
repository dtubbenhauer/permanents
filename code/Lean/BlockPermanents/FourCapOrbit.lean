import BlockPermanents.FourCapAction
import Mathlib.Logic.Equiv.Option

/-! # The two orbits of completed marked routes

After projecting the four survivors, a completed routing distinguishes
only whether the two marked colors land in the same ordinary packet.
-/
namespace BlockPermanents.FourCapOrbit
open Bend Closures FourRoutes FourCapAction Equiv
open scoped BigOperators
noncomputable section

abbrev Pos := Fin 3 × Fin 2
abbrev Letter := Option (Option (Fin 4))
abbrev Chart := Pos ≃ Letter

def sameChart : Chart := finProdFinEquiv.trans ((finSuccEquiv 5).trans (finSuccEquiv 4).optionCongr)
def mixedChart : Chart := (swap ((0,1) : Pos) (1,0)).trans sameChart

def twist (p : Perm (Fin 3)) (t : Fin 3 → Perm (Fin 2)) : Perm Pos :=
  (Equiv.prodCongrRight t).trans (p.prodCongr (Equiv.refl _))

@[simp] theorem twist_apply (p : Perm (Fin 3)) (t : Fin 3 → Perm (Fin 2)) (i : Fin 3) (j : Fin 2) :
    twist p t (i,j) = (p i,t i j) := rfl

def feet {d : ℕ} (F : Triple d 2 → ℂ) (w : Pos → Fin d) : ℂ :=
  6⁻¹ * ∑ σ : Perm (Fin 3), F (fun i j => w (σ.symm i,j))

theorem averaged_feet {d n : ℕ} (hn : n ≤ 3) (F : Triple d 2 → ℂ)
    (s : Spectator d 2 n) (w : Word d (n*2)) :
    averaged hn F s w = feet F (Function.uncurry ((split hn 1).symm (s,w))) := rfl

/-- Independent in-packet permutations can be removed before applying the
packet average. The matrix packets satisfy this on every coordinate word. -/
def Inner {d : ℕ} (F : Triple d 2 → ℂ) : Prop :=
  ∀ (t : Fin 3 → Perm (Fin 2)) (w : Triple d 2), F (fun i => w i ∘ t i) = F w

theorem packet_inner {d : ℕ} (x : Fin 3 → Fin 2 → Fin d → ℂ) :
    Inner (pureWord (fun i => packet (x i))) := by
  intro t w
  apply Finset.prod_congr rfl
  intro i _
  have h := Bridges.packet_symmetric d 2 (x i)
  rw [Bend.Symmetric,Bridges.symClasp_action] at h
  simpa only [Equiv.symm_symm, h] using
    clasp_invariant (packet (x i)) (t i).symm (w i)

theorem feet_invariant {d : ℕ} {F : Triple d 2 → ℂ} (hF : Inner F)
    (p : Perm (Fin 3)) (t : Fin 3 → Perm (Fin 2)) (w : Pos → Fin d) :
    feet F (w ∘ twist p t) = feet F w := by
  unfold feet
  congr 1
  have hi (σ : Perm (Fin 3)) :
      F (fun i j => (w ∘ twist p t) (σ.symm i,j)) =
        F (fun i j => w (((σ * p.symm).symm i),j)) :=
    hF (fun i => t (σ.symm i)) (fun i j => w (p (σ.symm i),j))
  simp_rw [hi]
  exact (Group.mulRight_bijective p.symm).sum_comp (fun σ : Perm (Fin 3) => F (fun i j => w (σ.symm i,j)))

def labels {d : ℕ} (a b : Fin d) (w : Fin 4 → Fin d) : Letter → Fin d :=
  Option.elim' a (Option.elim' b w)

def value {d : ℕ} (S : Finset (Fin d)) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (e : Chart) (w : Fin 4 → Fin d) : ℂ :=
  24⁻¹ * ∑ σ : Perm (Fin 4), ∑ b ∈ S, ∑ a,
    feet F (labels a b (w ∘ σ) ∘ e) * star (H ![b,a])

private theorem forget {A : Type*} (q : Perm (Option A)) (h : q none = none) :
    q = q.removeNone.optionCongr := by
  apply Equiv.ext; intro u
  cases u with
  | none => exact h
  | some u =>
    have he : ∃ v, q (some u) = some v := by
      cases e : q (some u) with
      | none => exact (Option.some_ne_none u (q.injective (e.trans h.symm))).elim
      | some v => exact ⟨v,rfl⟩
    exact (Equiv.removeNone_some q he).symm

private theorem fixed_two (q : Perm Letter) (ha : q none = none)
    (hb : q (some none) = some none) :
    ∃ p : Perm (Fin 4), q = p.optionCongr.optionCongr := by
  have e := forget q ha
  refine ⟨q.removeNone.removeNone, e.trans ?_⟩
  apply congrArg Equiv.optionCongr
  apply forget
  rw [e] at hb
  exact Option.some_injective _ hb

private theorem value_trans {d : ℕ} (S : Finset (Fin d)) {F : Triple d 2 → ℂ} (hF : Inner F)
    (H : Word d 2 → ℂ) (e : Chart) (p : Perm (Fin 3)) (t : Fin 3 → Perm (Fin 2))
    (q : Perm (Fin 4)) (w : Fin 4 → Fin d) :
    value S F H (((twist p t).trans e).trans q.optionCongr.optionCongr) w =
      value S F H e w := by
  have hl (a b : Fin d) (v : Word d 4) :
      labels a b v ∘ q.optionCongr.optionCongr = labels a b (v ∘ q) := by
    funext i; rcases i with _ | (_ | i) <;> rfl
  unfold value
  congr 1
  have he (σ : Perm (Fin 4)) (a b : Fin d) :
      feet F (labels a b (w ∘ σ) ∘ (((twist p t).trans e).trans q.optionCongr.optionCongr)) =
        feet F (labels a b (w ∘ (⇑(σ*q : Perm (Fin 4)))) ∘ e) := by
    change feet F (((labels a b (w ∘ σ) ∘ q.optionCongr.optionCongr) ∘ e) ∘ twist p t) = _
    rw [feet_invariant hF,hl]
    rfl
  simp_rw [he]
  exact (Group.mulRight_bijective q).sum_comp (fun σ : Perm (Fin 4) => ∑ b ∈ S, ∑ a, feet F (labels a b (w ∘ σ) ∘ e) * star (H ![b,a]))

private def reorder3 (a b : Fin 3) : Perm (Fin 3) :=
  (swap (swap 0 a 1) b) * swap 0 a

private theorem transitive (a b : Pos) (h : a ≠ b) :
    let e := if a.1 = b.1 then sameChart else mixedChart
    ∃ (p : Perm (Fin 3)) (t : Fin 3 → Perm (Fin 2)),
      twist p t (e.symm none) = a ∧ twist p t (e.symm (some none)) = b := by
  have e₀ : sameChart.symm none = (0,0) := by decide
  have e₁ : sameChart.symm (some none) = (0,1) := by decide
  have f₀ : mixedChart.symm none = (0,0) := by decide
  have f₁ : mixedChart.symm (some none) = (1,0) := by decide
  simp only
  split_ifs with hab
  · refine ⟨swap 0 a.1,fun _ => swap 0 a.2,?_⟩
    rw [e₀,e₁]
    have ht : a.2 ≠ b.2 := fun he => h (Prod.ext hab he)
    have h₂ : ∀ i j : Fin 2, i ≠ j → swap 0 i 1 = j := by decide
    simp only [twist_apply,swap_apply_left,h₂ _ _ ht]; exact ⟨trivial,Prod.ext hab rfl⟩
  · refine ⟨reorder3 a.1 b.1,fun i => if i=0 then swap 0 a.2 else swap 0 b.2,?_⟩
    rw [f₀,f₁]
    have h₂ : ∀ i j : Fin 3, i ≠ j → reorder3 i j 0 = i ∧ reorder3 i j 1 = j := by decide
    obtain ⟨h₀,h₁⟩ := h₂ _ _ hab
    simp only [twist_apply, if_pos rfl, if_neg (show (1:Fin 3) ≠ 0 by decide),swap_apply_left,h₀,h₁]; exact ⟨by simp, trivial⟩

/-- Any placement of the two ordered marked colors has one of two values.
The survivor projection and both foot symmetries are included in the proof. -/
theorem classify {d : ℕ} (S : Finset (Fin d)) {F : Triple d 2 → ℂ} (hF : Inner F)
    (H : Word d 2 → ℂ) (e : Chart) (w : Fin 4 → Fin d) :
    value S F H e w = if (e.symm none).1 = (e.symm (some none)).1
      then value S F H sameChart w else value S F H mixedChart w := by
  let a := e.symm none
  let b := e.symm (some none)
  let f := if a.1 = b.1 then sameChart else mixedChart
  have hab : a ≠ b := fun he => Option.noConfusion (e.symm.injective he)
  obtain ⟨p,t,ha,hb⟩ := transitive a b hab
  change twist p t (f.symm none) = a at ha
  change twist p t (f.symm (some none)) = b at hb
  let q := f.symm.trans ((twist p t).trans e)
  have h₀ : q none = none := by change e (twist p t (f.symm none)) = _; rw [ha];exact e.apply_symm_apply _
  have h₁ : q (some none) = some none := by change e (twist p t (f.symm (some none))) = _;rw [hb];exact e.apply_symm_apply _
  obtain ⟨r,hr⟩ := fixed_two q h₀ h₁
  have he : ((twist p t).trans e) = f.trans r.optionCongr.optionCongr := by
    apply Equiv.ext; intro i
    have h := DFunLike.congr_fun hr (f i)
    change e (twist p t (f.symm (f i))) = _ at h
    simpa using h
  have hi := value_trans S hF H e p t 1 w
  have hj := value_trans S hF H f 1 (fun _ => 1) r w
  have hi' : value S F H ((twist p t).trans e) w = value S F H e w := by
    convert hi using 2
    apply Equiv.ext; intro i
    change _ = (Equiv.optionCongr (Equiv.optionCongr (1 : Perm (Fin 4)))) _
    rcases ((twist p t).trans e) i with _ | (_ | j) <;> rfl
  have hj' : value S F H (f.trans r.optionCongr.optionCongr) w = value S F H f w := hj
  rw [← hi', he, hj']
  dsimp only [f,a,b]
  split_ifs <;> rfl

end
end BlockPermanents.FourCapOrbit
