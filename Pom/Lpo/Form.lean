import Init.Prelude
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.SetNotation
import Mathlib.Order.SymmDiff

def Form (α : Type) := Set α → Prop

@[ext]
lemma form_ext {α : Type} {φ ψ : Form α} (h : ∀ x, φ x = ψ x) : φ = ψ := funext h

namespace Form

variable {α : Type}

def true : Form α := fun _ => True
def false : Form α := fun _ => False
def and (p : Form α) (q : Form α) : Form α := fun v => p v ∧ q v
def or (p : Form α) (q : Form α) : Form α := fun v => p v ∨ q v
def not (p : Form α) : Form α := fun v => ¬(p v)
def literal (x : α) : Form α := fun v => x ∈ v

def sOr {ι : Type} (p : ι → Form α) : Form α :=
  fun v ↦ ∃ x, p x v
def sAnd {ι : Type} (p : ι → Form α) : Form α :=
  fun v ↦ ∀ x, p x v

def sat (p : Form α) : Prop := ∃ v, p v

instance : LE (Form α) where
  le φ ψ := ∀ v, φ v → ψ v

instance : Preorder (Form α) where
  le_refl φ v h := h
  le_trans φ ψ ξ h₁ h₂ v hφ := h₂ v (h₁ v hφ)

instance : PartialOrder (Form α) where
  le_antisymm φ ψ h₁ h₂ := by ext v; exact ⟨h₁ v, h₂ v⟩

lemma mt {p q : Form α} (h : p ≤ q) : q.not ≤ p.not := by
  intro v hqn hp; exact hqn (h v hp)

lemma true_and {p : Form α} : Form.true.and p = p := by
  ext v; exact iff_iff_eq.mpr <| _root_.true_and _

lemma and_comm {p q : Form α} : p.and q = q.and p := by
  ext v; exact And.comm

lemma and_assoc {p q r : Form α} : (p.and q).and r = p.and (q.and r) := by
  ext v; exact _root_.and_assoc

lemma and_comm_assoc {p q r : Form α} : (p.and q).and r = (p.and r).and q := by
  rw [and_assoc, and_comm (p := q), ← and_assoc]

def DependsOn (p : Form α) (s : Set α) : Prop :=
  ∀ v v', Disjoint (symmDiff v v') s → p v = p v'

namespace DependsOn

lemma monotone (p : Form α) : Monotone p.DependsOn := by
  intro s t hsub hd v v' h
  refine hd v v' ?_
  exact Set.disjoint_of_subset_right hsub h

lemma true : (@Form.true α).DependsOn ∅ := by
  intro _ _ _; rfl

lemma false : (@Form.false α).DependsOn ∅ := by
  intro _ _ _; rfl

lemma literal {x : α} : (Form.literal x).DependsOn {x} := by
  intro v v' hd; ext; constructor; all_goals {
    intro h; have := Set.disjoint_right.mp hd (Set.mem_singleton _)
    have := Set.mem_symmDiff.mpr.mt this; simp only [not_or, not_and, not_not] at this
    try (exact this.1 h)
    try (exact this.2 h)
  }

lemma and {φ ψ : Form α} {s t : Set α} (h₁ : φ.DependsOn s) (h₂ : ψ.DependsOn t) :
    (φ.and ψ).DependsOn (s ∪ t) := by
  intro v v' hd; refine congrArg₂ And ?_ ?_
  · refine h₁.monotone _ ?_ v v' hd; exact Set.subset_union_left
  · refine h₂.monotone _ ?_ v v' hd; exact Set.subset_union_right

lemma or {φ ψ : Form α} {s t : Set α} (h₁ : φ.DependsOn s) (h₂ : ψ.DependsOn t) :
    (φ.or ψ).DependsOn (s ∪ t) := by
  intro v v' hd; refine congrArg₂ Or ?_ ?_
  · refine h₁.monotone _ ?_ v v' hd; exact Set.subset_union_left
  · refine h₂.monotone _ ?_ v v' hd; exact Set.subset_union_right

lemma not {φ : Form α} {s : Set α} (h : φ.DependsOn s) :
    φ.not.DependsOn s := by
  intro v v' hd; refine congrArg Not ?_; exact h v v' hd

lemma sOr {ι : Type} {p : ι → Form α} {s : ι → Set α}
    (h : ∀ i : ι, (p i).DependsOn (s i)) :
    (sOr p).DependsOn (Set.iUnion s) := by
  intro v v' hd; ext; refine exists_congr fun i ↦ iff_iff_eq.mpr ?_
  exact DependsOn.monotone _ (Set.subset_iUnion _ _) (h i) v v' hd

lemma sAnd {ι : Type} {p : ι → Form α} {s : ι → Set α}
    (h : ∀ i : ι, (p i).DependsOn (s i)) :
    (sAnd p).DependsOn (Set.iUnion s) := by
  intro v v' hd; refine forall_congr fun i ↦ ?_
  exact DependsOn.monotone _ (Set.subset_iUnion _ _) (h i) v v' hd

lemma empty_vars {p : Form α} (hd : p.DependsOn ∅) (hsat : p.sat) : p = Form.true := by
  ext v; conv => exact iff_true _
  have ⟨v', hform⟩ := hsat
  refine (hd v v' ?_).mpr hform
  exact Set.disjoint_empty _

lemma inter {p : Form α} {s t : Set α} (h₁ : p.DependsOn s) (h₂ : p.DependsOn t) :
    p.DependsOn (s ∩ t) := by
  intro v v' hd
  have hvv' {x} : x ∈ v ∩ s ∩ t ↔ x ∈ v' ∩ s ∩ t := by
    constructor; all_goals
    · intro ⟨⟨hv, hs⟩, ht⟩; refine ⟨⟨?_, hs⟩, ht⟩
      have ⟨hl, hr⟩ := Set.disjoint_right.mp hd ⟨hs, ht⟩
        |> Set.mem_symmDiff.mpr.mt
        |> not_or.mp
      refine not_and.mp ?_ hv |> not_not.mp; assumption
  let u := (v ∩ s ∩ t) ∪ (v' ∩ (t \ s)) ∪ (v ∩ (s \ t))
  refine (h₁ v u ?_).trans ?_ <;> subst u
  · refine Set.disjoint_left.mpr ?_; intro x hsd hx
    rcases Set.mem_symmDiff.mp hsd with ⟨hxv, h'⟩ | ⟨(h | h) | h, h'⟩
    · apply h'; by_cases ht : x ∈ t
      · left; left; exact ⟨⟨hxv, hx⟩, ht⟩
      · right; exact ⟨hxv, hx, ht⟩
    · exact h' h.1.1
    · exact h.2.2 hx
    · exact h' h.1
  · apply h₂ _ _; refine Set.disjoint_left.mpr ?_; intro x hsd hx
    rcases Set.mem_symmDiff.mp hsd with ⟨(h | h) | h, h'⟩ | ⟨hxv, h'⟩
    · apply h'; exact (hvv'.mp h).1.1
    · exact h' h.1
    · exact h.2.2 hx
    · apply h'; by_cases hs : x ∈ s
      · left; left; apply hvv'.mpr; exact ⟨⟨hxv, hs⟩, hx⟩
      · left; right; exact ⟨hxv, hx, hs⟩

lemma restrict {p : Form α} {s v : Set α} (hdep : p.DependsOn s) : p v ↔ p (v ∩ s) := by
  apply iff_iff_eq.mpr
  refine hdep _ _ ?_; refine Set.disjoint_left.mpr ?_; intro x hsd hx
  rcases Set.mem_symmDiff.mp hsd with ⟨hv, hvs⟩ | ⟨⟨hv, _⟩, hv'⟩
  · exact hvs ⟨hv, hx⟩
  · exact hv' hv

end DependsOn

end Form
