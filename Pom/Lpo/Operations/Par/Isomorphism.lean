import Pom.Lpo.Isomorphism
import Pom.Lpo.Operations.Par
import Pom.Lpo.Operations.Seq.Equiv

namespace Lpo

noncomputable def Equiv.par {x y : Node} {X X' Y Y' : Set Node} (e₁ : X ≃ Y) (e₂ : X' ≃ Y')
    (hx : x ∉ X) (hx' : x ∉ X') (hd : Disjoint X X')
    (hy : y ∉ Y) (hy' : y ∉ Y') (hd' : Disjoint Y Y') :
    ↑(Set.insert x (X ∪ X')) ≃ ↑(Set.insert y (Y ∪ Y')) :=
  (Equiv.singleton x y).union (e₁.union e₂ hd hd')
    (by refine Set.disjoint_left.mpr ?_; rintro x rfl (h | h) <;> contradiction)
    (by refine Set.disjoint_left.mpr ?_; rintro x rfl (h | h) <;> contradiction)

lemma par_form₁ {φ : Form Node} {x y : Node} (hφ : Form.literal x ≤ φ ∧ φ.DependsOn {x}) :
    Form.literal y ≤ φ.permute (Equiv.singleton x y) ∧
    (φ.permute (Equiv.singleton x y)).DependsOn {y} := sorry

lemma par_form₂ {φ : Form Node} {x y : Node} (hφ : (Form.literal x).not ≤ φ ∧ φ.DependsOn {x}) :
    (Form.literal y).not ≤ φ.permute (Equiv.singleton x y) ∧
    (φ.permute (Equiv.singleton x y)).DependsOn {y} := sorry

lemma par_permute {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpo l}
    {φ₁ φ₂ : Form Node}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hd : Disjoint α.nodes β.nodes}
    {hroot : ℓ ≠ ⊥}
    {hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x}}
    {hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}}
    {X Y : Set Node} {y : Node}
    (hy : y ∉ X) (hy' : y ∉ Y) (hd' : Disjoint X Y)
    (e₁ : α.nodes ≃ X) (e₂ : β.nodes ≃ Y) :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).permute (Equiv.par e₁ e₂ hx hx' hd hy hy' hd') =
    par_gen (α := α.permute e₁) (β := β.permute e₂)
      hy hy' hd' hroot (par_form₁ hφ₁) (par_form₂ hφ₂) := by
  ext1
  · rfl
  · sorry
  · sorry
  · sorry

lemma par_isomorphic {l : Type} [Bot l] {x y : Node} {ℓ : l} {α α' β β' : Lpo l}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hy : y ∉ α'.nodes} {hy' : y ∉ β'.nodes}
    {hd : Disjoint α.nodes β.nodes}
    {hd' : Disjoint α'.nodes β'.nodes}
    {hroot : ℓ ≠ ⊥}
    (hα : α ≈ α') (hβ : β ≈ β') :
    par hx hx' hd hroot ≈ par hy hy' hd' hroot := by
  have ⟨e₁, hα⟩ := hα
  have ⟨e₂, hβ⟩ := hβ
  refine ⟨Equiv.par e₁ e₂ hx hx' hd hy hy' hd', ?_⟩
  conv => lhs; exact par_permute hy hy' hd' e₁ e₂
  congr

end Lpo
