import Pom.Order.FinApprox

namespace Pom

noncomputable def trunc {l : Type} [Preorder l] [OrderBot l] (p : Pom l) (n : ℕ) : Pomfin l :=
  p.lift
    (fun (a : Lpo l) ↦ Quotient.mk (@Lpofin.instSetoid l _) (a.trunc n))
    (fun _ _ h ↦ Quotient.eq_iff_equiv.2 (Lpo.trunc_equiv h))

lemma trunc_mono {l : Type} [PartialOrder l] [OrderBot l] {p q : Pom l} {n m : ℕ}
    (hp : p ≤ q) (hn : n ≤ m) : p.trunc n ≤ q.trunc m := by
  obtain ⟨α, rfl, β, rfl, hle⟩ := hp
  refine ⟨α.trunc n, rfl, β.trunc m, rfl, Lpo.trunc_mono hle hn⟩

lemma trunc_le {l : Type} [PartialOrder l] [OrderBot l] (p : Pom l) (n : ℕ) :
    p.trunc n ≤ p := by
  obtain ⟨α, rfl⟩ := p.exists_rep
  refine ⟨α.trunc n, rfl, α, rfl, Lpo.trunc_le _ _⟩

lemma lpo_trunc_mem {l : Type} [Preorder l] [OrderBot l] {α : Lpo l} {p : Pom l} {n : ℕ}
    (h : α ∈ p) : α.trunc n ∈ p.trunc n := by
  rw [h]; rfl

lemma trunc_0 {l : Type} [Preorder l] [OrderBot l] (p : Pom l) : (p.trunc 0).to_pom = ⊥ := by
  unfold Pomfin.to_pom trunc; obtain ⟨α, rfl⟩ := p.exists_rep
  conv => lhs; arg 3; exact Quotient.lift_mk _ _ _
  conv => lhs; exact Quotient.map_mk _ _ _
  refine Quotient.eq_iff_equiv.mpr ?_
  have ⟨x, hx, hroot⟩ := α.property.rel.single_rooted
  have hlev := lev_root hx hroot
  refine ⟨⟨fun _ ↦ ⟨default, ?_⟩, fun _ ↦ ⟨x, hx, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Set.mem_singleton _
  · exact le_of_eq hlev
  · intro ⟨y, hy, hlev'⟩; ext; simp only; by_contra h
    have := lt_of_lt_of_le (lev_mono <| hroot _ hy h) hlev'
    rw [hlev] at this
    contradiction
  · rintro ⟨_, rfl⟩; rfl
  · ext1
    · rfl
    · ext y z; constructor
      · rintro ⟨rfl, rfl, hrel, _⟩; exfalso
        exact α.property.rel.irrefl _ hrel
      · rintro ⟨⟩
    · ext z; refine dite_congr ?_ ?_ ?_
      · ext; constructor <;> rintro rfl <;> rfl
      · rintro rfl; refine if_neg ?_
        conv => arg 1; lhs; exact hlev
        trivial
      · intro _; rfl
    · ext z v; constructor
      · rintro ⟨rfl, _⟩; simp only [Lpo.form, Lpo.singleton, ite_self, ↓reduceIte]; trivial
      · intro hform; by_cases hz : z = default
        · subst hz; refine ⟨Set.mem_singleton _, ?_⟩
          simp only [Form.permute, Lpo.form, Equiv.symm_mk, Equiv.coe_fn_mk]
          conv => exact congrFun (if_pos (le_of_eq hlev)) _
          have := form_root_true hx hroot; rw [this]; trivial
        · conv at hform => exact congrFun (dif_neg (Ne.symm hz)) _
          contradiction

end Pom
