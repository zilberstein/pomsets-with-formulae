import Pom.Lpo.Basic

namespace Lpo

open Classical in
noncomputable def par_base {l : Type} [Bot l] (x : Node) (ℓ : l) (α β : Lpo l)
    (φ₁ φ₂ : Form Node) : Lpo_base l := {
  nodes := Set.insert x (α.nodes ∪ β.nodes)
  rel y z := (x = y ∧ z ∈ (α.nodes ∪ β.nodes)) ∨ α.rel y z ∨ β.rel y z
  lab y := if x = y then ℓ else if y ∈ α.nodes then α.lab y else β.lab y
  form y v :=
    (x = y) ∨
    (y ∈ α.nodes ∧ (α.form y).and φ₁ v) ∨
    (y ∈ β.nodes ∧ (β.form y).and φ₂ v)
}

open Classical in
lemma par_lev {l : Type} [Bot l] {x : Node} {b : l} {α β : Lpo l} {φ₁ φ₂ : Form Node}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) :
    (par_base x b α β φ₁ φ₂).rel.lev =
    fun y ↦ if x = y then 0 else if y ∈ α.nodes then α.rel.lev y + 1 else β.rel.lev y + 1 := by
  sorry

lemma par_rel_valid {l : Type} [Bot l] {x : Node} {ℓ : l} {α : Lpo l} {β : Lpo l} {φ₁ φ₂ : Form Node}
    (hx₁ : x ∉ α.nodes) (hx₂ : x ∉ β.nodes) (h : Disjoint α.nodes β.nodes) :
    Rel.IsCausalityRel (par_base x ℓ α β φ₁ φ₂).rel (par_base x ℓ α β φ₁ φ₂).nodes := by
  constructor
  -- Transitivity
  · intro y z w
    rintro (⟨rfl, hx | hx⟩ | hyz | hyz) (⟨rfl, hw | hw⟩ | hzw | hzw) <;>
      (try exfalso; exact hx₁ (α.property.rel_dom hyz).2) <;>
      (try exfalso; exact hx₂ (β.property.rel_dom hyz).2) <;>
      (try exfalso; exact hx₁ hx) <;>
      (try exfalso; exact hx₂ hx)
    · left; exact ⟨rfl, Or.inl (α.property.rel_dom hzw).2⟩
    · left; exact ⟨rfl, Or.inr (β.property.rel_dom hzw).2⟩
    · left; exact ⟨rfl, Or.inl (α.property.rel_dom hzw).2⟩
    · left; exact ⟨rfl, Or.inr (β.property.rel_dom hzw).2⟩
    · right; left; exact α.property.rel.trans hyz hzw
    · exfalso; exact Set.disjoint_left.mp h (α.property.rel_dom hyz).2 (β.property.rel_dom hzw).1
    · exfalso; exact Set.disjoint_left.mp h (α.property.rel_dom hzw).1 (β.property.rel_dom hyz).2
    · right; right; exact β.property.rel.trans hyz hzw
  -- Antisymmetry
  · intro y z
    rintro (⟨rfl, hx⟩ | hyz | hyz) (⟨rfl, hy⟩ | hzy | hzy)
    · rfl
    · exfalso; exact hx₁ (α.property.rel_dom hzy).2
    · exfalso; exact hx₂ (β.property.rel_dom hzy).2
    · exfalso; exact hx₁ (α.property.rel_dom hyz).2
    · exact α.property.rel.antisymm hyz hzy
    · exfalso
      exact Set.disjoint_left.mp h (α.property.rel_dom hyz).1 (β.property.rel_dom hzy).2
    · exfalso; exact hx₂ (β.property.rel_dom hyz).2
    · exfalso
      exact Set.disjoint_left.mp h (α.property.rel_dom hzy).1 (β.property.rel_dom hyz).2
    · exact β.property.rel.antisymm hyz hzy
  -- Irreflexitivity
  · rintro y (⟨rfl, _ | _⟩ | hy | hy) <;> try contradiction
    · exact α.property.rel.irrefl _ hy
    · exact β.property.rel.irrefl _ hy
  -- Finitely Preceded
  · intro y; by_cases hy : y ∈ (par_base x ℓ α β φ₁ φ₂).nodes
    · rcases hy with rfl | hy | hy
      · refine Set.finite_empty.subset ?_
        rintro z (⟨rfl, hx | hx⟩ | hzx | hzx) <;> exfalso
        · exact hx₁ hx
        · exact hx₂ hx
        · exact hx₁ (α.property.rel_dom hzx).2
        · exact hx₂ (β.property.rel_dom hzx).2
      · refine ((α.property.rel.fin_prec y).insert x).subset ?_
        rintro z (⟨rfl, _⟩ | hzy | hzy)
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hzy
        · exfalso; exact Set.disjoint_left.mp h hy (β.property.rel_dom hzy).2
      · refine ((β.property.rel.fin_prec y).insert x).subset ?_
        rintro z (⟨rfl, _⟩ | hzy | hzy)
        · exact Set.mem_insert _ _
        · exfalso; exact Set.disjoint_left.mp h (α.property.rel_dom hzy).2 hy
        · exact (Set.mem_insert_of_mem _) hzy
    · refine Set.finite_empty.subset ?_
      rintro z (⟨rfl, hy'⟩ | hzy | hzy) <;> exfalso <;> apply hy
      · right; exact hy'
      · right; left; exact (α.property.rel_dom hzy).2
      · right; right; exact (β.property.rel_dom hzy).2
  -- Finite Levels
  · intro n; rw [par_lev hx₁ hx₂]; cases n with
    | zero =>
      refine (Set.finite_singleton x).subset ?_
      rintro y ⟨rfl | hy | hy, hlev⟩
      · exact Set.mem_singleton _
      · have hx' : x ≠ y := by rintro rfl; exact hx₁ hy
        simp only [hx', ↓reduceIte, hy, Nat.cast_zero, add_eq_zero, one_ne_zero, and_false] at hlev
      · have hx' : x ≠ y := by rintro rfl; exact hx₂ hy
        have hy' := Set.disjoint_right.mp h hy
        simp only [hx', ↓reduceIte, hy', Nat.cast_zero, add_eq_zero, one_ne_zero, and_false] at hlev
    | succ n =>
      refine
          ((Set.finite_union.mpr
            ⟨α.property.rel.fin_lev n, β.property.rel.fin_lev n⟩).insert x).subset ?_
      rintro y ⟨rfl | hy | hy, hlev⟩
      · exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ (Or.inl ⟨hy, ?_⟩)
        have hx : x ≠ y := by rintro rfl; exact hx₁ hy
        simp only [hx, ↓reduceIte, hy, Nat.cast_add, Nat.cast_one] at hlev
        exact WithTop.add_right_cancel ENat.one_ne_top hlev
      · refine Set.mem_insert_of_mem _ (Or.inr ⟨hy, ?_⟩)
        have hx : x ≠ y := by rintro rfl; exact hx₂ hy
        have hy' := Set.disjoint_right.mp h hy
        simp only [hx, ↓reduceIte, hy', Nat.cast_add, Nat.cast_one] at hlev
        exact WithTop.add_right_cancel ENat.one_ne_top hlev
  -- Single-Rooted
  · refine ⟨x, Or.inl rfl, ?_⟩
    rintro y (rfl | hy | hy) hneq
    · exfalso; exact hneq rfl
    · left; exact ⟨rfl, Or.inl hy⟩
    · left; exact ⟨rfl, Or.inr hy⟩

lemma par_valid {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpo l} {φ₁ φ₂ : Form Node}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥)
    (hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x})
    (hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}) :
    IsValidLpo (par_base x ℓ α β φ₁ φ₂) := by
  unfold par_base; constructor
  · rintro y z (⟨rfl, hz | hz⟩ | hr | hr)
    · exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ (Or.inl hz)⟩
    · exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ (Or.inr hz)⟩
    · rcases α.property.rel_dom hr with ⟨hy, hz⟩
      exact ⟨Set.mem_insert_of_mem _ (Or.inl hy), Set.mem_insert_of_mem _ (Or.inl hz)⟩
    · rcases β.property.rel_dom hr with ⟨hy, hz⟩
      exact ⟨Set.mem_insert_of_mem _ (Or.inr hy), Set.mem_insert_of_mem _ (Or.inr hz)⟩
  · intro y hy
    apply Set.mem_insert_iff.mpr.mt at hy; simp only [Set.mem_union, not_or] at hy
    rcases hy with ⟨hneq, hyα, hyβ⟩
    simp only [Ne.symm hneq, ↓reduceIte, hyα]
    exact β.property.lab_dom _ hyβ
  · exact par_rel_valid hx hx' hd
  · rintro y hlab z (⟨rfl, _⟩ | hyz | hyz)
    · simp only [↓reduceIte] at hlab; exact hroot hlab
    · have hy := (α.property.rel_dom hyz).1
      have hx : x ≠ y := by rintro rfl; exact hx hy
      simp only [hx, ↓reduceIte] at hlab
      conv at hlab => lhs; exact if_pos hy
      exact α.property.bot _ hlab _ hyz
    · have hy := (β.property.rel_dom hyz).1
      have hx : x ≠ y := by rintro rfl; exact hx' hy
      have hy' : y ∉ α.val.nodes := Set.disjoint_right.mp hd hy
      simp only [hx, ↓reduceIte] at hlab
      conv at hlab => lhs; exact if_neg hy'
      exact β.property.bot _ hlab _ hyz
  · intro y; constructor
    · rintro ⟨v, rfl | ⟨hy, _⟩ | ⟨hy, _⟩⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Or.inl hy)
      · exact Set.mem_insert_of_mem _ (Or.inr hy)
    · intro hy; rcases Set.eq_or_mem_of_mem_insert hy with rfl | hmem | hmem
      · exact ⟨∅, Or.inl rfl⟩
      · obtain ⟨v, hform⟩ := (α.property.form_dom y).mpr hmem
        refine ⟨Set.insert x v, Or.inr (Or.inl ⟨hmem, ?_, ?_⟩)⟩
        · refine (((α.property.form y) hmem).1 _ _ ?_).mp hform
          refine Set.disjoint_left.mpr ?_; intro z hz hrel
          obtain rfl : z = x := by
            rcases Set.mem_symmDiff.mp hz with ⟨hz, hins⟩ | ⟨hins, hz⟩
            · exfalso; apply hins; refine Set.mem_insert_iff.mpr (Or.inr hz)
            · rcases Set.mem_insert_iff.mp hins with heq | hc <;> trivial
          exact hx (α.property.rel_dom hrel).1
        · apply hφ₁.1; exact Set.mem_insert _ _
      · obtain ⟨v, hform⟩ := (β.property.form_dom y).mpr hmem
        refine ⟨v \ {x}, Or.inr (Or.inr ⟨hmem, ?_, ?_⟩)⟩
        · refine (((β.property.form y) hmem).1 _ _ ?_).mp hform
          refine Set.disjoint_left.mpr ?_; intro z hz hrel
          obtain rfl : z = x := by
            rcases Set.mem_symmDiff.mp hz with ⟨hz, hdiff⟩ | ⟨hdiff, hz⟩
            · have := not_not.mp <| not_and.mp ((Set.mem_sdiff z).mpr.mt hdiff) hz; exact this
            · exfalso; exact hz ((Set.mem_sdiff _).mp hdiff).1
          exact hx' (β.property.rel_dom hrel).1
        · apply hφ₂.1; intro h; have := ((Set.mem_sdiff _).mp h).2; contradiction
  · intro y hy; rcases Set.eq_or_mem_of_mem_insert hy with rfl | hmem | hmem <;>
      clear hy <;> simp only <;> constructor
    · intro _ _ _; ext; constructor <;> exact fun _ ↦ Or.inl True.intro
    · intro _ _ _ _; left; trivial
    · intro v v' h; ext1; refine or_congr (Iff.refl _) (or_congr ?_ ?_)
      · refine and_congr_right' (and_congr ?_ ?_)
        · refine iff_iff_eq.mpr <| (α.property.form y hmem).1 _ _ ?_
          refine Disjoint.mono (le_refl _) ?_ h
          intro z hrel; right; left; exact hrel
        · refine iff_iff_eq.mpr <| hφ₁.2 _ _ ?_; refine Disjoint.mono (le_refl _) ?_ h
          rintro x rfl; left; exact ⟨rfl, Or.inl hmem⟩
      · refine and_congr_right ?_; intro h; exfalso; exact Set.disjoint_left.mp hd hmem h
    · rintro z (⟨rfl, _⟩ | hrel | hrel) v hsat
      · left; trivial
      · right; left; refine ⟨hmem, ?_⟩; rcases hsat with rfl | ⟨hz, hform, hφ⟩ | ⟨hc, _⟩
        · exfalso; exact hx <| (α.property.rel_dom hrel).2
        · refine ⟨?_, hφ⟩; exact (α.property.form y hmem).2 _ hrel _ hform
        · exfalso; refine Set.disjoint_right.mp hd hc ?_; exact (α.property.rel_dom hrel).2
      · exfalso; refine Set.disjoint_left.mp hd hmem ?_; exact (β.property.rel_dom hrel).1
    · intro v v' h; ext1; refine or_congr (Iff.refl _) (or_congr ?_ ?_)
      · refine and_congr_right ?_; intro h; exfalso; exact Set.disjoint_right.mp hd hmem h
      · refine and_congr_right' (and_congr ?_ ?_)
        · refine iff_iff_eq.mpr <| (β.property.form y hmem).1 _ _ ?_
          refine Disjoint.mono (le_refl _) ?_ h
          intro z hrel; right; right; exact hrel
        · refine iff_iff_eq.mpr <| hφ₂.2 _ _ ?_; refine Disjoint.mono (le_refl _) ?_ h
          rintro x rfl; left; exact ⟨rfl, Or.inr hmem⟩
    · rintro z (⟨rfl, _⟩ | hrel | hrel) v hsat
      · left; trivial
      · exfalso; refine Set.disjoint_right.mp hd hmem ?_; exact (α.property.rel_dom hrel).1
      · right; right; refine ⟨hmem, ?_⟩; rcases hsat with rfl | ⟨hc, _⟩ | ⟨hz, hform, hφ⟩
        · exfalso; exact hx' <| (β.property.rel_dom hrel).2
        · exfalso; refine Set.disjoint_left.mp hd hc ?_; exact (β.property.rel_dom hrel).2
        · refine ⟨?_, hφ⟩; exact (β.property.form y hmem).2 _ hrel _ hform

noncomputable def par_gen {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpo l} {φ₁ φ₂ : Form Node}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥)
    (hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x})
    (hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}) : Lpo l := {
  val := par_base x ℓ α β φ₁ φ₂
  property := par_valid hx hx' hd hroot hφ₁ hφ₂
}

end Lpo
