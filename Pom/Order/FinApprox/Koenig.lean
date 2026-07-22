import Pom.Order.FinApprox.Trunc

structure TreeNode {l : Type} [Bot l] [LE l] (a b : Lpo l) : Type where
  n : ℕ
  -- Perm is a permutation
  f : Node → Node
  f_inj : (a.trunc n).nodes.InjOn f
  f_dom : ∀ x ∉ (a.trunc n).nodes, f x = default
  le_b : (a.trunc n).val.permute (Equiv.Set.imageOfInjOn f _ f_inj) ≤ b

attribute [ext] TreeNode

namespace TreeNode

def dom {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  (a.trunc t.n).val.nodes

def range {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  t.f '' t.dom

noncomputable def perm {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) :
    t.dom ≃ t.range :=
  Equiv.Set.imageOfInjOn t.f _ t.f_inj

lemma f_eq_perm {l : Type} [Bot l] [LE l] {a b : Lpo l} {t : TreeNode a b} {x : Node}
    (hx : x ∈ t.dom) : t.f x = t.perm ⟨x, hx⟩ := rfl

namespace Equiv

open Classical in
noncomputable def to_f {l : Type} [Bot l] [LE l] {a : Lpo l} {X : Set Node} {n : ℕ}
    (e : (a.trunc n).nodes ≃ X) : Node → Node :=
  fun x ↦ if hx : x ∈ (a.trunc n).nodes then e ⟨_, hx⟩ else default

noncomputable def to_treeNode {l : Type} [Bot l] [LE l] {a b : Lpo l} {X : Set Node} {n : ℕ}
    (e : (a.trunc n).nodes ≃ X) (hle : (a.trunc n).permute e ≤ b) : TreeNode a b := {
  n := n
  f := to_f e
  f_inj := by
    intro x hx y hy heq
    have := (dif_pos hx).symm.trans (heq.trans (dif_pos hy))
    exact Subtype.ext_iff.mp (e.injective (Subtype.ext this))
  f_dom := fun _ hx ↦ dif_neg hx
  le_b := by
    refine le_of_eq_of_le ?_ hle
    refine Lpo.permute_range_eq ?_ ?_
    · ext x; constructor
      · intro hx; obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
        conv => rhs; exact dif_pos hx'
        exact Subtype.coe_prop _
      · intro hx; refine (Set.mem_image _ _ _).mpr ⟨e.symm ⟨_, hx⟩, ?_, ?_⟩
        · exact Subtype.coe_prop _
        · refine (dif_pos (Subtype.coe_prop _)).trans ?_
          simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · intro x; exact dif_pos x.property
}

end Equiv

lemma trunc_0_permute {l : Type} [Bot l] {a b : Lpo l} {X : Set Node} {e : (a.trunc 0).nodes ≃ X}
    (h : X ⊆ (b.trunc 0).nodes) : (a.trunc 0).val.permute e = b.trunc 0 := by
  have hy {x} : (e.symm x).val ∈ a.nodes := (e.symm x).property.1
  have hroot {x} : ∀ z ∈ a.nodes, (e.symm x).val ≠ z → a.rel (e.symm x).val z := by
    intro z hz hne; refine lev_zero hy ?_ _ hz hne
    exact bot_unique (e.symm x).property.2
  have heq : X = (b.trunc 0).nodes := by
    refine le_antisymm h ?_
    intro x hx
    have ⟨y, hy⟩ : ∃ y, y ∈ X := by
      have ⟨z, hz, hroot⟩ := a.property.rel.single_rooted
      exact ⟨e ⟨z, hz, le_of_eq (lev_root hz hroot)⟩, Subtype.coe_prop _⟩
    have : x = y := by
      by_contra hc; have := lev_zero hx.1 (bot_unique hx.2) _ (h hy).1 hc
      have :=
        lt_of_eq_of_lt
          (bot_unique hx.2).symm
          (lt_of_lt_of_le (lev_mono this) (h hy).2)
      simp only [bot_eq_zero', Nat.cast_zero, lt_self_iff_false] at this
    subst this; exact hy
  subst heq; clear h
  simp only [Lpo.trunc, Lpo.trunc_base, Lpo.permute]; ext1
  · rfl
  · ext x y; simp only [Lpo.rel, Nat.cast_zero, nonpos_iff_eq_zero]
    constructor; all_goals {
      try (intro ⟨_, _, hrel, hlx, hly⟩)
      try (intro ⟨hrel, hlx, hly⟩)
      exfalso
      have := lt_of_eq_of_lt hlx.symm (lt_of_lt_of_eq (lev_mono hrel) hly)
      exact (lt_self_iff_false _).mp this
    }
  · simp only [Lpo.lab, Nat.cast_zero, not_lt_zero, nonpos_iff_eq_zero, ↓reduceIte,
      dite_eq_ite, ite_self]
  · ext x v; simp only [Lpo.form, Lpofin.nodes, Lpo.nodes]; constructor
    · rintro ⟨hx, _⟩
      have hroot := lev_zero hx.1 (bot_unique hx.2)
      conv => exact congrFun ((if_pos hx.2).trans (form_root_true hx.1 hroot)) _
      exact True.intro
    · intro hform; by_cases hx : x ∈ (b.trunc 0).nodes
      · refine ⟨hx, ?_⟩
        conv => exact congrFun ((if_pos (e.symm _).property.2).trans (form_root_true hy hroot)) _
        exact True.intro
      · refine False.elim ((congrFun (if_neg ?_) _).mp hform)
        intro hc; conv at hform => exact congrFun (if_pos hc) _
        have h := (b.property.form_dom _).mp ⟨_, hform⟩
        exact not_and.mp hx h hc

noncomputable def root {l : Type} [Preorder l] [OrderBot l] (a b : Lpo l) : TreeNode a b :=
  let x := a.property.rel.single_rooted.choose
  let y := b.property.rel.single_rooted.choose
  {
    n := 0
    f z := if x = z then y else default
    f_inj := by
      intro u hu v hv _; refine Eq.trans (b := x) ?_ (Eq.symm ?_); all_goals {
        by_contra h; have ⟨hx, hroot⟩ := a.property.rel.single_rooted.choose_spec
        refine not_lt_zero (a := a.rel.lev x) ?_
        try (exact lt_of_lt_of_le (lev_mono (hroot _ hu.1 (Ne.symm h))) hu.2)
        try (exact lt_of_lt_of_le (lev_mono (hroot _ hv.1 (Ne.symm h))) hv.2)
      }
    f_dom := by
      intro z hz; refine if_neg ?_
      rintro rfl; have ⟨hx, hroot⟩ := a.property.rel.single_rooted.choose_spec
      exact hz ⟨hx, le_of_eq (lev_root hx hroot)⟩
    le_b := by
      refine le_of_eq_of_le (trunc_0_permute ?_) (Lpo.trunc_le b 0)
      intro z hz; obtain ⟨z, hz', rfl⟩ := (Set.mem_image _ _ _).mp hz
      have : x = z := by
        by_contra h; have ⟨hx, hroot⟩ := a.property.rel.single_rooted.choose_spec
        refine h (a.property.rel.antisymm ?_ ?_)
        · exact hroot _ hz'.1 h
        · refine lev_zero hz'.1 ?_ _ hx (Ne.symm h)
          exact bot_unique hz'.2
      subst this
      conv => rhs; exact if_pos rfl
      have ⟨hy, hroot⟩ := b.property.rel.single_rooted.choose_spec
      exact ⟨hy, le_of_eq (lev_root hy hroot)⟩
  }

instance {l : Type} [LE l] [Bot l] {a b : Lpo l} : LE (TreeNode a b) where
  le t u :=
    t.n ≤ u.n ∧
    ∀ x ∈ t.dom, t.f x = u.f x

instance {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} : Preorder (TreeNode a b) where
  le_refl t := by
    refine ⟨le_refl _, ?_⟩; intro _ _; rfl
  le_trans t u v := by
    intro ⟨hn₁, hf₁⟩ ⟨hn₂, hf₂⟩
    refine ⟨le_trans hn₁ hn₂, ?_⟩
    intro x hx; refine (hf₁ x hx).trans (hf₂ _ ?_)
    exact (Lpo.trunc_mono (le_refl _) hn₁).nodes hx

instance {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} : PartialOrder (TreeNode a b) where
  le_antisymm t u := by
    intro ⟨hn₁, hex₁⟩ ⟨hn₂, hex₂⟩
    have hn := le_antisymm hn₁ hn₂; ext1
    · exact hn
    · ext x; by_cases hx : x ∈ t.dom
      · exact hex₁ _ hx
      · rw [t.f_dom _ hx]; symm; refine u.f_dom _ ?_
        rw [← hn]; exact hx

lemma le_and_n_eq {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hle : t ≤ u) (hn : t.n = u.n) : t = u := by
  refine le_antisymm hle ⟨le_of_eq hn.symm, ?_⟩
  intro x hx; unfold TreeNode.dom at hx; rw [← hn] at hx
  exact (hle.2 _ hx).symm

lemma le_iff {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b} :
    t ≤ u ↔ t.n ≤ u.n ∧ PermExt t.perm u.perm := by
  constructor
  · intro hle; refine ⟨hle.1, ?_, ?_⟩
    · exact (Lpo.trunc_mono (le_refl _) hle.1).nodes
    · intro x; rw [← f_eq_perm, ← f_eq_perm]
      exact hle.2 _ x.property
  · intro ⟨hn, hex⟩; refine ⟨hn, ?_⟩
    intro x hx; have := hex.extend ⟨_, hx⟩
    rw [← f_eq_perm, ← f_eq_perm] at this; exact this

lemma lt_iff {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b} :
  t < u ↔ t.n < u.n ∧ ∀ x ∈ t.dom, t.f x = u.f x := by
    constructor
    · intro ⟨⟨hn, hex⟩, hc⟩; refine ⟨?_, hex⟩
      · refine Nat.lt_iff_le_and_not_ge.2 ⟨hn, fun h => hc ?_⟩
        cases Nat.lt_or_eq_of_le hn with
        | inl hlt => apply Nat.not_lt_of_le at h; contradiction
        | inr heq => exact le_of_eq (Eq.symm (le_and_n_eq ⟨hn, hex⟩ heq))
    · intro ⟨hn, hex⟩; refine ⟨⟨Nat.le_of_lt hn, hex⟩, fun hc => ?_⟩
      have h := hc.1; linarith

open Classical in
noncomputable def cover_of {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l}
    {t u : TreeNode a b} (hlt : t < u) : TreeNode a b :=
  have hle := Lpo.trunc_mono (le_refl a) (Nat.succ_le_of_lt (lt_iff.mp hlt).1)
  {
    n := t.n + 1
    f x := if x ∈ (a.trunc (t.n + 1)).nodes then u.f x else default
    f_inj := by
      intro x hx y hy heq
      refine u.f_inj ?_ ?_ ?_
      · exact hle.nodes hx
      · exact hle.nodes hy
      · exact ((if_pos hx).symm.trans heq).trans (if_pos hy)
    f_dom := by intro x hx; refine if_neg hx
    le_b := by
      refine le_trans ?_ u.le_b
      refine Lpo.permute_monotone hle ⟨hle.nodes, ?_⟩
      intro ⟨x, hx⟩; simp only [Equiv.Set.imageOfInjOn, Subtype.coe_prop, ↓reduceIte,
        Equiv.coe_fn_mk]
  }

lemma cover_is_cover {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hlt : t < u) : t ⋖ cover_of hlt := by
  refine ⟨lt_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Nat.lt_succ_self _
  · intro x hx; refine ((le_of_lt hlt).2 x hx).trans (if_pos ?_).symm
    exact (Lpo.trunc_mono (le_refl _) (Nat.le_succ _)).nodes hx
  · intro v htv hc
    have h₁ := (lt_iff.mp htv).1
    have h₂ := (lt_iff.mp hc).1; simp only [cover_of] at h₂
    linarith

lemma cover_le {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hlt : t < u) : cover_of hlt ≤ u := by
  unfold cover_of; constructor
  · exact Nat.succ_le_of_lt (lt_iff.mp hlt).1
  · simp only [TreeNode.dom]; intro x hx; exact if_pos hx

instance {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} :
    IsStronglyAtomic (TreeNode a b) where
  exists_covBy_le_of_lt _ _ hlt := ⟨cover_of hlt, cover_is_cover hlt, cover_le hlt⟩

lemma cov_by_iff {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b} :
  t ⋖ u ↔ t.n + 1 = u.n ∧ ∀ x ∈ t.dom, t.f x = u.f x := by
  constructor
  · intro ⟨hlt, hnlt⟩; constructor
    · refine le_antisymm ?_ ?_
      · exact Nat.succ_le_of_lt (lt_iff.mp hlt).1
      · refine not_lt.mp fun hc ↦ ?_
        have := lt_iff.mpr.mt (hnlt (cover_is_cover hlt).1)
        simp only [not_and, cover_of] at this
        refine this hc ?_; intro x hx; exact if_pos hx
    · have ⟨⟨_, hf⟩, _⟩ := hlt; exact hf
  · intro ⟨hn, hp⟩; refine ⟨lt_iff.mpr ⟨by linarith, hp⟩, ?_⟩
    · intro v hv hu
      have hn₁ := (lt_iff.mp hv).1
      have hn₂ := (lt_iff.mp hu).1
      linarith

noncomputable def covBy_injection {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l}
    (t : TreeNode a b)
    (u : {u // t ⋖ u})
    (x : { x // x ∈ a.nodes ∧  a.rel.lev x ≤ t.n + 1 }) :
    { x // x ∈ b.nodes ∧ b.rel.lev x ≤ t.n + 1} :=
  ⟨u.val.f x.val, by {
    have hu : x.val ∈ u.val.dom := by
      refine (Lpo.trunc_mono (le_refl _) ?_).nodes x.property
      exact Nat.succ_le_of_lt (lt_iff.mp u.property.1).1
    constructor
    · refine u.val.le_b.nodes ?_; exact (Set.mem_image _ _ _).mpr ⟨x, hu, rfl⟩
    · refine le_of_eq_of_le ?_ x.property.2
      refine (lev_isotone u.val.le_b ?_).symm.trans ?_
      · exact (Set.mem_image _ _ _).mpr ⟨x, hu, rfl⟩
      · refine (congrArg _ (f_eq_perm hu)).trans ((Lpo.permute_lev _ _).symm.trans ?_)
        refine lev_isotone (Lpo.trunc_le a u.val.n) ?_
        have := (cov_by_iff.mp u.property).1; rw [← this]; exact x.property
  }⟩

lemma covBy_injective {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} (t : TreeNode a b) :
    Function.Injective (covBy_injection t) := by
  intro ⟨u, hu⟩ ⟨v, hv⟩ h
  have ⟨hun, hup⟩ := cov_by_iff.mp hu
  have ⟨hvn, hvp⟩ := cov_by_iff.mp hv
  ext x <;> simp only
  · rw [← hun, ← hvn]
  · by_cases hx : x ∈ a.nodes ∧ a.rel.lev x ≤ ↑(t.n + 1)
    · have := congrFun h ⟨x, hx⟩
      simp only [covBy_injection, Subtype.mk.injEq] at this; exact this
    · refine (u.f_dom _ ?_).trans (v.f_dom _ ?_).symm
      · rw [hun] at hx; exact hx
      · rw [hvn] at hx; exact hx

lemma finite_branching {l : Type} [PartialOrder l] [OrderBot l] (a b : Lpo l)
    (t : TreeNode a b) : { u | t ⋖ u }.Finite := by
  let f (u : { u | t ⋖ u }) : (a.trunc u.val.n).nodes ≃ u.val.range := u.val.perm
  refine @Finite.of_injective _ _ ?_ (covBy_injection t) (covBy_injective t)
  exact @Pi.finite _ _ (a.trunc (t.n + 1)).property (fun _ => (b.trunc (t.n + 1)).property)

lemma has_infinite_nodes {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l}
    (hle : ∀ n, (Pom.mk a).trunc n ≤ Pom.mk b) :
    (Set.Ici (root a b)).Infinite := by
  have h n : ∃ t : TreeNode a b, t.n = n ∧ root a b ≤ t := by
    have ⟨a', ha', hlea⟩ := Pom.ge_lpo (hle n)
    have ⟨e, he⟩ := Quotient.exact ha'
    refine ⟨TreeNode.Equiv.to_treeNode e ?_, rfl, ⟨bot_le, ?_⟩⟩
    · exact le_of_eq_of_le he hlea
    · intro x hx
      conv => rhs; exact dif_pos ((Lpo.trunc_mono (le_refl _) (Nat.zero_le _)).nodes hx)
      refine (if_pos ?_).trans ?_
      · by_contra h
        have ⟨hc, hroot⟩ := a.property.rel.single_rooted.choose_spec
        refine h (a.property.rel.antisymm ?_ ?_)
        · exact hroot _ hx.1 h
        · exact lev_zero hx.1 (bot_unique hx.2) _ hc (Ne.symm h)
      · by_contra h
        have ⟨hc, hroot⟩ := b.property.rel.single_rooted.choose_spec
        have hy {h} : (e ⟨x, h⟩).val ∈ b.nodes := hlea.nodes (Subtype.coe_prop _)
        refine h (b.property.rel.antisymm ?_ ?_)
        · exact hroot _ hy h
        · refine lev_zero hy ?_ _ hc (Ne.symm h)
          rw [← lev_isotone hlea (Subtype.coe_prop _)]; nth_rewrite 1 [← he]
          refine (Lpo.permute_lev _ ?_).symm.trans ?_
          refine (lev_isotone (Lpo.trunc_mono (le_refl _) (Nat.zero_le _)) hx).symm.trans ?_
          refine (lev_isotone (Lpo.trunc_le a 0) hx).trans ?_
          exact bot_unique hx.2
  choose f hf using h
  refine (Set.infinite_univ.image ?_ (f := f)).mono ?_
  · intro i _ j _ heq;
    refine (hf i).1.symm.trans ?_; rw [heq]; exact (hf j).1
  · intro t ht; obtain ⟨n, _, rfl⟩ := (Set.mem_image _ _ _).mp ht
    exact (hf n).2

end TreeNode

open OmegaCompletePartialOrder

theorem pom_ge_iff_ge_fin {l : Type} [DCPO l] [OrderBot l] {p q : Pom l}
    (hle : ∀ n, p.trunc n ≤ q) : p ≤ q := by {
  -- Start with any arbitrary representations of p and q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q
  -- Invoke Konig's lemma to show that there is an infinitely increasing
  -- chain of permutations from a.trunc n to something smaller than b
  obtain ⟨f, h₀, hsucc⟩ :=
    exists_seq_covby_of_forall_covby_finite
      (TreeNode.finite_branching a b)
      (TreeNode.has_infinite_nodes hle)
  have hn (n : ℕ) : (f n).n = n := by
    induction n with
    | zero => rw [h₀]; rfl
    | succ n ih =>
      have ⟨hn, _⟩ := TreeNode.cov_by_iff.mp (hsucc n)
      refine hn.symm.trans ?_; rw [ih]
  have hf {i j} (hle : i ≤ j) : f i ≤ f j :=
    monotone_nat_of_le_succ (fun n ↦ (hsucc n).le) hle
  have hext {i j hi hj} (hle : i ≤ j) :
      PermExt
        (Lpo.cast_perm (f i).perm hi rfl (X' := (a.trunc i).nodes))
        (Lpo.cast_perm (f j).perm hj rfl (X' := (a.trunc j).nodes)) := by
    constructor
    · intro x
      exact (TreeNode.le_iff.mp (hf hle)).2.2
        ⟨x, by unfold TreeNode.dom; rw [hn i]; exact Subtype.coe_prop _⟩
    · refine (congrArg₂ (· ⊆ ·) ?_ ?_).mp (TreeNode.le_iff.mp (hf hle)).2.1
      all_goals { unfold TreeNode.dom; rw [hn]; rfl }
  -- Build a new chain by permuting truncations
  let c : Chain (Lpo l) := {
    toFun n := (a.trunc n).val.permute' (f n).perm (by unfold TreeNode.dom; rw [hn n]) rfl
    monotone' i j hle := by
      refine Lpo.permute_monotone ?_ ?_
      · exact Lpo.trunc_mono (le_refl _) hle
      · exact hext hle
  }
  -- Witness that p ≤ q using the supremum of the new chain c as the
  -- representative lpo of p
  refine ⟨ωSup c, ?_, b, rfl, ?_⟩
  -- a ≈ sup c
  · refine Quotient.eq_iff_equiv.mpr ?_
    refine Lpo.permute_chain ?_ ?_ (en := fun n ↦ Lpo.cast_perm (f n).perm ?_ rfl)
    · unfold TreeNode.dom; rw [hn n]; rfl
    · intro i; rfl
    · intro i j hle; exact hext hle
  -- sup c is smaller than b, since every element of c is smaller than b
  · refine ωSup_le _ _ ?_; intro n; unfold c
    refine le_of_eq_of_le ?_ (f n).le_b
    refine (Lpo.permute'_eq ?_ rfl).symm; rw [hn n]
  }
