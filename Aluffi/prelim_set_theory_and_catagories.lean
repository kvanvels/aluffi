import Mathlib.Tactic

namespace aluffi

variable {X Y : Type} 


def IsPartition (c : Set (Set X)) : Prop :=
  (∅ ∉ c ∧ ∀ a : X, ∃! b ∈ c, a ∈ b)

def myIsPartition(c : Set (Set X)) : Prop :=
  (∅ ∉ c) ∧ (∀ x : X, ∃ p ∈ c, x ∈ p) ∧ (∀ p0 ∈ c, ∀ p1 ∈ c, p0 ≠ p1 → (p0 ∩ p1) = ∅  )



theorem T0 (c : Set (Set X)) : IsPartition c ↔ myIsPartition c := by
  apply Iff.intro
  intro ⟨h0,h1⟩
  constructor
  exact h0
  constructor
  intro x
  specialize h1 x
  rcases h1 with ⟨θ,⟨hθ0,hθ1⟩,hθ2⟩
  dsimp at hθ2
  apply Exists.intro θ
  apply And.intro hθ0 hθ1
  intro p0 hp0 p1 hp1
  contrapose!
  rintro ⟨Γ,hΓ0,hΓ1⟩
  have h10 := h1 Γ
  rcases h10 with ⟨θ,⟨hθ0,hθ1⟩,hθ2⟩
  dsimp at hθ2
  have hθ20 := hθ2 p0 ⟨hp0,hΓ0⟩
  have hθ21 := hθ2 p1 ⟨hp1,hΓ1⟩
  rw [hθ20]
  exact hθ21.symm

  rintro ⟨h0,h1,h2⟩
  constructor
  exact h0
  intro θ
  rcases h1 θ with ⟨p,hp⟩
  apply Exists.intro p
  apply And.intro hp
  intro Γ h3
  by_contra h4
  specialize h2 Γ h3.left p (hp.left) h4
  have h5 : θ ∈ Γ ∩ p := ⟨h3.right,hp.right⟩
  rw [h2] at h5
  exact h5


-- theorem mem_partition {c : Set (Set X)} {θ : Set X} (hp : IsPartition c) : θ ∉ c ↔ θ = ∅ ∨ True := by
--   apply Iff.intro
--   intro h0
--   unfold IsPartition at hp


-- def partitionMap {c : Set (Set X)} (hp : IsPartition c) (x : X) : ↑c ∧ ():= by
--   have h1 := hp.right
--   choose ff hff using h1
--   rcases hff x with ⟨h2,h3⟩
--   dsimp at h3
--   exact ⟨_,h2.left⟩

-- theorem T0 {c : Set (Set X)} (hp : IsPartition c) (x : X) :
--     x ∈ (partitionMap hp x).val := by


-- def R_from_partition {c : Set (Set X) } {hp : IsPartition c} : X → X → Prop := by
--   intro a b
--   exact (@partitionMap X c hp a) = (@partitionMap X c hp b)

-- theorem R_equiv {c : Set (Set X)} (hp : IsPartition c) : Equivalence (@R_from_partition X c hp):= by
--   constructor

--   --reflexive
--   intro x
--   rfl

--   --symm
--   intro a b h0
--   exact h0.symm

--   --trans
--   intro a b c hab hbc
--   exact hab.trans hbc


-- def sets_from_R (R : X → X → Prop)  : Set (Set X)  :=
--   { G : Set X | G.Nonempty ∧ ∀ a b : X, a ∈ G → (b ∈ G ↔ R a b)}

-- theorem partition_sets_from_R {R : X → X → Prop} (hR : Equivalence R) :
--   IsPartition (@sets_from_R X R) := by
--   constructor
--   rintro ⟨h0,h1⟩
--   rcases h0 with ⟨θ,hθ⟩
--   exact hθ
--   intro x
--   unfold sets_from_R
--   apply Exists.intro ({θ : X | R θ x})
--   constructor
--   dsimp
--   apply And.intro
--   apply And.intro
--   use x
--   apply hR.refl x
--   intro a b Rax
--   apply Iff.intro
--   intro Rbx
--   have h11 := (@hR.symm b x) (Rbx)
--   exact (@hR.trans a x b) Rax h11
--   intro Rab
--   have h11 := (@hR.symm a b) Rab
--   exact (@hR.trans b a x) h11 Rax
--   exact hR.refl x
--   intro G
--   dsimp
--   intro ⟨⟨h0,h1⟩,h2⟩
--   apply subset_antisymm
--   intro χ hχ
--   show R χ x
--   have h33 := @hR.symm x χ
--   exact h33 ((h1 x χ h2).mp hχ)
--   intro χ (hχ : R χ x)
--   specialize h1 x χ h2
--   rw [h1]
--   exact (@hR.symm χ x) hχ


-- theorem round_trip (c : Set (Set X)) (hp : IsPartition c) :
--   c = @sets_from_R X (@R_from_partition X c hp)  := by
--   ext s
--   constructor
--   intro h0
--   unfold IsPartition at hp
--   have ⟨h1,h2⟩ := hp
--   have h3 : s ≠ ∅ := by
--     intro h4
--     rw [h4] at h0
--     exact h1 h0
--   have h4 : s.Nonempty := Set.nonempty_iff_ne_empty.mpr h3
--   constructor
--   exact h4
--   intro a b has
--   apply Iff.intro  
--   intro hbs
--   unfold R_from_partition
  
--   have h2a := h2 a
--   have h2b := h2 b
--   rcases h2a with ⟨A,⟨hA0,hA1⟩,hA2⟩
--   dsimp at hA2
--   rcases h2b with ⟨B,⟨hB0,hB1⟩,hB2⟩
--   dsimp at hB2
--   specialize hA2 s _
--   apply And.intro h0 has
--   specialize hB2 s ⟨h0,hbs⟩


--   have h5 : (partitionMap hp a).val ∈ c := Subtype.coe_prop (partitionMap hp a)
--   have h6 : a ∈ (partitionMap hp a).val := by
--     unfold partitionMap
    


