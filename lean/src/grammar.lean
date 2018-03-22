import .byte

def Grammar (A : Type) : Type := list byte → A → Prop

def Unambiguous {A} (G : Grammar A) : Prop :=
    ∀ s p1 p2, G s p1 → G s p2 → p1 = p2

def Delimited {A} (G : Grammar A) : Prop :=
    ∀ pre s suf p1 p2, G s p1 → G (pre ++ s ++ suf) p2 → pre = [] ∧ suf = [] ∧ p1 = p2

def Nonempty {A} (G : Grammar A) : Prop :=
    ¬ (∃ a, G [] a)

inductive Kleene_star {A} (G : Grammar A) : Grammar (list A)
| Empty : Kleene_star [] []
| Cons : ∀ s a ss as, G s a → Kleene_star ss as → Kleene_star (s ++ ss) (a :: as)

def kleene_star_unambiguous : 
    ∀ {A} {G : Grammar A}, 
    Delimited G →
    Nonempty G →
    Unambiguous (Kleene_star G)
    := 
    λ A G delimited nonempty s p1 p2 p1_good p2_good, _