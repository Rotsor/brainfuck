-- 4.6

namespace section_4_6_1
    variables (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
    iff.intro
        (assume h : ∀ x, p x ∧ q x,
        have r1 : (∀ x, p x), from (λ x, and.elim_left (h x)),
        have r2 : (∀ x, q x), from (λ x, and.elim_right (h x)),
        show (∀ x, p x) ∧ (∀ x, q x), from ⟨ r1, r2 ⟩
        )
        (assume h : (∀ x, p x) ∧ (∀ x, q x),
        have h1 : (∀ x, p x), from and.elim_left h,
        have h2 : (∀ x, q x), from and.elim_right h,
        λ x, and.intro (h1 x) (h2 x)
        )
    example : 
    (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
    begin
        assume h,
        assume pu,
        assume x,
        from h x (pu x)
    end
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
    begin
        assume h,
        assume x,
        from (or.elim h
        (assume pu, or.intro_left _ (pu x))
        (assume qu, or.intro_right _ (qu x))
        )
    end
end section_4_6_1

namespace section_4_6_2
    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) := 
      assume x,
      iff.intro
        (λ rp, rp x)
        (λ r x, r)
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
      iff.intro
        (λ h, classical.by_contradiction 
          (assume nh2,
          nh2 (or.intro_left _ 
          (assume x,
          or.elim (h x)
            (λ x, x)
            (λ r, false.elim (nh2 (or.intro_right _ r)))
          ))
          ))
        (λ h,
        or.elim h
          (λ pu x, or.intro_left _ (pu x))
          (λ r x, or.intro_right _ r))
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
        iff.intro
            (λ h r x, h x r)
            (λ h r x, h x r)
end section_4_6_2

namespace section_4_6_3
    variables (men : Type) (barber : men)
    variable  (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
    false := (
        let weird := h barber in
        let A := shaves barber barber in
        let o : ¬ A := (λ s, weird.mp s s) in
        o (weird.mpr o)
    )
end section_4_6_3


namespace section_4_6_4
    namespace hide

    def divides (m n : ℕ) : Prop := ∃ k, m * k = n

    instance : has_dvd nat := ⟨divides⟩

    def even (n : ℕ) : Prop := 2 ∣ n

    section
    variables m n : ℕ

    #check m ∣ n
    #check m^n
    #check even (m^n +3)
    end

    end hide

    def prime (n : ℕ) : Prop := 
        (¬ n = 1) ∧ (∀ d, d ∣ n → d = 1 ∨ d = n)

    def infinitely_many_primes : Prop := 
        ∀ t, ∃ n, n > t ∧ prime n

    def Fermat_prime (n : ℕ) : Prop :=
        (∃ k, n = 2 ^ (2 ^ k)) ∧ prime n

    def infinitely_many_Fermat_primes : Prop :=
        ∀ t, ∃ n, n > t ∧ Fermat_prime n

    def goldbach_conjecture : Prop := 
        ∀ x, x > 2 → ∃ a b, prime a ∧ prime b ∧ x = a + b

    def Goldbach's_weak_conjecture : Prop :=
        ∀ x, x > 5 → (¬ hide.even x)
        → ∃ a b c, prime a ∧ prime b ∧ prime c ∧ x = a + b + c

    def Fermat's_last_theorem : Prop := 
        ¬ ∃ a b c n, n > 2 ∧ a ^ n + b ^ n = c ^ n

end section_4_6_4

namespace section_4_6_5
    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    example : (∃ x : α, r) → r :=
        λ ex, exists.elim ex (λ _ r, r)
    example : r → (∃ x : α, r) :=
        λ r, exists.intro a r
    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
        iff.intro
            (λ ex, exists.elim ex (λ x ⟨ px, r ⟩, 
                and.intro 
                    (exists.intro x px)
                    r
            ))
            (λ ⟨ px, r ⟩, 
                exists.elim px (λ x px,
                    exists.intro x ⟨ px, r ⟩
                )
            )
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
        iff.intro
            begin
                intro ex,
                exact (exists.elim ex
                    (λ x pqx, 
                        or.elim pqx 
                            (λ px, 
                                or.intro_left _
                                    (exists.intro _ px))
                            (λ qx, 
                                or.intro_right _
                                    (exists.intro _ qx))
                            )
                )
            end
            (λ x, or.elim x
                (λ ⟨ x , px ⟩, ⟨ x, or.intro_left _ px ⟩)
                (λ ⟨ x , qx ⟩, ⟨ x, or.intro_right _ qx ⟩)
            )

    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := iff.intro 
        (λ pu enp, 
            exists.elim enp
                (λ x npx, npx (pu x)))
        (λ nenp x, 
            classical.by_contradiction
                (λ npx, 
                    nenp ⟨ x, npx ⟩)
        )
        
    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := iff.intro
        (λ ⟨ x , px ⟩ unpx, unpx x px)
        (λ nunp, 
            classical.by_contradiction (λ nep, 
                nunp (λ x px, nep ⟨ x, px ⟩)))
    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := iff.intro
        (λ nep x px, nep ⟨ x, px ⟩)
        (λ unp ⟨ x , px ⟩, unp x px)
    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := iff.intro
        (λ nup, 
            classical.by_contradiction (λ nenp, 
                nup (λ x, 
                    classical.by_contradiction (
                        λ np, 
                            nenp ⟨ x , np ⟩
                    )
                )
            ))
         (λ ⟨ x , npx ⟩ pu, npx (pu x))

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
        iff.intro
            (λ upxr ⟨ x, px ⟩, upxr x px)
            (λ epxr x px, epxr ⟨ x, px ⟩)

    lemma univ_or_counterexample : (∀ x, p x) ∨ (∃ x, ¬ p x) :=
        or.elim (classical.em (∃ x, ¬ p x))
            (λ ex, or.intro_right _ ex)
            (λ nex, or.intro_left _ (λ x, 
                classical.by_contradiction (λ np, nex ⟨ _ , np ⟩)))

    example : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
        iff.intro
            (λ ⟨ x , pxr ⟩ pu, pxr (pu x))
            (λ pur, 
                or.elim
                    (univ_or_counterexample _ p)
                    (λ univ, ⟨ a, λ _, pur univ ⟩)
                    (λ ⟨ x , np ⟩, ⟨ x, λ px, false.elim (np px) ⟩)
                )
    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
        iff.intro
            (λ ⟨ x, rpx ⟩ r, ⟨ x , rpx r ⟩)
            (λ rex, 
                or.elim (classical.em r)
                    (λ r, 
                        let ⟨ x, px ⟩ := rex r in
                        ⟨ x, λ _, px ⟩
                        )
                    (λ nr,
                        ⟨ a, λ r, false.elim (nr r) ⟩
                    )
                )
end section_4_6_5

namespace section_4_6_6
    variables (real : Type) [ordered_ring real]
    variables (log exp : real → real)
    variable  log_exp_eq : ∀ x, log (exp x) = x
    variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
    variable  exp_pos    : ∀ x, exp x > 0
    variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

    -- this ensures the assumptions are available in tactic proofs
    include log_exp_eq exp_log_eq exp_pos exp_add

    example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
    by rw [exp_add, exp_add]

    example (y : real) (h : y > 0)  : exp (log y) = y :=
    exp_log_eq h

    theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
    calc
        log (x * y) = log (x * y) : rfl
        ... = log (exp (log x) * exp (log y)) : by rw [exp_log_eq hx, exp_log_eq hy]
        ... = log (exp (log x + log y)) : by rw exp_add
        ... = log x + log y : log_exp_eq _
    
end section_4_6_6