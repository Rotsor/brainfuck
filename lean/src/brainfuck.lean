import .byte
import .unix
open byte

universes u v

namespace brainfuck
  namespace ast
    -- AST
    inductive instruction : Type
    | left : instruction
    | right : instruction
    | plus : instruction
    | minus : instruction
    | print : instruction
    | ask : instruction
    | loop : list instruction -> instruction

    def program := list instruction

    instance : has_append(program) := ⟨ list.append ⟩
  end ast

  -- Interperter links Brainfuck programs to unix process semantics
  namespace interpreter

    -- Abstract machine
    def tape := (ℕ -> byte) × ℕ
    def machine_state : Type := 
      tape × ast.program

    -- Interpreter 
    def modify_tape : (ℕ -> byte) -> ℕ -> byte -> (ℕ -> byte) :=
      λ f i v j, if i = j then v else f j

    open unix.with_coinduction
    open brainfuck.ast

    def execution_step : machine_state -> step_result machine_state
    | ((tape, tape_position), []) := step_result.step ((tape, tape_position), [])
    | ((tape, tape_position), (instruction.plus :: k)) :=
      step_result.step ((modify_tape tape tape_position (byte.increment (tape tape_position)), tape_position), k)
    | ((tape, tape_position), (instruction.minus :: k)) :=
      step_result.step ((modify_tape tape tape_position (byte.decrement (tape tape_position)), tape_position), k)
    | ((tape, tape_position), (instruction.print :: k)) :=
      step_result.print (tape tape_position, ((tape, tape_position), k))
    | ((tape, tape_position), (instruction.ask :: k)) :=
      step_result.ask (λ x , ((modify_tape tape tape_position x, tape_position), k))
    | ((tape, tape_position), (instruction.right :: k)) :=
      step_result.step ((tape, tape_position + 1), k)
    | ((tape, tape_position), (instruction.left :: k)) :=
      step_result.step ((tape, tape_position - 1), k)
    | ((tape, tape_position), (instruction.loop body :: k)) :=
      if tape tape_position = byte.zero
      then
      step_result.step ((tape, tape_position), k)
      else
      step_result.step ((tape, tape_position), (list.append body (instruction.loop body :: k)))

    def machine_initial_state (p : program) : machine_state := 
        (((λ (_ : ℕ), byte.zero), 0), p)

    def interpret (p : program) : unix.with_coinduction.process :=
      { 
        state := machine_state,
        initial_state := machine_initial_state p,
        transition := execution_step,
      }

  end interpreter

  namespace concrete_syntax

    def string : Type := list byte
    instance : has_append(string) := ⟨ list.append ⟩
    instance : has_repr(string) :=
      ⟨ λ l, list.as_string (list.map (λ (x : fin _), char.of_nat x.val)  l) ⟩

    def lparen : byte := 91
    def rparen : byte := 93

    -- decidable with witness
    inductive or_error (α : Type u) : Type u
    | error : (α → false) → or_error
    | ok : α → or_error

    def witness_unique {α : Sort u} (p : α → Prop) : Sort (max 1 u) :=
    { x : α // p x ∧ ∀ y, p y → y = x }

    notation `Σ!` binders `, ` r:(scoped P, witness_unique P) := r

    def unambiguous_parse (T : Type) (G : string → T → Prop) (s : string) :=
      or_error (Σ! t, G s t)

    def unambiguous_parser (T : Type) (G : string → T → Prop)
      := ∀ s, unambiguous_parse T G s

    mutual def print_instruction, print_loop
    with print_instruction : ast.instruction → string
    | ast.instruction.plus := [ 43 ]
    | ast.instruction.minus := [ 45 ]
    | ast.instruction.left := [ 60 ]
    | ast.instruction.right := [ 62 ]
    | ast.instruction.print := [ 46 ]
    | ast.instruction.ask := [ 44 ]
    | (ast.instruction.loop xs) := [ lparen ] ++ print_loop xs
    with print_loop : list ast.instruction → string
    | list.nil := [ rparen ]
    | (list.cons x xs) := print_instruction x ++ print_loop xs

    def print_program : ast.program → string :=
      λ xs, [ lparen ] ++ print_loop xs

    def is_special_char (c : byte) :=
      (∃ i, print_instruction i = [ c ])
      ∨ c = lparen
      ∨ c = rparen

    inductive equal_modulo_comments : list byte → list byte → Prop
    | empty : equal_modulo_comments [] []
    | cons : ∀ c {xs1 xs2}, equal_modulo_comments xs1 xs2 → equal_modulo_comments (c :: xs1) (c :: xs2)
    | comment : ∀ c {xs1 xs2}, not (is_special_char c) → equal_modulo_comments xs1 xs2 → equal_modulo_comments (c :: xs1) (c :: xs2)

    def is_valid_parse : list byte → ast.program → Prop :=
      λ string program, equal_modulo_comments string (print_program program)

    /- end of trusted definitions -/

    inductive stack : Type
    | empty : stack
    | cons : ast.program → stack → stack

    def subst {A : Sort u} (P : A → Sort v) : ∀ {x y : A}, x = y → P x → P y
    | _ _ (eq.refl _) := λ x, x

    section stupid_char_parsing

      inductive simple_instruction_parsing_derivation : byte → ast.instruction → Prop
      | plus  : simple_instruction_parsing_derivation 43 ast.instruction.plus
      | minus : simple_instruction_parsing_derivation 45 ast.instruction.minus
      | lt    : simple_instruction_parsing_derivation 60 ast.instruction.left
      | gt    : simple_instruction_parsing_derivation 62 ast.instruction.right
      | dot   : simple_instruction_parsing_derivation 46 ast.instruction.print
      | comma : simple_instruction_parsing_derivation 44 ast.instruction.ask

      def is_special_char2 (c : byte) :=
        (∃ p, simple_instruction_parsing_derivation c p)
        ∨ c = lparen
        ∨ c = rparen

      def singleton_list_inj : ∀ {A : Type} {a b : A}, [ a ] = [ b ] → a = b :=
          λ _ _ _ eq,
          list.no_confusion eq (λ eq1 eq2, eq1)

      def instruction_non_empty :
        ∀ i, print_instruction i = [ ] → false := begin
        intros i eq,
        induction i; try { unfold print_instruction at eq }; try { contradiction },
        end

      def is_special_char_equiv0 :
        ∀ c,
        (∃ p, simple_instruction_parsing_derivation c p)
        ↔ (∃ i, print_instruction i = [ c ]) :=
        λ c,
        iff.intro
        (λ ex,
        begin
          induction ex with i d,
          induction d,
          exact (exists.intro ast.instruction.plus (by refl)),
          exact (exists.intro ast.instruction.minus (by refl)),
          exact (exists.intro ast.instruction.left (by refl)),
          exact (exists.intro ast.instruction.right (by refl)),
          exact (exists.intro ast.instruction.print (by refl)),
          exact (exists.intro ast.instruction.ask (by refl)),
        end)
        begin
          intro ex,
          induction ex with i d,
          induction i; try {rw ←(singleton_list_inj d)},
          exact (exists.intro _ simple_instruction_parsing_derivation.lt),
          exact (exists.intro _ simple_instruction_parsing_derivation.gt),
          exact (exists.intro _ simple_instruction_parsing_derivation.plus),
          exact (exists.intro _ simple_instruction_parsing_derivation.minus),
          exact (exists.intro _ simple_instruction_parsing_derivation.dot),
          exact (exists.intro _ simple_instruction_parsing_derivation.comma),
          begin
            unfold print_instruction at d,
            induction i,
            unfold print_loop at d,
            exact (list.no_confusion d (λ _ eq, list.no_confusion eq)),
            unfold print_loop at d,
            have : false :=
              list.no_confusion d begin
                intros _,
                simp,
                intro eq,
                exact (instruction_non_empty i_hd begin
                  cases (print_instruction i_hd),
                  refl,
                  contradiction
                end)
              end,
            contradiction
          end
        end

      inductive parsed_char : byte → Type
      | simple_instruction : ∀ b i, simple_instruction_parsing_derivation b i → parsed_char b
      | lparen : parsed_char lparen
      | rparen : parsed_char rparen
      | comment : ∀ b, ¬ is_special_char2 b → parsed_char b

      def refute : ∀ (c : byte),
        (¬ 43 = c) → (¬ 45 = c) → (¬ 60 = c) → (¬ 62 = c) → (¬ 46 = c) → (¬ 44 = c)
        → ∀ i, simple_instruction_parsing_derivation c i → false
      | ._ neq _ _ _ _ _ _ simple_instruction_parsing_derivation.plus := neq (eq.refl _)
      | ._ _ neq _ _ _ _ _ simple_instruction_parsing_derivation.minus := neq (eq.refl _)
      | ._ _ _ neq _ _ _ _ simple_instruction_parsing_derivation.lt := neq (eq.refl _)
      | ._ _ _ _ neq _ _ _ simple_instruction_parsing_derivation.gt := neq (eq.refl _)
      | ._ _ _ _ _ neq _ _ simple_instruction_parsing_derivation.dot := neq (eq.refl _)
      | ._ _ _ _ _ _ neq _ simple_instruction_parsing_derivation.comma := neq (eq.refl _)

      def parse_simple_instruction : ∀ c, or_error (subtype (λ i, simple_instruction_parsing_derivation c i)) :=
        λ c,
        match fin.decidable_eq 256 43 c with
        | decidable.is_true eq := or_error.ok {
          val := ast.instruction.plus,
          property := 
            @@eq.subst (λ c : byte, simple_instruction_parsing_derivation c ast.instruction.plus) eq simple_instruction_parsing_derivation.plus
        }
        | decidable.is_false neq_plus :=
        match fin.decidable_eq 256 45 c with
        | decidable.is_true eq := or_error.ok {
          val := ast.instruction.minus,
          property := 
            @@eq.subst (λ c : byte, simple_instruction_parsing_derivation c ast.instruction.minus) eq simple_instruction_parsing_derivation.minus
        }
        | decidable.is_false neq_minus :=
        match fin.decidable_eq 256 60 c with
        | decidable.is_true eq := or_error.ok {
          val := ast.instruction.left,
          property := 
            @@eq.subst (λ c : byte, simple_instruction_parsing_derivation c ast.instruction.left) eq simple_instruction_parsing_derivation.lt
        }
        | decidable.is_false neq_left :=
        match fin.decidable_eq 256 62 c with
        | decidable.is_true eq := or_error.ok {
          val := ast.instruction.right,
          property := 
            @@eq.subst (λ c : byte, simple_instruction_parsing_derivation c ast.instruction.right) eq simple_instruction_parsing_derivation.gt
        }
        | decidable.is_false neq_right :=
        match fin.decidable_eq 256 46 c with
        | decidable.is_true eq := or_error.ok {
          val := ast.instruction.print,
          property := 
            @@eq.subst (λ c : byte, simple_instruction_parsing_derivation c ast.instruction.print) eq simple_instruction_parsing_derivation.dot
        }
        | decidable.is_false neq_print :=
        match fin.decidable_eq 256 44 c with
        | decidable.is_true eq := or_error.ok {
          val := ast.instruction.ask,
          property := 
            @@eq.subst (λ c : byte, simple_instruction_parsing_derivation c ast.instruction.ask) eq simple_instruction_parsing_derivation.comma
        }
        | decidable.is_false neq_ask :=
          or_error.error (λ s, refute _ neq_plus neq_minus neq_left neq_right neq_print neq_ask s.val s.property)
        end
        end
        end
        end
        end
        end

      def refute2 : ∀ c, 
        (¬ c = lparen) → (¬ c = rparen)
        → ((subtype (λ i, simple_instruction_parsing_derivation c i)) → false)
        → is_special_char2 c → false :=
        λ _ eql eqr none is_special,
        or.elim is_special 
          (λ ex, exists.elim ex (λ val prop,
            none { val := val, property := prop }))
          (λ x, or.elim x eql eqr)

      def parse_char : ∀ c, parsed_char c :=
        λ c, 
          match fin.decidable_eq 256 c lparen with
          | decidable.is_true e := subst parsed_char (eq.symm e) parsed_char.lparen
          | decidable.is_false neq1 := 
            match fin.decidable_eq 256 c rparen with
            | decidable.is_true e := subst parsed_char (eq.symm e) parsed_char.rparen
            | decidable.is_false neq2 := 
              match parse_simple_instruction c with
              | or_error.ok simpl := parsed_char.simple_instruction c simpl.val simpl.property
              | or_error.error neqs :=
                parsed_char.comment c (refute2 _ neq1 neq2 neqs)
              end
            end
          end
    end stupid_char_parsing

    def add_char : char → ast.program → stack → ast.program × stack
      := λ c p s,
       match parse_char c with
       end
      
    

    def opt_cons {A : Type} (x : option A) (l : list A) :=
      match x with
      | option.none := l
      | option.some x := x :: l
      end

    inductive nonterminal : Type
    | program : nonterminal
    | instruction_or_comment : nonterminal
    | instruction : nonterminal

    def nt_type : nonterminal → Type
    | nonterminal.program := ast.program
    | nonterminal.instruction_or_comment := option ast.instruction
    | nonterminal.instruction := ast.instruction

    /- unused (yet?) -/
    namespace indexed_derivation
      open nonterminal
      inductive derivation : ∀ (n : nonterminal), string → nt_type n → Type
      | empty : derivation nonterminal.program [] []
      | cons : ∀ s1 p1 s2 p2,
        derivation instruction_or_comment s1 p1
        → derivation program s2 p2
        → derivation program (s1 ++ s2) (opt_cons p1 p2)
      | comment :
        ∀ c, ¬ is_special_char c
        → derivation instruction_or_comment [c] option.none
      | instruction : 
        ∀ s i, derivation nonterminal.instruction s i
        → derivation instruction_or_comment s (option.some i)
      | simple_instruction : 
        ∀ s i, derivation nonterminal.instruction s i
        → derivation instruction_or_comment s (option.some i)
    end indexed_derivation

    mutual inductive
      program_parsing_derivation,
      instruction_or_comment_parsing_derivation,
      instruction_parsing_derivation

    with program_parsing_derivation : string → ast.program → Prop
    | empty : program_parsing_derivation [] []
    | cons : ∀ {s1 p1 s2 p2},
       instruction_or_comment_parsing_derivation s1 p1
       → program_parsing_derivation s2 p2
       → program_parsing_derivation (s1 ++ s2) (opt_cons p1 p2)

    with instruction_or_comment_parsing_derivation : string → option ast.instruction → Prop
    | comment : ∀ c, ¬ is_special_char c → instruction_or_comment_parsing_derivation [c] option.none
    | instruction :
      ∀ {s i}, instruction_parsing_derivation s i
      → instruction_or_comment_parsing_derivation s (option.some i)
    with instruction_parsing_derivation : string → ast.instruction → Prop
    | simple_instruction : ∀ {b i},
       simple_instruction_parsing_derivation b i
       → instruction_parsing_derivation [b] i
    | while_loop : 
      ∀ {s p}, program_parsing_derivation s p →
       instruction_parsing_derivation
         ([ lparen ] ++ s ++ [ rparen ])
         (ast.instruction.loop p)

    def instruction_or_comment_parsing_derivation.simple_instruction
      : ∀ {b i}, simple_instruction_parsing_derivation b i
       → instruction_or_comment_parsing_derivation [b] (option.some i)
      :=
      λ b i x, instruction_or_comment_parsing_derivation.instruction
       (instruction_parsing_derivation.simple_instruction x)

    inductive right_side_context : Type
    | top_level : right_side_context
    | in_loop : ast.program × right_side_context → right_side_context

    def right_side_zipper := ast.program × right_side_context

    mutual inductive right_side_context_parsing_derivation, program_suffix_parsing_derivation
    with right_side_context_parsing_derivation : string → right_side_context → Prop
    | empty : right_side_context_parsing_derivation [] right_side_context.top_level
    | in_loop :
      ∀ {s p},
      program_suffix_parsing_derivation s p
      → right_side_context_parsing_derivation
        ([rparen] ++ s)
        (right_side_context.in_loop p)
    with program_suffix_parsing_derivation : string → right_side_zipper → Prop
    | program : ∀ {s1 p1 s2 p2},
      program_parsing_derivation s1 p1
      → right_side_context_parsing_derivation s2 p2
      → program_suffix_parsing_derivation (s1 ++ s2) (p1, p2)

    namespace program_suffix_parsing_derivation

     def empty : program_suffix_parsing_derivation [] ([], right_side_context.top_level)
       :=
       program_suffix_parsing_derivation.program
         program_parsing_derivation.empty
         right_side_context_parsing_derivation.empty

     def right_paren :
         ∀ s1 p1, program_suffix_parsing_derivation s1 p1
         → program_suffix_parsing_derivation (rparen :: s1) ([], right_side_context.in_loop p1)
         :=
         begin
           intros s1 p1 d1,
           exact (program_suffix_parsing_derivation.program
             (program_parsing_derivation.empty)
             (right_side_context_parsing_derivation.in_loop d1))
         end

     def left_paren : 
       ∀ s loop_body outer_context,
       program_suffix_parsing_derivation s (loop_body, right_side_context.in_loop outer_context)
       → program_suffix_parsing_derivation (lparen :: s) (ast.instruction.loop loop_body :: outer_context.fst, outer_context.snd)
       := begin
         intros s loop_body outer_context derivation,
         cases derivation with s1 p1 s23' p23' d1 d23',
         cases d23' with s23 p23 d23,
         cases d23 with s2 p2 s3 p3 d2 d3,
         have proof := (
           program_suffix_parsing_derivation.program
             (program_parsing_derivation.cons
               (instruction_or_comment_parsing_derivation.instruction
                 (instruction_parsing_derivation.while_loop d1)
               )
               d2
             )
             d3
          ),
          simp at proof,
          exact proof
       end

     def cons :
       ∀ {s1 p1 s2 p2},
       instruction_or_comment_parsing_derivation s1 p1
       → program_suffix_parsing_derivation s2 p2
       → program_suffix_parsing_derivation (s1 ++ s2) (opt_cons p1 p2.fst, p2.snd)
       :=
       λ s1 p1 s2 p2 d1 d2,
       begin
         cases d2 with _ _ _ _ d21 d22,
         have proof := (program_suffix_parsing_derivation.program (
           program_parsing_derivation.cons
             d1
             d21
         ) d22),
         simp at *,
         exact proof
       end

    end program_suffix_parsing_derivation

    def step0 : 
      ∀ (c : byte) (s : string) (p : right_side_zipper), parsed_char c → 
      program_suffix_parsing_derivation s p → option right_side_zipper
    | ._ s p parsed_char.rparen w := 
      option.some ([], right_side_context.in_loop p)
    | ._ s (p0, right_side_context.in_loop (p1, c)) parsed_char.lparen w :=
      option.some (ast.instruction.loop p0 :: p1, c)
    | ._ s p (parsed_char.simple_instruction b i wi) w :=
      option.some (i :: p.fst, p.snd)
    | ._ s p (parsed_char.comment b non_special) w :=
      option.some (p.fst, p.snd)
    | ._ s (p1, right_side_context.top_level) parsed_char.lparen w :=
      option.none

    def unstep0 : 
      ∀ (s : string) p,
      program_suffix_parsing_derivation s p
      → (∃ c parsed_c p' w', step0 c s p' parsed_c w' = option.some p)
       ∨ s = []
      :=
      λ s p w,
      program_suffix_parsing_derivation.rec_on
          w
          begin -- empty
            intros,
            exact (or.intro_right _ (eq.refl _))
          end
          begin  -- cons
            intros s1 p1 s2 p2 instruction_or_comment rest_of_program induction,
            induction instruction_or_comment,
          end
          sorry -- right_paren
          sorry -- left_paren
        
/-    | c parsed_c s p 
      (program_suffix_parsing_derivation.program _ _ _ (p'_fst, p'_snd) (program_parsing_derivation.empty) w) :=
      step0_unavoidable c parsed_c _ p w

    inductive program_parsing_derivation : string → ast.program → Prop
    | append : ∀ s1 p1 s2 p2, program_parsing_derivation s1 p1 → program_parsing_derivation s2 p2 → program_parsing_derivation (s1 ++ s2) (p1 ++ p2)
    | comment : ∀ c, ¬ is_special_char c → program_parsing_derivation [c] []
    | simple_instruction : ∀ b i, simple_instruction_parsing_derivation b i → program_parsing_derivation [b] [i]
    | while_loop : 
      ∀ s p, program_parsing_derivation s p →
       program_parsing_derivation ([ lparen ] ++ s ++ [ rparen ]) [ast.instruction.loop p]

    | program : ∀ s1 p1 s2 p2, 
      program_parsing_derivation s1 p1 →
      program_suffix_parsing_derivation s2 p2 → 
      program_suffix_parsing_derivation (s1 ++ s2) (p1 ++ p2.fst, p2.snd)
    | right_paren : ∀ s1 p1, program_suffix_parsing_derivation s1 p1 → program_suffix_parsing_derivation (rparen :: s1) ([], right_side_context.in_loop p1)
    | left_paren : 
      ∀ s1 loop_body outer_context,
      program_suffix_parsing_derivation s1 (loop_body, right_side_context.in_loop outer_context)
      → program_suffix_parsing_derivation (lparen :: s1) (ast.instruction.loop loop_body :: outer_context.fst, outer_context.snd)
-/

    /- def prefix_ambiguity_step :
      ∀ c (parsed_c : parsed_char c) (s : string),
      (∀ p1 p2, 
      program_suffix_parsing_derivation s p1
      → program_suffix_parsing_derivation s p2
      → p1 = p2)
      → (∀ p1 p2, 
      program_suffix_parsing_derivation (c :: s) p1
      → program_suffix_parsing_derivation (c :: s) p2
      → p1 = p2)
    | ._ parsed_char.rparen := 
      λ f, 
      λ p1 p2  -/

    /- def no_prefix_ambiguity :
      ∀ (s : string) p1 p2
      → program_suffix_parsing_derivation s p1
      → program_suffix_parsing_derivation s p2
      → p1 = p2
    |  :=  -/

    /-def impossible_to_close_paren 
      : ∀ (s : string) p, program_suffix_parsing_derivation s (right_side_context.top_level, p)
      → ∀ {s2} {p2 : right_side_zipper}, s2 = (s ++ [ rparen ]) 
      → program_suffix_parsing_derivation s2 p2
      → false
    | _ _ _ ._ ._ eq (closing_paren s1 c1 p0 p1 w1 := sorry -/
/-
    | empty : program_suffix_parsing_derivation [] (right_side_context.top_level, [])
    | program : ∀ s1 p1 s2 p2, 
      program_suffix_parsing_derivation s1 p1 → program_parsing_derivation s2 p2 → program_suffix_parsing_derivation (s1 ++ s2) (p1.fst, p1.snd ++ p2)
    | closing_paren : 
      ∀ s1 c1 p0 p1, 
      program_suffix_parsing_derivation s1 (right_side_context.in_loop (c1, p0), p1) 
      → program_suffix_parsing_derivation (s1 ++ [rparen]) (c1, p0 ++ [ast.instruction.loop p1])
-/

    def step :
      ∀ (c : byte) (s : string) (p : right_side_zipper), parsed_char c → 
      program_suffix_parsing_derivation s p → 
      or_error (subtype (λ (p2 : right_side_zipper), program_suffix_parsing_derivation (c :: s) p2))
    | ._ s p parsed_char.rparen w := 
      or_error.ok ({ subtype.
          val := ([], right_side_context.in_loop p),
          property := program_suffix_parsing_derivation.right_paren s p w
        })
    | ._ s (p1, right_side_context.top_level) parsed_char.lparen w :=
      or_error.error (sorry)
    | ._ s (p0, right_side_context.in_loop (p1, c)) parsed_char.lparen w :=
      or_error.ok ({ subtype.
          val := (ast.instruction.loop p0 :: p1, c),
          property :=
            program_suffix_parsing_derivation.left_paren
              s p0 (p1, c) w
        })
    | ._ s p (parsed_char.simple_instruction b i wi) w :=
      or_error.ok ({
        val := (i :: p.fst, p.snd),
        property := 
          program_suffix_parsing_derivation.cons
            (instruction_or_comment_parsing_derivation.simple_instruction wi)
            w
      })
    | ._ s p (parsed_char.comment b non_special) w :=
      or_error.ok ({
        val := (p.fst, p.snd),
        property :=
          program_suffix_parsing_derivation.cons
            (instruction_or_comment_parsing_derivation.comment b non_special) w
      })

    def parse_as_suffix (s : string) : 
      or_error (subtype (λ (p : right_side_zipper), program_suffix_parsing_derivation s p))
      := 
      list.rec_on s
        (or_error.ok {
          val := ([], right_side_context.top_level),
          property := 
            program_suffix_parsing_derivation.empty
        })
        (λ c s accum,
          or_error.rec_on
            accum
            sorry
            (λ parsed, 
              step c s parsed.val (parse_char c) parsed.property
            )
        )

    def no_unclosed_parens : 
      ∀ {s},
      (subtype (λ (p : right_side_zipper), program_suffix_parsing_derivation s p))
      → or_error (
        (subtype (λ (p : ast.program), program_parsing_derivation s p))
      ) :=
      λ s z, match z.val.snd with
        | right_side_context.top_level := 
          -- this is actually not trivial with our definition of program_suffix_parsing_derivation
          or_error.ok ⟨ z.val.fst, sorry ⟩
        | right_side_context.in_loop _ :=
          or_error.error sorry
        end
      
    def parse (s : string) :
      or_error (subtype (λ (p : ast.program), program_parsing_derivation s p))
      := 
      or_error.rec_on
        (parse_as_suffix s)
        sorry
        (λ res, no_unclosed_parens res)

  end concrete_syntax

end brainfuck

constant brainfuck_interpreter : brainfuck.ast.program

constant is_correct_parse : brainfuck.ast.program -> list byte -> Prop

constant process_equivalent
  (process1 : unix.with_coinduction.process) 
  (process2 : unix.with_coinduction.process) : Prop

constant correct : 
  ∀
   (p : brainfuck.ast.program) 
   (source : list byte),
   is_correct_parse p source -> 
    process_equivalent
       (unix.with_coinduction.feed_input
         (source ++ [byte.zero])
         (brainfuck.interpreter.interpret brainfuck_interpreter))
       (brainfuck.interpreter.interpret p)




--def print (b : byte) : process -> process :=
--  λ (p : process) budget input, 
   --let res := p budget input in
   --(b :: res.fst, res.snd)

-- mutual def run_interpreter_from_state, run_interpreter_from_step, run_interpreter_from_ask
-- run_interpreter_from_state (state : machine_state) : process
-- | 0 := λ _input, ([], false)
-- | nat.succ x := execution_step machine_state
--   incorporate_result
-- with
-- run_interpreter_from_step : step_result -> process
-- | terminate := λ _budget _input, ([], true)
-- | ask f := λ budget input, run_interpreter_from_ask input f budget
-- | print (b, s) -> λ budget input, add_byte (run_interpreter_from_state budget input)
-- | step : machine_state -> step_result
-- with 
-- run_interpreter_from_ask : byte list -> (byte -> machine_state) -> time_budget -> output
-- | nil -> λ _f _b, ([], false)
-- | b :: input -> λ f budget -> run_interpreter_from_state (f b) budget input


-- def find_matching_paren (program : )

-- tape index
-- double-tape brainfuck
-- left = "<<"
-- right = ">>"


-- brainfuck variant with interleaved named tapes and some extra stuff
namespace spare_tape_lang
  variable tape : Type
  variable tape_item : tape → Type
  


  inductive instruction : Type
  | prim : instruction
  | while : tape → list instruction → instruction
  | ask : tape → instruction
  | print : tape → instruction
  | left : instruction
  | right : instruction
  | case : tape → list (list instruction) → instruction

  def program : Type := list (instruction tape)

  variable accumulator : tape
  def state : Type := 
    (∀ (t : tape), ℕ → tape_item t) × program tape

  constant trace : program tape → state tape tape_item → state tape tape_item → Type

  /- def implements_relation (p : program) : (state → state → Prop) → Prop
    := λ R → ∀ s1 s2, R s1 s2 → ∃ trace p s1 s2 -/
  

end spare_tape_lang

/-def paren_matcher
  (tape : Type)
  (accumulator : tape)
  (looking_at : tape)
  (is_left_paren : spare_tape_lang.program tape) -- program that puts 1
  := -/



namespace simple_edsl
  def program := list char
  def char_to_byte : char -> byte
  | '+' := 43
  | '-' := 45
  | '.' := 46
  | '<' := 60
  | '>' := 62
  | ',' := 44
  | '[' := 91
  | ']' := 93
  | _ := 0

/-
  --
  -- sparse tape layout:
  -- 0. accumulator (we stand here)
  -- 1. helper
  -- 2. data
  -- 3. program (0 at beginning of program and end of program, 1 etc are op. codes); is always to the left of data
  -- 4. instruction pointer (1 everywhere except one position where it's 0)
  -- 5. data pointer (0 everywhere except one position where it's 1)
  -- 6. stack (1 everywhere except:
           - 0 at all the brackets that we want to match; 2 at top-level such bracket
           - 0 temorarily at the closing bracket we're matching)
  --
  -- "<": ez
  -- ">": ez
  -- "+": ez
  -- "-": ez
  -- skip until ']':

  *stack = 2;
  while(todo) {
    if('[') {
      *stack = 0;
    }
    else if(']') {
      *stack = 0;
      stack--;
      while(*stack) {
        stack--;
      }
      if(!*ip) {
        *stack = 1;
        stack++;
        while(*stack) {
          stack++;
        }
        *stack = 1;
        todo = false;
      } else {
        *stack = 1;
        stack++;
        while(*stack) {
          stack++;
        }
        *stack = 1;
      }
    }
  advance();
}

        if(!*stack){
        } else {
          stack--;
          
        }
      }
    }

  }
   if()
   
  -- skip instruction:
  -- if
  -- "[": 
  -- skip to after ']': 
  -- while 
  -- if ... then >[] find the matching 
  --  
-/

  def inner_big_case : Π (n : ℕ), (fin n -> program) → program
  | nat.zero := λ _, []
  | (nat.succ n) := λ f, []
  -- def big_case (f : byte -> program) : program :=

  -- def case (branches : (byte × program)) (default : program): program :=

  def boo : program := [ '+' ]

  def parsed1 := 
    brainfuck.concrete_syntax.parse 
      (list.map char_to_byte [ '[', '[', ']', ']' ])

  def parsed2 := 
    brainfuck.concrete_syntax.parse 
      (list.map char_to_byte [ 'x' ])

  def blah : brainfuck.concrete_syntax.or_error unit := brainfuck.concrete_syntax.or_error.ok ()
  def qqq : option int := some 3
  #eval parsed1
  #eval parsed2
  #eval blah
  
  #print boo
  -- for a given closing paren, find the matching opening paren
  -- requirements: 
  -- - null byte before program
  -- - comments stripped
  --
  -- keep going left
  -- replace
  --[
  --  case of
  --  | ']' ->
  --]
end simple_edsl
