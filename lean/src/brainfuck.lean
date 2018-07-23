import .byte
import .unix
import .ast
open byte

universes u v

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
 
  -- def program := list char
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
  -- sparse tape layout:
  -- 0. accumulator (we stand here)
  -- 1. helper
  -- 2. data
  -- 3. program (0 everywhere outside of program and after end of program, 1 etc are op. codes); is always to the left of data
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
  -/


open brainfuck.ast

inductive direction : Type
| forward : direction
| backward : direction

def direction.reverse : direction → direction
| direction.forward := direction.backward
| direction.backward := direction.forward

namespace list
  def replicate {A : Type} : nat → A → list A
  | nat.zero x := []
  | (nat.succ n) x := x :: replicate n x
end list

namespace simple_operations
  def reset :=
    [ instruction.loop [ instruction.minus ] ]
end simple_operations

open simple_operations

namespace opcode

  @[reducible]
  def opcode := fin 10
  def undefined : opcode := 0
  def lparen : opcode := 1 
  def rparen : opcode := 2
  def minus : opcode := 3
  def plus : opcode := 4
  def left : opcode := 5
  def right : opcode := 6
  def print : opcode := 7
  def ask : opcode := 8

  def to_byte (x : opcode) : byte :=
    fin.mk x.val (nat.le_trans x.is_lt dec_trivial)

end opcode
open opcode (opcode)

namespace tape_layout
  @[reducible]
  def period := 10
  @[reducible]
  def slot := fin period
  
  def accumulator : slot := 0
  def helper : slot := 9 -- very short-term storage
  def register1 : slot := 1
  def data : slot := 2
  def code : slot := 3
  def ip : slot := 4
  def dp : slot := 5
  def stack : slot := 6

  def move (x : slot) :=
    list.replicate x.val instruction.left

  def unmove (x : slot) :=
    list.replicate x.val instruction.right

  def focus (x : slot) : program → program :=
    λ p, move x ++ p ++ unmove x

  def unfocus (x : slot) : program → program :=
    λ p, unmove x ++ p ++ move x

  def set (x : slot) (b : byte) : program :=
    focus x (reset ++ list.replicate b.val instruction.plus)

  def while (x : slot) (p : program) : program :=
    focus x [ instruction.loop (unfocus x p) ]

  def fin_zero {c : nat} : fin (c + 1) :=
    { val := 0, is_lt := nat.zero_lt_succ c }

  def remove_zero {A : Type} {c : nat} : (fin (c + 1) → A) → (fin c → A) :=
    λ f c, f (fin.succ c)

  -- start out focused on x
  def match_worker
    (todo : slot) (x : slot)
    : ∀ (c : nat) (branch : fin (c + 1) → program), program
    | nat.zero branch :=
      unfocus x (branch fin_zero ++ set todo 0)
    | (nat.succ c) branch :=
      [ instruction.loop
         (
           instruction.minus
           :: match_worker c (remove_zero branch)
           ++ unfocus x (focus todo [
             instruction.loop (
               instruction.minus ::
               unfocus todo (branch fin_zero)
             )
           ])
         )
      ]

  def match_
    (todo : slot) (x : slot)
    (c : nat) (branch : fin (c + 1) → program): program
    :=
    set todo 1
    ++ focus x (match_worker todo x c branch)

  def if_before_last {A : Type} (true : A) (false : A) :
    ∀ (c : nat) (f : fin (c + 2)), A
  | (nat.succ x) ⟨ nat.zero, _ ⟩ := false
  | nat.zero ⟨ nat.zero, _ ⟩ := true
  | nat.zero ⟨ nat.succ nat.zero, lt ⟩ := false
  | (nat.succ x) ⟨ (nat.succ y), lt ⟩ :=
    if_before_last x ⟨ y, nat.le_of_succ_le_succ lt ⟩
  | nat.zero ⟨ nat.succ (nat.succ _), lt ⟩ :=
    begin
     have qq := nat.not_succ_le_zero _ (nat.le_of_succ_le_succ (nat.le_of_succ_le_succ lt)),
     contradiction
    end

  def if_ (x : slot) (v : byte) (true : program) (false : program) :=
    match_ helper x (v.val + 1) (λ f, if_before_last true false _ f)

  def advance_raw : direction → program
  | direction.forward := list.replicate period instruction.right
  | direction.backward := list.replicate period instruction.left

  def advance (slots_to_copy : list slot) (d : direction) :=
    let copy : slot → program :=
      λ s,
        advance_raw d
        ++ focus s reset
        ++ (advance_raw (direction.reverse d))
        ++ while s (
          [ instruction.minus ]
          ++ advance_raw d
          ++ [ instruction.plus ]
          ++ advance_raw (direction.reverse d)
        )
    in
    list.join (list.map copy slots_to_copy)
    ++ advance_raw d

end tape_layout

open tape_layout

namespace blergh

  def find_paren (d : direction) : program :=
     let open_paren : opcode :=
       (match d with | direction.forward := opcode.lparen | direction.backward := opcode.rparen end)
     in
     let close_paren : opcode :=
       (match d with | direction.forward := opcode.rparen | direction.backward := opcode.lparen end)
     in
     let todo : slot := register1 in
     (set stack 2 ++
     set register1 1 ++
     while todo (
       (if_ code (opcode.to_byte open_paren)
         (set stack 0)
         (if_ code (opcode.to_byte close_paren)
          (set stack 0 ++
           advance [] (direction.reverse d)
           ++ while stack (
             advance [] (direction.reverse d)
           )
          )
          []
         ))
         ++
         advance
     ))

end blergh

/-

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
