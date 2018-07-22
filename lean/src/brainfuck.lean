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
