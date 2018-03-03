import .byte
import .unix
open byte
namespace brainfuck
  namespace ast
    -- AST
    inductive instruction : Type
    | plus : instruction
    | minus : instruction
    | loop : list instruction -> instruction
    | print : instruction
    | ask : instruction
    | right : instruction
    | left : instruction

    def program := list instruction
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

end brainfuck

namespace fuel_limited

  def input : Type := list byte
  def output : Type := list byte × bool

  def time_budget : Type := ℕ

  -- given input so far, returns output so far and [true] if the program terminated
  def process : Type :=
  time_budget -> list byte -> output

  def bool_leq : bool -> bool -> Prop
  | ff := λ _, true
  | tt := λ x, x = tt

  def output_leq (output1 output2 : output) :=
  bool_leq output1.snd output2.snd ∧
  ∃ (suffix : list byte), append (output1.fst : list byte) suffix = output2.fst

  def process_leq (worse : process) (better : process) : Prop :=
  ∀ input time_budget, ∃ time_budget', output_leq (worse time_budget input) (better time_budget' input)

  def process_equivalent (process1 : process) (process2 : process) : Prop :=
  process_leq process1 process2 ∧ process_leq process2 process1
end fuel_limited

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

namespace simple_edsl
  def program := list char
  def char_to_byte : char -> byte
  | '+' := 43
  | '-' := 45
  | '.' := 46
  | '<' := 60
  | '>' := 62
  | ',' := 44
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