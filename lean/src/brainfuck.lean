import .byte
import .unix
import .ast
import system.io
import .interpreter
import .concrete_syntax
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

/-
  -- sparse tape layout:
  -- - accumulator
  -- - helper
  -- - program: 0 everywhere outside of program and after end of program, 1 etc are op. codes
  -- - instruction pointer: 2 to the left, 1 at the pointer, 0 to the right
  -- - stack: 0 everywhere except:
           - 1 at all the opening brackets that we want to match;
           - 1 temorarily at the closing bracket we're matching)
  -- - toplevel-bracket we're matching
  -/
namespace tape_layout
  @[reducible]
  def period := 10
  @[reducible]
  def slot := fin period

  def helper : slot := 0
  def helper2 : slot := 1
  def helper3 : slot := 2
  def accumulator : slot := 3
  def register1 : slot := 4
  def data : slot := 5
  -- data pointer: 2 to the left, 1 at the pointer, 0 to the right
  def data_pointer : slot := 6
  def code : slot := 7
  def code_pointer : slot := 8
  def stack : slot := 9
  def top_of_stack : slot := 10

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

  def destructive_match_
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

  -- uses [helper]
  def destructive_if_ (x : slot) (v : byte) (true : program) (false : program) :=
    destructive_match_ helper x (v.val + 1) (λ f, if_before_last true false _ f)

  def raw_move
    (focus_from : program → program)
    (unfocus_from : program → program)
    (destinations : list (program → program)) : program
    :=
      list.join (list.map (λ (focus : program → program), focus reset) destinations)
      ++ focus_from [ instruction.loop (
        [ instruction.minus ] ++
        unfocus_from (
          list.join (list.map (λ (focus : program → program), focus [ instruction.plus ]) destinations)
        )) ]

  -- uses [helper]
  def copy (from_ : slot) (to : slot) : program :=
    raw_move (focus from_) (unfocus from_) [focus helper]
    ++
    raw_move (focus helper) (unfocus helper) ((focus from_) :: focus to :: [])

  -- uses [helper] and [helper2]
  -- the body may modify [x]
  def if_ (x : slot) (v : byte) (true : program) (false : program) : program :=
    copy x helper2
    ++ destructive_if_ x v true false

  def whileC (x : slot) (compute_cond : program) (p : program) : program :=
    compute_cond
    ++ focus x [ instruction.loop (unfocus x (p ++ compute_cond)) ]

  -- uses all 3 helpers
  def whileZ (x : slot) (p : program) : program :=
    whileC helper3 (
      if_ x 0
        (focus helper3 (reset ++ [instruction.plus]))
        (focus helper3 reset)) p

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

  def parsed_char_to_opcode : ∀ {x : byte}, brainfuck.concrete_syntax.parsed_char x → opcode
  | _ brainfuck.concrete_syntax.parsed_char.lparen := opcode.lparen
  | _ brainfuck.concrete_syntax.parsed_char.rparen := opcode.rparen
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ brainfuck.ast.instruction.left _) := opcode.left
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ brainfuck.ast.instruction.right _) := opcode.right
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ brainfuck.ast.instruction.plus _) := opcode.plus
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ brainfuck.ast.instruction.minus _) := opcode.minus
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ brainfuck.ast.instruction.print _) := opcode.print
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ brainfuck.ast.instruction.ask _) := opcode.ask
  | _ (brainfuck.concrete_syntax.parsed_char.simple_instruction _ (brainfuck.ast.instruction.loop _) wtf) :=
    begin
    have z : false := begin
     cases wtf,
     end,
     contradiction
    end
  | _ (brainfuck.concrete_syntax.parsed_char.comment _ _) := opcode.undefined

  def decode_instruction (x : fin 100) : opcode :=
    parsed_char_to_opcode 
      (brainfuck.concrete_syntax.parse_char
        { val := x.val, is_lt := (nat.le_trans x.is_lt dec_trivial) })

  -- read the program and initialize the initial state
  def read_program : program :=
    let todo := register1 in
    (advance [] direction.forward) ++
    set todo 1 ++
    while todo (
      set todo 1
      ++ focus accumulator [ instruction.ask ]
      ++ destructive_match_
        helper accumulator 99
         (λ x,
          if x.val = 0
          then
            set todo 0
          else
            set code (opcode.to_byte (decode_instruction x)))
      ++
      if_ todo 0
        []
        (advance [] direction.forward))
    ++ (advance [] direction.backward)
    ++ while todo (advance [] direction.backward)
    ++ set data_pointer 2
    ++ set code_pointer 2
    ++ (advance [] direction.forward)
    ++ set data_pointer 1
    ++ set code_pointer 1

  def find_paren (d : direction) : program :=
     let open_paren : opcode :=
       (match d with | direction.forward := opcode.lparen | direction.backward := opcode.rparen end)
     in
     let close_paren : opcode :=
       (match d with | direction.forward := opcode.rparen | direction.backward := opcode.lparen end)
     in
     let todo : slot := register1 in
     (
     set stack 1 ++
     set top_of_stack 1 ++
     set register1 1 ++
     while todo (
       (if_ code (opcode.to_byte open_paren)
         (set stack 1)
         (if_ code (opcode.to_byte close_paren)
          (set stack 1 ++
           advance [] (direction.reverse d)
           ++ whileZ stack (
             advance [] (direction.reverse d))
           ++
           if_ top_of_stack 0
             (-- erase the two matching parens and continue
               set stack 0
               ++ whileZ stack (advance [] d)
               ++ set stack 0)
             (
              -- erase the two matching parens and finish
               set top_of_stack 0
               ++ set stack 0
               ++ whileZ stack (advance [] d)
               ++ set stack 0
               ++ set todo 0
             )
          )
          []
         ))
         ++
         if_ todo 0 [] (advance [todo] d)
     ))

  def src1 : list byte :=
    10 :: 43 :: 45 :: 60 :: 62 :: 46 :: 44 :: []

  def echo :=
    set register1 1 ++
    while register1 (
      focus accumulator [ instruction.ask ]
      ++ focus accumulator [ instruction.print ])

end blergh

end simple_edsl

meta def char_to_byte (c : char) : byte :=
  if h : c.val < 256 then { val := c.val, is_lt := h }
  else 0

def byte_to_char (b : byte) : char :=
  { val := b.val,
  valid := begin refine (is_valid_char_range_1 b.val _),
  exact ((nat.le_trans b.is_lt dec_trivial))end }

meta def get_byte : io byte :=
  io.stdin >>= λ stdin,
  io.fs.get_char stdin >>= λ c,
  return (char_to_byte c)

meta def run : unix.with_coinduction.process → io unit :=
  λ x,
   let r s :=
     run { state := x.state, initial_state := s, transition := x.transition }
   in
   match x.transition x.initial_state with
   | unix.with_coinduction.step_result.step s :=
     r s
   | unix.with_coinduction.step_result.ask f :=
     get_byte >>=
     λ c, r (f c)
   | unix.with_coinduction.step_result.print (c, s) :=
     io.stdout >>= λ stdout,
     io.fs.put_char stdout (byte_to_char c) >>= (λ _, r s)
   end

meta def main := run (brainfuck.interpreter.interpret [])
