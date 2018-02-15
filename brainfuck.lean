def byte := fin 256

-- AST
inductive brainfuck : Type
| plus : brainfuck
| minus : brainfuck
| loop : list brainfuck -> brainfuck
| print : brainfuck
| ask : brainfuck
| right : brainfuck
| left : brainfuck

def program := list brainfuck

-- Abstract machine
def tape := (ℕ -> byte) × ℕ
def machine_state : Type := 
  tape × program

inductive step_result (state : Type) : Type
| terminate {} : step_result
| ask : (byte -> state) -> step_result
| print : byte × state -> step_result
| step : state -> step_result

-- Interpreter 
def modify_tape : (ℕ -> byte) -> ℕ -> byte -> (ℕ -> byte) :=
  λ f i v j, if i = j then v else f j

def increment_byte : byte -> byte :=
  fin.add 1

def decrement_byte : byte -> byte :=
  fin.add 255

def zero_byte : byte := (0 : fin 256)

def execution_step : machine_state -> step_result machine_state
| ((tape, tape_position), []) := step_result.terminate
| ((tape, tape_position), (brainfuck.plus :: k)) :=
  step_result.step ((modify_tape tape tape_position (increment_byte (tape tape_position)), tape_position), k)
| ((tape, tape_position), (brainfuck.minus :: k)) :=
  step_result.step ((modify_tape tape tape_position (decrement_byte (tape tape_position)), tape_position), k)
| ((tape, tape_position), (brainfuck.print :: k)) :=
  step_result.print (tape tape_position, ((tape, tape_position), k))
| ((tape, tape_position), (brainfuck.ask :: k)) :=
  step_result.ask (λ x , ((modify_tape tape tape_position x, tape_position), k))
| ((tape, tape_position), (brainfuck.right :: k)) :=
  step_result.step ((tape, tape_position + 1), k)
| ((tape, tape_position), (brainfuck.left :: k)) :=
  step_result.step ((tape, tape_position - 1), k)
| ((tape, tape_position), (brainfuck.loop body :: k)) :=
  if tape tape_position = zero_byte
  then
  step_result.step ((tape, tape_position), k)
  else
  step_result.step ((tape, tape_position), (list.append body (brainfuck.loop body :: k)))

def input : Type := list byte
def output : Type := list byte × bool

def time_budget : Type := ℕ

namespace process0
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
end process0

def process : Type 1 :=
  Σ (state : Type), state × (state -> step_result state)

def machine_initial_state (p : program) : machine_state := 
    (((λ (_ : ℕ), zero_byte), 0), p)

def interpret (p : program) : process :=
  sigma.mk machine_state (machine_initial_state p, execution_step)

constant brainfuck_interpreter : program

def optbyte := list byte

def uncons {A R : Type} : list A -> R -> (A → list A → R) → R
| list.nil := λ nil _, nil
| (x :: xs) := λ _ cons, cons x xs

def feed_input : list byte -> process -> process :=
  λ input proces,
  let state := proces.fst in
  let state0 := proces.snd.fst in
  let step := proces.snd.snd in
  (@sigma.mk Type (λ (s : Type), s × (s -> step_result s)) (optbyte × state) ((input, state0), (λ s, 
    let extra_input := s.fst in
    @step_result.rec_on
      state 
      (λ _, step_result (optbyte × state)) (step s.snd)
      -- terminate
      (@step_result.terminate (optbyte × state))
      -- ask is special: it should receive the [extra_input] if we have any remaining
      (λ (f : byte -> state), 
        let f' : byte -> (optbyte × state) := λ (char : fin 256), ([], f char) in
        uncons extra_input
          -- no extra input
          (step_result.ask f')
          -- use the extra input
          (λ byte rest, step_result.step (rest, f byte))
        )
      -- print
      (λ s,
        let byte := s.fst in
        let s := s.snd in
        step_result.print (byte, (extra_input, s))
      )
      -- step
      (λ s,
        step_result.step (extra_input, s)
      ))))

constant is_correct_parse : program -> list byte -> Prop

constant correct : 
  ∀ (p : program) (s : list byte), is_correct_parse p s
   -> 
    process_equivalent
       (feed_input (s ++ [zero_byte]) (interpret brainfuck_interpreter))
       (interpret p)

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
