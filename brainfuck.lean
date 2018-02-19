def byte := fin 256
instance : has_add(byte) := ⟨fin.add⟩
instance : has_one(byte) := ⟨(1 : fin 256)⟩
instance : has_zero(byte) := ⟨(0 : fin 256)⟩

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

universes u v w

structure lift2 (α : Sort u) : Sort (u + 1) :=
mk :: (fst : α)


namespace relational

  namespace in_out_mixed_up
    inductive effect : Type
    | input : char → effect
    | output : char → effect

    structure process : Type 1 := 
      (state : Type)
      (initial_state : state)
      (valid_transition : state → effect → state → Prop)

    def trace := list effect

    inductive is_valid_trace_between_witness (p : process) : trace → p.state → p.state → Type
    | empty {} : ∀ s, is_valid_trace_between_witness [] s s
    | step : ∀ {s1 s2 s3 e rest}, p.valid_transition s1 e s2 → is_valid_trace_between_witness rest s2 s3 → is_valid_trace_between_witness (e :: rest) s1 s3

    def is_valid_trace_between (p : process) : trace → p.state → p.state → Prop :=
      λ t s1 s2, nonempty (is_valid_trace_between_witness p t s1 s2)

    def transition_effect {p : process} {e s1 s2} : p.valid_transition s1 e s2 → effect := λ _, e

    inductive valid_trace_between (p : process) : p.state → p.state → Type
    | empty {} : ∀ s, valid_trace_between s s
    | step : ∀ {s1 s2 s3 e}, p.valid_transition s1 e s2 → valid_trace_between s2 s3 → valid_trace_between s1 s3

    def compose_valid_trace {p : process} : ∀ {s1 s2 s3 : p.state}, valid_trace_between p s1 s2 → valid_trace_between p s2 s3 → valid_trace_between p s1 s3
    | _ ._ _ (valid_trace_between.step transition rest) := λ x, valid_trace_between.step transition (compose_valid_trace rest x)
    | _ ._ _ (valid_trace_between.empty _) := λ x, x

    def is_valid_trace_from (p : process) (t : trace) (s : p.state) : Prop :=
      ∃ (final_state : p.state), is_valid_trace_between p t s final_state

    def is_valid_trace (p : process) (t : trace) : Prop :=
      is_valid_trace_from p t p.initial_state

    def process_equivalent (p1 : process) (p2 : process) : Prop :=
      ∀ t, is_valid_trace p1 t ↔ is_valid_trace p2 t

    structure process_equivalence (p1 : process) (p2 : process) : Type :=
      (related : p1.state → p2.state → Prop)
      (initial_states_related :  related p1.initial_state p2.initial_state) 
      (transitions1 : ∀ s1 s2, related s1 s2 → ∀ e d1, p1.valid_transition s1 e d1 → ∃ d2, related d1 d2 ∧ p2.valid_transition s2 e d2)
      (transitions2 : ∀ s1 s2, related s1 s2 → ∀ e d2, p2.valid_transition s2 e d2 → ∃ d1, related d1 d2 ∧ p1.valid_transition s1 e d1)

    def is_reachable_from (p : process) (s1 s2 : p.state) : Prop :=
      ∃ (t : trace), nonempty (is_valid_trace_between_witness p t s1 s2)

    def is_reachable (p : process) (s : p.state) : Prop :=
      is_reachable_from p p.initial_state s

    def mk_valid_trace0 {p : process} : ∀ {t : trace}, ∀ {s1 s2 : p.state}, is_valid_trace_between_witness p t s1 s2 → valid_trace_between p s1 s2
    | ._ _ _ (is_valid_trace_between_witness.empty _) := valid_trace_between.empty _
    | ._ _ _ (is_valid_trace_between_witness.step transition rest) := valid_trace_between.step transition (mk_valid_trace0 rest)

    def mk_valid_trace {p : process} : ∀ {s1 s2 : p.state}, is_reachable_from p s1 s2 → nonempty (valid_trace_between p s1 s2) :=
      λ _ _ reachable, (exists.elim reachable (λ trace reachable, nonempty.elim reachable (λ witness, nonempty.intro (mk_valid_trace0 witness))))

    def unmk_valid_trace {p : process} : ∀ {s1 s2 : p.state}, valid_trace_between p s1 s2 → is_reachable_from p s1 s2
    | _ _ (valid_trace_between.step transition rest) := 
      let r := unmk_valid_trace rest in
      exists.elim r (λ t rest, exists.intro (transition_effect transition :: t) (nonempty.elim rest (λ rest, nonempty.intro (is_valid_trace_between_witness.step transition rest))))
    | _ _ (valid_trace_between.empty _) := exists.intro [] (nonempty.intro (is_valid_trace_between_witness.empty _))



    def reachability_step {p : process} {s1 s2 : p.state} : is_reachable p s1 → ∀ {t}, is_valid_trace_between p t s1 s2 → is_reachable p s2 :=
      λ s1_reachable _t trace_to_s2, 
        exists.elim s1_reachable (λ trace reachable,
          nonempty.elim reachable (λ witness1, 
            nonempty.elim trace_to_s2 (λ witness2,
            let composition := compose_valid_trace (mk_valid_trace0 witness1) (mk_valid_trace0 witness2) in
            unmk_valid_trace composition
          )
        ))
        

    def and3_intro {A B C : Prop} (a : A) (b : B) (c : C) : A ∧ B ∧ C :=
      and.intro a (and.intro b c)

    lemma lemma1 (p1 p2 : process) (equivalent : process_equivalent p1 p2) : process_equivalence p1 p2 :=
      { 
        related := λ s1 s2
          , is_reachable p1 s1 ∧
            is_reachable p2 s2 ∧
            (∀ t, 
            is_valid_trace_from p1 t s1 ↔
            is_valid_trace_from p2 t s2) ,
        initial_states_related := 
          and3_intro
            (Exists.intro [] (nonempty.intro (is_valid_trace_between_witness.empty _)))
            (Exists.intro [] (nonempty.intro (is_valid_trace_between_witness.empty _)))
            equivalent
          ,
        transitions1 :=
          λ s1 s2 s1_s2_related, λ e d1 s1_e_d1_valid,
            let s1_reachable := s1_s2_related.left in
            let s2_reachable := s1_s2_related.right.left in
            let related := s1_s2_related.right.right in
            let small_trace := [e] in
            let s1_to_d1 := nonempty.intro (is_valid_trace_between_witness.step s1_e_d1_valid (is_valid_trace_between_witness.empty _)) in
            let small_trace_valid1 := Exists.intro d1 s1_to_d1 in
            let small_trace_valid2 := (related [e]).mp small_trace_valid1 in
            let d1_reachable := reachability_step s1_reachable s1_to_d1 in
            exists.elim small_trace_valid2 (λ d2 s2_to_d2, Exists.intro d2 (
              and.intro
                (and3_intro
                  (reachability_step s1_reachable s1_to_d1)
                  (reachability_step s2_reachable s2_to_d2)
                  _)
                (singleton_trace_to_one_valid_transition d2_good)
            ))
      }
    

    def process_equivalent (p1 : process) (p2 : process) : Prop :=
      ∃ , (process_equivalent' p1 p2 related)

    def process_leq (p1 : process) (p2 : process) : Prop :=
      ∃ (related : p1.state → p2.state → Prop), (process_equivalent' p1 p2 related)
  end in_out_mixed_up

  def process : Type 1 :=
    Σ (active_state : Type), 
    (Σ (waiting_state : Type), 
      -- out transition
      (active_state → active_state → Prop)
      -- step transition
      × (active_state → active_state → Prop)
      -- ask transition
      × (active_state → waiting_state → Prop)
      -- input handler
      × (waiting_state → byte → active_state))
      
end relational

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

constant process_equivalent (process1 : process) (process2 : process) : Prop

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