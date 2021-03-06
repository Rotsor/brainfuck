import .byte
open byte
namespace unix
namespace with_coinduction 
  inductive step_result (state : Type) : Type
  | ask : (byte -> state) -> step_result
  | print : byte × state -> step_result
  | step : state -> step_result

  structure process : Type 1 :=
    (state : Type)
    (initial_state : state)
    (transition : state -> step_result state)

  inductive process_equivalence_step
    (eq : process → process → Prop) : process → process → Prop
  | step1 :
    ∀ (p1 p2 : process) (s1 : p1.state), 
    (p1.transition p1.initial_state = step_result.step s1)
    ∧ eq 
    {
      state := p1.state,
      initial_state := s1,
      transition := p1.transition
    }
    p2
    → process_equivalence_step p1 p2      
  | step2 :
    ∀ (p1 p2 : process) (s2 : p2.state), 
    (p2.transition p2.initial_state = step_result.step s2)
    ∧ eq 
    p1
    {
      state := p2.state,
      initial_state := s2,
      transition := p2.transition
    }
    → process_equivalence_step p1 p2      
  | ask : 
    ∀ (p1 p2 : process) (f1 : byte → p1.state) (f2 : byte → p2.state), 
    (p1.transition p1.initial_state = step_result.ask f1)
    ∧ (p2.transition p2.initial_state = step_result.ask f2)
    ∧ (∀ c, eq 
    {
      state := p1.state,
      initial_state := f1 c,
      transition := p1.transition
    }
    {
      state := p2.state,
      initial_state := f2 c,
      transition := p2.transition
    })
    → process_equivalence_step p1 p2
  | print : 
    ∀ (p1 p2 : process) (b1 : byte) (b2 : byte) (s1 : p1.state) (s2 : p2.state), 
    (p1.transition p1.initial_state = step_result.print (b1, s1))
    ∧ (p2.transition p2.initial_state = step_result.print (b2, s2))
    ∧ eq 
    {
      state := p1.state,
      initial_state := s1,
      transition := p1.transition
    }
    {
      state := p2.state,
      initial_state := s2,
      transition := p2.transition
    }
    → process_equivalence_step p1 p2      

  def process_equivalence (p1 : process) (p2 : process) : Prop :=
    ∃ (eq : process → process → Prop), eq p1 p2 ∧ (∀ p1 p2, eq p1 p2 -> process_equivalence_step eq p1 p2)

  def uncons {A R : Type} : list A -> R -> (A → list A → R) → R
  | list.nil := λ nil _, nil
  | (x :: xs) := λ _ cons, cons x xs

  def feed_input : list byte -> process -> process :=
    λ input proces,
    let state := proces.state in
    let state0 := proces.initial_state in
    let step := proces.transition in
    ({ 
      state := (list byte × state),
      initial_state := (input, state0),
      transition := (λ s, 
      let extra_input := s.fst in
      @step_result.rec_on
        state 
        (λ _, step_result (list byte × state)) (step s.snd)
        -- ask is special: it should receive the [extra_input] if we have any remaining
        (λ (f : byte -> state), 
          let f' : byte -> (list byte × state) := λ (char : fin 256), ([], f char) in
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
        ))
        })
  
  def transition_function (s : Type) : Type := (s → step_result s)

  def run_s {s : Type} (transition : transition_function s) : nat → s → list byte → list byte × (s × list byte)
  | nat.zero := λ s input, ([], (s, input))
  | (nat.succ n) := λ s input,
    match transition s with
    | step_result.ask f :=
      match input with
      | [] := ([], s, input)
      | head :: rest := run_s n (f head) rest
      end
    | step_result.print (char, s) :=
      let res := run_s n s input in
      ((char :: res.fst), res.snd)
    | step_result.step s :=
      run_s n s input
    end

  

end with_coinduction 
namespace relational_honest

  inductive mode : Type
  | active
  | waiting
  | spins

  inductive label : mode → Type
  | output : byte → label mode.active
  | ask : label mode.waiting
  | spin : label mode.spins

  -- describes a set of behaviors
  structure spec : Type 1 :=
    (state : mode → Type)
    (initial_state : state mode.active)
    (transition : ∀ {m} (s : state mode.active), label m → state m → Prop)
    (take_input : state mode.waiting → byte → state mode.active)

  def is_determined (spec : spec) : Prop :=
    (∀ (s : spec.state mode.active), ∃! (m : mode) (l : label m) (s' : spec.state m), spec.transition s l s')

end relational_honest

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

end in_out_mixed_up

namespace another
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
end another

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

end unix