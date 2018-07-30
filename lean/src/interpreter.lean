import .ast
import .unix

namespace brainfuck
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
    | ((tape, tape_position), []) :=
      step_result.print (48, (tape, tape_position), [])
    | ((tape, tape_position), (instruction.plus :: k)) :=
      step_result.print (43, (modify_tape tape tape_position (byte.increment (tape tape_position)), tape_position), k)
    | ((tape, tape_position), (instruction.minus :: k)) :=
      step_result.print (45, (modify_tape tape tape_position (byte.decrement (tape tape_position)), tape_position), k)
    | ((tape, tape_position), (instruction.print :: k)) :=
      step_result.print (tape tape_position, ((tape, tape_position), k))
    | ((tape, tape_position), (instruction.ask :: k)) :=
      step_result.ask (λ x , ((modify_tape tape tape_position x, tape_position), k))
    | ((tape, tape_position), (instruction.right :: k)) :=
      step_result.print (62, (tape, tape_position + 1), k)
    | ((tape, tape_position), (instruction.left :: k)) :=
      step_result.print (60, ((tape, tape_position - 1), k))
    | ((tape, tape_position), (instruction.loop body :: k)) :=
      if tape tape_position = byte.zero
      then
      step_result.print (120, (tape, tape_position), k)
      else
      step_result.print (46, (tape, tape_position), (list.append body (instruction.loop body :: k)))

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
