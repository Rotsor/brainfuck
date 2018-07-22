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
end brainfuck
