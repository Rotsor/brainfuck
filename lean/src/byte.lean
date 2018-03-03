def byte := fin 256

namespace byte
  instance : has_add(byte) := ⟨fin.add⟩
  instance : has_one(byte) := ⟨(1 : fin 256)⟩
  instance : has_zero(byte) := ⟨(0 : fin 256)⟩

  def increment : byte -> byte :=
    fin.add 1

  def decrement : byte -> byte :=
    fin.add 255

  def zero : byte := (0 : fin 256)
end byte