constants p q : Prop

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

theorem t1 : p → q → p :=
assume x,
assume y,
show p, 
from x