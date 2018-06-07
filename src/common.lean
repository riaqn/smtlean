attribute [reducible]
def parse_error := string

class has_from_string (α : Type _) :=
(from_string {} : string → except parse_error α)

export has_from_string (from_string)
