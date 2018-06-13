import data.buffer

attribute [reducible]
def parse_error := string

class has_from_buffer (α : Type _) :=
(from_buffer {} : char_buffer → except parse_error α)

export has_from_buffer (from_buffer)

class has_from_string (α : Type _) :=
(from_string {} : string → except parse_error α)

export has_from_string (from_string)

instance has_from_string_via_buffer {α : Type _} [has_from_buffer α] : has_from_string α :=
⟨ λ s, from_buffer (s.to_char_buffer)⟩

instance except_has_to_string {α β : Type} [has_to_string α] [has_to_string β] : has_to_string (except α β) :=
⟨λ e, match e with
| except.error a := "ERROR\n" ++ to_string a
| except.ok b := "OK\n" ++ to_string b
end
⟩
