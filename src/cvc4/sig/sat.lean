namespace sig

def bool := bool
def tt := bool.tt
def ff := bool.ff

def satlem (α β : Prop) (x : α) (y : α → β) : β := y x
def satlem_simplify (α β : Prop) (x : α) (y : α → β) : β := y x

end sig
