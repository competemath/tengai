import TengaiData.Fx

-- the namespace is not open: a scoped instance is not found, as in the library it came from
example : Nonempty (Fx.Tg Bool) := ⟨inferInstance⟩
