import TengaiData.FxAB

-- both private instances are found, the one of each module: they were added to the environment as the source has them, whatever their names have in common
example : Nonempty (Fx.Sz Bool) := ⟨inferInstance⟩
example : Nonempty (Fx.Sz Int) := ⟨inferInstance⟩
