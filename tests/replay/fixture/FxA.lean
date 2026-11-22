import Fx

/-! Two modules each with a PRIVATE instance of the same user-facing name (`Fx.instCollide`): in Tengoku this is ordinary (every module has its own private names), in one replayed module it is a collision of Lean's
registry of newly added constants, which keys them by the name without the private prefix (tests/test_replay.py). -/
namespace Fx
private instance instCollide : Sz Bool := ⟨3⟩
-- a statement that mentions the private instance: an export carries what its constants mention, not every private constant
theorem collideA : Sz.n Bool = 3 := rfl
end Fx
