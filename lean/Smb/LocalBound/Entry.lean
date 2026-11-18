import Smb.Tas

/-!
# Exact entry state for the optional local bound

This is the complete model state after the first 17,863 aligned HappyLee inputs,
not merely a position or RAM checkpoint. `tasInputs` omits the movie's first idle
frame for the established startup alignment. Thus the entry is after zero-indexed
model frame 17,862. It starts from `Smb.initial`: fixed power-on and one reset,
with controller 2 idle and no later resets.
-/
namespace Smb.LocalBound

/-- Preserve the full replay state, including timing, PPU, controllers and open bus. -/
def entry : NES := NES.runFrames (tasInputs.take 17863) initial

end Smb.LocalBound
