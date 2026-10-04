import Base
import ./LAWS.bend as Laws
import ./Square6.bend as S

def Laws.square6_has_packing_at_three(F, field):
  S.Square6.packing(~F, ~field)
