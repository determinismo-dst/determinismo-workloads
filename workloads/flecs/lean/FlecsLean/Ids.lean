/-
  Ids, generations and pairs, as in flecs v4.2.0
  include/flecs/private/api_defines.h 320-365 and src/world.c 24-102.
-/
namespace Flecs

abbrev Id := UInt64

/-- api_defines.h 331-335 -/
def ID_FLAGS_MASK : UInt64 := (0xFF : UInt64) <<< 60
def ENTITY_MASK : UInt64 := 0xFFFFFFFF
def GENERATION_MASK : UInt64 := (0xFFFF : UInt64) <<< 32
def COMPONENT_MASK : UInt64 := ~~~ ID_FLAGS_MASK
def PAIR : UInt64 := (1 : UInt64) <<< 63
/-- `ECS_AUTO_OVERRIDE` (world.c 11) -/
def AUTO_OVERRIDE : UInt64 := (1 : UInt64) <<< 62

def generation (e : UInt64) : UInt64 := (e &&& GENERATION_MASK) >>> 32
/-- `ECS_GENERATION_INC` (api_defines.h 335): the 16-bit generation wraps. -/
def genInc (e : UInt64) : UInt64 :=
  (e &&& ~~~ GENERATION_MASK) ||| ((0xFFFF &&& (generation e + 1)) <<< 32)

def lo32 (e : UInt64) : UInt64 := e &&& ENTITY_MASK

def isPair (id : Id) : Bool := (id &&& ID_FLAGS_MASK) == PAIR
/-- `ECS_PAIR_FIRST` / `ECS_PAIR_SECOND` (api_defines.h 340-341). -/
def pairFirst (id : Id) : UInt64 := ((id &&& COMPONENT_MASK) >>> 32) &&& ENTITY_MASK
def pairSecond (id : Id) : UInt64 := id &&& ENTITY_MASK
/-- `ecs_pair(rel, tgt)` = `ECS_PAIR | ((uint64)rel << 32) + (uint32)tgt`: both
    halves lose their generation bits (api_defines.h 357-361). -/
def mkPair (r t : UInt64) : Id := PAIR ||| (r <<< 32) ||| (t &&& ENTITY_MASK)

/-- FLECS_HI_COMPONENT_ID (flecs.h 286). -/
def HI : UInt64 := 256

/-! Builtin ids, src/world.c 24-102 (FLECS_HI_COMPONENT_ID + n). -/
def EcsPrefab : Id := HI + 9
def EcsWildcard : Id := HI + 14
def EcsAny : Id := HI + 15
def EcsExclusive : Id := HI + 26
def EcsChildOf : Id := HI + 30
def EcsIsA : Id := HI + 31
def EcsOnDelete : Id := HI + 39
def EcsOnDeleteTarget : Id := HI + 40
def EcsRemove : Id := HI + 54
def EcsDelete : Id := HI + 55
def EcsPanic : Id := HI + 56
/-- flecs.h 1961 -/
def EcsFirstUserEntityId : UInt64 := HI + 128

/-- `ecs_id_is_wildcard` (id.c 93-112), without value pairs. -/
def isWildcard (id : Id) : Bool :=
  if id == EcsWildcard || id == EcsAny then true
  else if !isPair id then false
  else
    let f := pairFirst id
    let s := pairSecond id
    f == EcsWildcard || s == EcsWildcard || f == EcsAny || s == EcsAny

/-- `ecs_id_match` (id.c 12-84) for the id shapes the model uses. -/
def idMatch (id pattern : Id) : Bool :=
  if id == pattern then true
  else if (pattern &&& PAIR) != 0 then
    if (id &&& PAIR) == 0 then false
    else
      let pf := pairFirst pattern
      let ps := pairSecond pattern
      if pf == EcsWildcard then ps == EcsWildcard || ps == pairSecond id
      else if ps == EcsWildcard then pf == pairFirst id
      else false
  else
    if (id &&& ID_FLAGS_MASK) != (pattern &&& ID_FLAGS_MASK) then false
    else (COMPONENT_MASK &&& pattern) == EcsWildcard

end Flecs
