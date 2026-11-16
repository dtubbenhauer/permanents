import BlockPermanents.ThreeChunks

namespace BlockPermanents.ThreeWire

/-- All unweighted composites of an upright list, a middle list and a
right-hand list, in the order in which their operators are multiplied. -/
def stacked (l m r : List Wire) : List Wire :=
  l.flatMap fun a => m.flatMap fun b => r.map fun c => a ∘ b ∘ c

def move13 : Wire := ![4,5,2,3,0,1]

/-- Forty-eight times the unbent Q₃ of Section 3C at thickness two.
The second four-slot clasp is the conjugate of the first by (13).
The 23 packet clasp has two terms, the identity and the whole interchange. -/
def fixedMarkedTerms : Terms :=
  let moved := fourList.map fun e => move13 ∘ e ∘ move13
  let g := [identity,fullSwap]
  weightedWires 6 allWires ++ weightedWires (-48) (packetOrders.map Prod.fst) ++
  weightedWires 6 (stacked pairList moved pairList) ++
  weightedWires (-3) (stacked fourList g pairList) ++
  weightedWires (-3) (stacked pairList g fourList)

end BlockPermanents.ThreeWire
