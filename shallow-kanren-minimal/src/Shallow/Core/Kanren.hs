module Shallow.Core.Kanren
(
  Relation(Relation)
, Kanren(KVar)
, KanrenEval
, LogicType
, L
, fresh, fresh2, fresh3, fresh4, fresh5
, relation, relation2, relation3, relation4, relation5
, rule, rule2, rule3, rule4, rule5
, axiom, axiom2, axiom3, axiom4
, rules, rules2, rules3, rules4
, call, embed
, eval
, run, run2, run3, run4, run5
, (===), (<=>)
, conde
) where

import Shallow.Core.Internal.Kanren
import Shallow.Utils.Kanren
import Shallow.Utils.Rule
import Shallow.Core.Internal.Logic