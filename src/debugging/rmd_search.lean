import sli.sli
namespace rmd_search
open sli.toTR

def EmptinessChecker (C α : Type) := TR C → (C → α) → list C


-- The counter example should not contain the start state
def search_breakpoint (C α : Type) (o : TR C) (reducer : C → α)  : list C := 
  --under-approximating dfs/bfs here
  sorry

-- def search_breakpoint(o: TR C) (reduce: C → α): list C :=
--     k = {}
--     wt = ()
--     for s ∈ o.initial do
--         if dfs o reduce s k wt then return wt end if
--     end for
--     return wt

-- def dfs (o: TR C) (reduce: C → α) 
-- (s: C) (k: set C) (wt: list C): bool :=
--     if o.accepting s then 
--         wt = wt.append(s)
--         return true
--     end if
--     k = k ∪ { s }
--     for t ∈ o.next s do
--         if (reduce t) ∉ k then
--             if dfs o red t k wt then
--                 wt = wt.append(s)
--                 return true 
--             end if
--         end if
--     end for
--     return false
-- end 

end rmd_search