

structure Node where
  children : List Nat  -- index
deriving Repr, DecidableEq, Inhabited

#check Node

-- terminal, this will be node 0
def t  : Node := { children := [] }
#eval t

-- v1, this will be node 1
def v1 : Node := { children := [ 0, 0 ] }
--   v1
--  /  \
-- t    t

-- v2, this will be node 2
def v2 : Node := { children := [ 1, 0 ] }
--            v2
--           /  \
--          v1   t
--         /  \
--        t    t

#eval t.children.length  -- 0 direct children
#eval v1.children.length -- 2 direct children
#eval v2.children.length -- 2 direct children

#eval (v1 = v2) -- false, they are not (structurally the same)

def v3 : Node := { children := [ 1, 0 ] } -- another node with same children
#eval (v2 = v3) -- true, they are not (structurally the same)

structure DAG where
  nodes: List Node
  -- root:  Nat

def dag : DAG := { nodes := [t, v1, v2], /- root := 2 -/ }

#eval dag              -- the whole DAG
#eval dag.nodes        -- the nodes of the DAG
#eval dag.nodes[0]     -- node index 0 (the t node)
#eval dag.nodes[1]     -- node index 1 (the v1 node)
#eval dag.nodes[2]     -- node index 2 (the v1 node)
#eval dag.nodes.length -- the number of nodes of the DAG


def dfs_fuel (dag:DAG) (nodes: List Nat) (fuel: Nat): Nat :=
  match fuel with
  | 0 => panic "too little fuel"
  | f + 1 =>
    match nodes with
    | [] => 0
    | node :: nl =>
      let n : List Nat := dag.nodes[node]!.children
      1 + dfs_fuel dag n f + dfs_fuel dag nl f


#eval (dfs_fuel dag [2] 5)


def dfs (dag:DAG) (nodes: List Nat) : Nat :=
  match nodes with
  | [] => 0
  | node :: nl =>
    let n : List Nat := dag.nodes[node]!.children
    1 + dfs dag n + dfs dag nl

    termination_by
      have sorry
      -- my idea is that it should be possible to prove it by cases nodes
      -- [] trivial
      -- node:: nl
      -- dfs dag n < dfs nodes
      -- dfs dag nl < dfs nodes
      -- how would I express that?

#eval! (dfs dag [2])
