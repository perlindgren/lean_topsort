

structure Node where
  val : Nat
  inputs : List Nat  -- index in DAG.nodes
deriving Repr, DecidableEq, Inhabited

#check Node

-- terminal, this will be node 0
def t0  : Node := { val := 0,  inputs := [] }
#eval t0

-- terminal, this will be node 1
def t1  : Node := { val := 1,  inputs := [] }
#eval t0


-- v1, this will be node 2
def v1 : Node := { val := 0, inputs := [ 0, 1 ] }
--   v1
--  /  \
-- t0    t1

-- v2, this will be node 3
def v2 : Node := { val := 0, inputs := [ 1, 0 ] }
--            v2
--           /  \
--          v1   t0
--         /  \
--        t1    t0

#eval t0.inputs.length -- 0 inputs
#eval v1.inputs.length -- 2 inputs
#eval v2.inputs.length -- 2 inputs
#eval (v1 = v2) -- false, they are not the same, inputs differ, DecidableEq

def v3 : Node := { val:= 0, inputs := [ 1, 0 ] } -- another node with same val and inputs
#eval (v2 = v3) -- true, they are the same

def v4 : Node := { val:= 1, inputs := [ 1, 0 ] } -- another node with same inputs
#eval (v2 = v4) -- true, they are not the same, value differs

structure DAG where
  nodes: List Node
  p: ∀ (h:i < nodes.length) (j: Nat), j ∈ nodes[i].inputs -> j < i
deriving Repr

def dag_empty: DAG :=  { nodes:= [], p:= by simp }

instance : Inhabited DAG where
  default := dag_empty

def add_node (d : DAG) (n: Node): DAG :=
  let check := n.inputs.all (λ k => k < d.nodes.length)
  match ch_cond: check with
  | false => panic "reference to future node"
  | true  => {
    nodes:= d.nodes ++ [n],
    p:= by
      intros i h j jh
      -- at this point ch_cond holds
      -- either:
      -- rw [List.all_eq_true] at ch_cond
      -- simp at ch_cond
      -- or just:
      simp [check] at ch_cond
      simp [List.getElem_append] at jh
      split at jh
      . apply d.p
        -- can be solved either by
        -- exact jh, or
        assumption
      . -- here we can introduce h_spec
        -- have h_spec := ch_cond j jh
        -- or specialize directly
        specialize ch_cond j jh
        omega
    }

def dt0 := add_node dag_empty t0  -- index 0
#eval! dt0

def dt0t1 := add_node dt0 t1      -- index 1
#eval! dt0t1

def dt0t1v1 := add_node dt0t1 v1  -- index 2
#eval! dt0t1v1

def d_err := add_node dt0t1v1 { val:= 0, inputs := [0,1,2]}
#eval! d_err -- this should panic

#eval dt0t1v1              -- the whole DAG
#eval dt0t1v1.nodes        -- the nodes of the DAG
#eval dt0t1v1.nodes[0]     -- node index 0 (the t0 node)
#eval dt0t1v1.nodes[1]     -- node index 1 (the t1 node)
#eval dt0t1v1.nodes[2]     -- node index 2 (the v1 node)
#eval dt0t1v1.nodes.length -- the number of nodes of the DAG


-- def dfs_fuel (dag:DAG) (nodes: List Nat) (fuel: Nat): Nat :=
--   match fuel with
--   | 0 => panic "too little fuel"
--   | f + 1 =>
--     match nodes with
--     | [] => 0
--     | node :: nl =>
--       let n : List Nat := dag.nodes[node]!.inputs
--       1 + dfs_fuel dag n f + dfs_fuel dag nl f


-- #eval (dfs_fuel dag_empty [2] 5)


-- def dfs (dag:DAG) (nodes: List Nat) : Nat :=
--   match nodes with
--   | [] => 0
--   | node :: nl =>
--     let n : List Nat := dag.nodes[node]!.inputs
--     1 + dfs dag n + dfs dag nl

--     termination_by
--       have dfs_nil: dfs dag [] = 0 := by
--         sorry
--       have
--         sorry

--       -- my idea is that it should be possible to prove it by cases nodes
--       -- [] trivial
--       -- node:: nl
--       -- dfs dag n < dfs nodes
--       -- dfs dag nl < dfs nodes
--       -- how would I express that?

-- #eval! (dfs dag_empty [2])
