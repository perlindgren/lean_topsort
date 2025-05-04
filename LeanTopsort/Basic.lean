

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
def v2 : Node := { val := 0, inputs := [ 2, 1 ] }
--            v2
--           /  \
--          v1   t1
--         /  \
--        t0    t1

#eval t0.inputs.length -- 0 inputs
#eval v1.inputs.length -- 2 inputs
#eval v2.inputs.length -- 2 inputs
#eval (v1 = v2) -- false, they are not the same, inputs differ, DecidableEq

def v3 : Node := { val:= 0, inputs := [ 2, 1 ] } -- another node with same val and inputs
#eval (v2 = v3) -- true, they are the same

def v4 : Node := { val:= 1, inputs := [ 2, 1 ] } -- another node with same inputs
#eval (v2 = v4) -- false, they are not the same, value differs

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
  | false => panic "reference to self or future node"
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

def d_err := add_node dt0t1v1 { val:= 0, inputs := [0,1,2,3]} -- index 3 is not in dt0t1tv1
#eval! d_err -- this should panic

def dt0t1v1v2 := add_node dt0t1v1 v2  -- index 3
#eval! dt0t1v1


#eval dt0t1v1v2              -- the whole DAG
#eval dt0t1v1v2.nodes        -- the nodes of the DAG
#eval dt0t1v1v2.nodes[0]     -- node index 0 (the t0 node)
#eval dt0t1v1v2.nodes[1]     -- node index 1 (the t1 node)
#eval dt0t1v1v2.nodes[2]     -- node index 2 (the v1 node)
#eval dt0t1v1v2.nodes.length -- the number of nodes in the DAG


-- for dfs we need to give a termination condition
-- we know that the depth is maximum the number of nodes in the tree
-- as we will try vising edges of terminals (nodes without edges) we have to add 1
def fuel (d: DAG) : Nat := d.nodes.length + 1
#eval (fuel dt0t1v1v2)

-- we can compute the total number of nodes spanned by trees rooted by the "edges" as:
def dfs_fuel (dag:DAG) (edges: List Nat) (fuel: Nat): Nat :=
  let _ := println! "here"
  match fuel with
  | 0     => panic "too little fuel"
  | f + 1 =>
    match edges with
    | []         => 0
    | edge :: el =>
      let e : List Nat := dag.nodes[edge]!.inputs
      1 + dfs_fuel dag e f + dfs_fuel dag el f

def dfs (dag: DAG) (e: Nat) : Nat :=
  let b : Bool :=  e < dag.nodes.length
  match b with
  | false => panic "edge not i DAG"
  | true  => dfs_fuel dag [e] (fuel dag)

#eval (dfs dt0t1v1v2 0) -- 1
#eval (dfs dt0t1v1v2 1) -- 1
#eval (dfs dt0t1v1v2 2) -- 3
#eval (dfs dt0t1v1v2 3) -- 5
#eval (dfs dt0t1v1v2 4) -- edge not in dag

-- we can apply some function over the spanned tree
-- f is a function from n.val (the value of the node),
-- the return value of the first edge
-- the return value of the remaining edges
def dfs_f_fuel (dag:DAG) (edges: List Nat) (f: Nat -> Nat -> Nat -> Nat) (fuel: Nat): Nat :=
  let _ := println! "here"
  match fuel with
  | 0     => panic "too little fuel"
  | fuel' + 1 =>
    match edges with
    | []         => 0
    | edge :: el =>
      let n := dag.nodes[edge]!
      let e := n.inputs
      f n.val (dfs_f_fuel dag e f fuel') (dfs_f_fuel dag el f fuel')

def dfs_f (dag: DAG) (e: Nat) (f: Nat -> Nat -> Nat -> Nat): Nat :=
  let b : Bool :=  e < dag.nodes.length
  match b with
  | false => panic "edge not i DAG"
  | true  => dfs_f_fuel dag [e] f (fuel dag)

-- example, lets sum the values of spanned nodes
def sum (v e el : Nat): Nat := v + e + el

#eval (dfs_f dt0t1v1v2 0 sum) -- 0, only the t0 node
#eval (dfs_f dt0t1v1v2 1 sum) -- 1, only the t1 node
#eval (dfs_f dt0t1v1v2 2 sum) -- 1, v1 node, v1 + t0 + t1, 0 + 0 + 1
#eval (dfs_f dt0t1v1v2 3 sum) -- 2, v2 node, v2 + v1 + t0 + t1 + t1, 0 + 0 + 0 + 1 + 1
