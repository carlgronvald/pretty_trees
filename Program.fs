﻿// Learn more about F# at http://fsharp.org

module Program

open System
open FsCheck

type Tree<'a> = Node of 'a * Tree<'a> list
let t = Node('a', [Node('b', [Node('c',[])]); Node('d',[]); Node('e',[Node('f',[])])])

exception NodeNoChildren of string 

// Extent contains 1: leftmost location and 2: rightmost location in each row
type Extent = (float * float) list

// Tree positioning functions
let rmax (p:float) (q:float) :float  =
    if p > q then p else q

let move_extent ((es:Extent),(x:float)) : Extent = List.map ( fun (p,q) -> (p+x, q+x)) es
let flip_extent (e : Extent) = List.map(fun (p,q) -> (-p, -q)) e
let move_tree (Node((label, x), subtrees) , (xprime:float)) =
    Node((label, x+xprime), subtrees)

let rec merge ps qs =
    match (ps,qs) with
    | ([], qs) -> qs
    | (ps, []) -> ps
    | (((p,_)::ps), ((_,q)::qs)) -> (p,q) :: merge ps qs

let merge_list es = List.fold merge [] es

// find the least left offset of the extent l2.
let rec fit (l1:Extent) (l2:Extent) =
    match (l1,l2) with
    | (((_,p)::ps), ((q,_)::qs)) ->
        rmax (fit ps qs) (p-q+1.0)
    | (_,_) ->
        0.0

let fit_list_left es =
    let rec fit_list_inner acc es =
        match es with
        | (e::es) ->
            let x = fit acc e;
            x :: fit_list_inner (merge acc (move_extent (e,x))) es
        | [] -> []
    fit_list_inner [] es

let fit_list_right es =
    let rec fit_list_inner acc es =
        match es with
        | (e::es) ->
            let x = -(fit e acc);
            x :: fit_list_inner (merge (move_extent (e,x)) acc) es
        | [] -> []
    List.rev (fit_list_inner [] (List.rev es))


let mean (x,y) = (x+y)/2.0
/// The mean of right fitting and left fitting gives us a perfectly symmetric fit.
let fit_list es = List.map mean (List.zip (fit_list_left es) (fit_list_right es))



/// Returns a positioned tree where all nodes have a location
let design tree =
    let rec design_inner (Node(label, subtrees)) =
        let (trees, extents) = List.unzip (List.map design_inner subtrees)
        let positions = fit_list extents
        let ptrees = List.map move_tree (List.zip trees positions)
        let pextents = List.map move_extent (List.zip extents positions)
        let resultextent = (0.0,0.0) :: merge_list pextents
        let resulttree = Node((label, 0.0), ptrees)
        (resulttree, resultextent)

    design_inner tree |> fst


// FSCHECK/VERIFICATION FUNCTIONS //
// Criterion 1 functions

/// Converts a relatively positioned tree to an absolutely positioned tree 
let absolute_positioned_tree postree =
    let rec helper (Node((label, position), ts)) (translation:float) =
        Node((label, position+translation), (List.map (fun t -> helper t (translation+position) ) ts))
    helper postree 0.0

/// Do a breadth first search by level
/// Returns a list of lists of nodes, where each list is one level.
let level_bfs tree =
    // The concept is to keep a list of nodes to be traversed both for the 
    // current level and the next level. Then, when the current level is 
    // empty, the current accumulator is appended to the total accumulator
    // (The current accumulator keeps a list of labels, the total
    // keeps a list of lists of labels)
    let rec helper current_level next_level acc acc_old =
        match current_level with
        | [] -> //Case where the current level is empty, and we go on to the next level
            match next_level with
            | [] -> acc_old @ [acc]
            | _ -> helper next_level [] [] (acc_old @ [acc])
        | Node(x, ts)::rest -> //Case where the current level is not empty, so we continue in the current level
            helper rest (next_level@ts) (acc @ [x]) acc_old
    helper [tree] [] [] []


let rec verify_level level =
    match level with 
    | [] -> true
    | (node,pos)::[] -> true
    | (node1,pos1)::(node2,pos2)::rest -> (pos1 <= (pos2 - 1.0)) && (verify_level ((node2,pos2)::rest))

// Check one level at a time
let check_positions postree =
    let rec helper levels =
        match levels with
        | [] -> true
        | level::rest -> verify_level level && helper rest

    let bfs_levels = level_bfs postree
    helper bfs_levels



// Criterion 2 functions
let extractLocations trees = List.map (fun (Node((label, location), subtrees)) -> location) trees

let extractMean subtrees = ((subtrees |> extractLocations |> List.max)+(subtrees |> extractLocations |> List.min))/2.0

let list_mean (xs : float list) : float =
    (List.fold (fun acc n -> acc + n) 0.0 xs) / (float (xs.Length))

let get_node_pos (Node((_,pos),_)) = pos


let mean_pos_of_children abs_postree =
    match abs_postree with
    | (Node((v,abs_pos),[])) -> raise (NodeNoChildren ("This node has no children"))
    | (Node((v,abs_pos),st)) -> extractMean st

let rec validate_children_positions abs_postree =
    match abs_postree with
    | (Node((v,abs_pos),[])) -> true // No children, must be centered correctly
    | (Node((v,abs_pos),st)) -> // Check that mean of subtree node positions equals abs_pos
            abs(abs_pos-(mean_pos_of_children abs_postree)) < 0.0000001 && // Avoid float rounding errors
            List.fold (fun acc elem -> acc && (validate_children_positions elem)) true st




// Criterion 3 functions
let rec reflect (Node(v, subtrees)) =
    Node(v, List.map reflect (List.rev subtrees))

let rec reflectpos (Node((v,x : float), subtrees)) =
    Node((v, -x), List.map reflectpos subtrees)

let preorder tree =
    let rec helper depth subtree =
        match subtree with
        | Node(_, []) -> 
            [depth]
        | Node(_, ts) ->
            depth :: List.collect (helper (depth+1)) ts
    helper 0 tree

let flat_bfs tree =
    let rec helper next acc =
        match next with
        | [] -> acc
        | Node(x, ts)::rest ->
            helper (rest@ts) (Node(x,ts)::acc)
    helper [tree] []




let matching_pairs pairs = List.fold (fun s (x,y) -> s && x = y) true pairs

let matching_preorder given_preorder node =
    preorder node = given_preorder

/// Returns whether two subtrees are designed in the same way
let same_design (Node(_,subtrees_1)) (Node(_,subtrees_2)) =
    let extract_design trees = (List.map (fun (Node((v,p),ts)) -> p) (flat_bfs trees))
    let pairs = List.zip (List.collect extract_design subtrees_1) (List.collect extract_design subtrees_2)
    matching_pairs pairs

//let positioned_tree = design t
//let preorder_filtered = 
//let designs = List.map (same_design positioned_tree) preorder_filtered
let all_equivalent_subtrees_match positioned_tree positioned_subtree =
    let equivalent_trees = List.filter (matching_preorder (preorder positioned_subtree)) (flat_bfs positioned_tree)
    let matching_designs = List.map (same_design positioned_subtree) equivalent_trees
    List.reduce (&&) matching_designs


/// TODO: EITHER IMPLEMENT OR REMOVE THIS
/// Finds the least right positions of all subtrees with passed extents.
/// Does exactly the opposite of fit_list_right
let fit_list_right_good = List.rev << (List.map (fun x -> -x)) << fit_list_left << (List.map flip_extent) << List.rev




[<EntryPoint>]
let main argv =
    printfn ""
    let k = design t
    //printfn "positioned tree: %A" k

    // FSCHECK: Criterion 1
    printfn "\n\nFsCheck Criterion 1 test:"
    let check_criterion1 test_tree = check_positions (absolute_positioned_tree (design test_tree))
    Check.Quick check_criterion1

    // FSCHECK: Criterion 2
    printfn "\n\nFsCheck Criterion 2 test:"
    let check_criterion2 test_tree = validate_children_positions (absolute_positioned_tree (design test_tree))
    Check.Quick check_criterion2

    // FSCHECK: Criterion 3
    printfn "\n\nFsCheck Criterion 3 test:"
    let check_criterion3 test_tree =
        let ds = design test_tree
        let ref_ds = (test_tree |> reflect |> design |> reflectpos |> reflect )
        let extract_design designed = designed |> flat_bfs |> List.map (fun (Node((v2,p2),ts)) -> (v2,p2))
        let pairs = List.zip (ds |> extract_design) (ref_ds |> extract_design)
        matching_pairs pairs
    Check.Quick check_criterion3

    printfn "\n\nFsCheck Criterion 4 test:"
    let check_criterion4 test_tree =
        let designed = design test_tree
        let equivs_that_match = List.map (all_equivalent_subtrees_match designed) (flat_bfs designed)
        List.reduce (&&) equivs_that_match
    
    Check.Quick check_criterion4
    1

