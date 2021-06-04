// Learn more about F# at http://fsharp.org

open System

exception ShitGoneHaywire of String;

type Tree<'a> = Node of 'a * Tree<'a> list
// Extent contains 1: leftmost location and 2: rightmost location in each row
type Extent = (float * float) list

let rmax (p:float) (q:float) :float  =
    if p > q then p else q

let moveextent (es:Extent) x = List.map ( fun (p,q) -> (p+x, q+x)) es

let rec merge ps qs =
    match (ps,qs) with
    | ([], qs) -> qs
    | (ps, []) -> ps
    | (((p,_)::ps), ((_,q)::qs)) -> (p,q) :: merge ps qs

//find the rightmost 
let rec fit (l1:Extent) (l2:Extent) =
    printf "l1 is %A" l1
    printf "l2 is %A" l2
    match (l1,l2) with
    | (((_,p)::ps), ((q,_)::qs)) ->
        printf "p is %f" p
        rmax (fit ps qs) (p-q+1.0)
    | ([],[]) ->
        0.0
    | (_,_) ->
        0.0

//TODO: WHAT IS ES??
let fitlistleft es =
    printf "es is %A" es
    let rec fitlistinner acc es =
        match es with
        | (e::es) ->
            let x = fit acc e;
            x :: fitlistinner( (merge acc (moveextent e x))) es
        | [] -> []
    fitlistinner [] es

let e1 :Extent = [(0.0,2.0) ; (0.0, 5.0)]
let e2 :Extent = [(4.0,5.0) ; (9.0, 13.0)]

let t = Node(5, [Node(2, [Node(1,[])]); Node(3,[]); Node(4,[Node(1,[])])])

[<EntryPoint>]
let main argv =
//    printfn "Hello World from F#!"
//    0 // return an integer exit code
    let k = fitlistleft( [e1;e2]);
    printfn ""
    printf "lol %A" k

    1

