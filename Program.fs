// Learn more about F# at http://fsharp.org

module Program

open Trees
open BasicFunctions

let t = Node('a', [Node('b', [Node('c',[])]); Node('d',[]); Node('e',[Node('f',[])])])


[<EntryPoint>]
let main argv =
    printfn ""
    let k = design t
    printf "positioned tree: %A" k
    1

