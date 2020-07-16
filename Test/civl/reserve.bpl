const memLo: int;
const memHi: int;
axiom 0 < memLo && memLo <= memHi;
function memAddr(i:int) returns (bool) { memLo <= i && i < memHi }

const numMutators: int;
axiom 0 < numMutators;
function {:inline} mutatorAddr(i: int) returns (bool) { 1 <= i && i <= numMutators }

const GcTid: int;
axiom GcTid > numMutators;

function {:builtin "MapConst"} MapConstBool(bool): [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

function {:builtin "MapOr"} MapOr([X]bool, [X]bool) : [X]bool;
function {:builtin "MapNot"} MapNot(x: [int]bool) : [int]bool;
function {:inline} Subset(X: [int]bool, Y: [int]bool) : (bool)
{
    MapOr(MapNot(X), Y) == MapConstBool(true)
}

type X = int;

var {:layer 0,1} Free: [int]bool;
var {:layer 0,1} freeSpace: int;
var {:layer 0,1} AllocatingAtOrAfter: [int][X]bool;
var {:layer 0,1} NumFreeAtOrAfter: [int]int;

function Size([int]bool) returns (int);
axiom (forall X: [int]bool :: 0 <= Size(X));
axiom (forall X: [int]bool, x: int :: X[x] ==> 1 <= Size(X));
axiom (forall X: [int]bool, x: int :: X[x] ==> X[x:=true] == X);
axiom (forall X: [int]bool, x: int :: !X[x] ==> X[x:=false] == X);
axiom (forall X: [int]bool, x: int :: Size(X[x := false]) + 1 == Size(X[x := true]));
axiom (forall X, Y: [int]bool :: Subset(X, Y) ==> Size(X) < Size(Y) || X == Y);

////////////////////////////////////////////////////////////////////////////////

function {:inline} Invariant(NumFreeAtOrAfter: [int]int, AllocatingAtOrAfter: [int][X]bool, Free: [int]bool, freeSpace: int) : (bool)
{
    Size(AllocatingAtOrAfter[memLo]) + freeSpace == NumFreeAtOrAfter[memLo] &&
    (forall u: int :: Size(AllocatingAtOrAfter[u]) <= NumFreeAtOrAfter[u]) &&
    0 <= freeSpace &&
    (forall u: int, v: int :: memAddr(u) && memAddr(v) && u <= v ==> Subset(AllocatingAtOrAfter[v], AllocatingAtOrAfter[u])) &&
    (forall u: int :: memAddr(u) || NumFreeAtOrAfter[u] == 0) &&
    (forall u: int :: {memAddr(u)} memAddr(u) ==> NumFreeAtOrAfter[u] == (NumFreeAtOrAfter[u+1] + (if Free[u] then 1 else 0)))
}

procedure {:yield_invariant} {:layer 1} YieldAlloc({:linear "tid"} tid:int, i: int);
requires mutatorAddr(tid);
requires Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
requires (forall u: int :: AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= i);
// potential trigger: {AllocatingAtOrAfter[u][tid]}

procedure {:yield_invariant} {:layer 1} YieldCollect({:linear "tid"} tid: X);
requires tid == GcTid;
requires Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);

////////////////////////////////////////////////////////////////////////////////

procedure {:yields} {:layer 1}
{:yield_requires "YieldAlloc", tid, 0}
{:yield_ensures  "YieldAlloc", tid, 0}
Alloc({:linear "tid"} tid: X)
{
    var i: int;
    var spaceFound: bool;

    assert {:layer 1} memAddr(memLo) ==> (forall v: int :: memAddr(v) && memLo <= v ==> Subset(AllocatingAtOrAfter[v], AllocatingAtOrAfter[memLo]));
    assert {:layer 1} memAddr(memLo) ==> (forall v: int :: memAddr(v) && v <= memLo ==> Subset(AllocatingAtOrAfter[memLo], AllocatingAtOrAfter[v]));

    call DecrementFreeSpace(tid);
    i := memLo;

    while (i < memHi)
    invariant {:layer 1}{:yields}{:yield_loop "YieldAlloc", tid, i} true;
    invariant {:layer 1} memAddr(i);
    {
        assert {:layer 1} memAddr(i+1) ==> (forall v: int :: memAddr(v) && i+1 <= v ==> Subset(AllocatingAtOrAfter[v], AllocatingAtOrAfter[i+1]));
        assert {:layer 1} memAddr(i+1) ==> (forall v: int :: memAddr(v) && v <= i+1 ==> Subset(AllocatingAtOrAfter[i+1], AllocatingAtOrAfter[v]));

        call spaceFound := AllocIfPtrFree(tid, i);

        if (spaceFound)
        {
            return;
        }
        else
        {
            i := i + 1;
        }
    }

    assert {:layer 1} false;
}

procedure {:yields} {:layer 1}
{:yield_requires "YieldCollect", tid}
{:yield_ensures  "YieldCollect", tid}
Collect({:linear "tid"} tid: X)
{
    while (*)
    invariant {:layer 1}{:yields}{:yield_loop "YieldCollect", tid} true;
    {
        call Reclaim(tid);
    }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 1} AtomicDecrementFreeSpace({:linear "tid"} tid: X)
modifies freeSpace, AllocatingAtOrAfter;
{
    assert AllocatingAtOrAfter[memLo] == AllocatingAtOrAfter[memLo][tid := false];
    assume 0 < freeSpace;
    freeSpace := freeSpace - 1;
    AllocatingAtOrAfter[memLo][tid] := true;
}

procedure {:atomic} {:layer 1} AtomicAllocIfPtrFree({:linear "tid"} tid:int, ptr:int) returns (spaceFound:bool)
modifies Free, NumFreeAtOrAfter, AllocatingAtOrAfter;
{
    assert memAddr(ptr);
    assert Free[ptr] || memAddr(ptr + 1);
    assert (forall u: int :: AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= ptr);
    spaceFound := Free[ptr];
    if (spaceFound)
    {
        Free[ptr] := false;
        NumFreeAtOrAfter := (lambda u: int :: NumFreeAtOrAfter[u] - (if memLo <= u && u <= ptr then 1 else 0));
        AllocatingAtOrAfter := (lambda u: int :: AllocatingAtOrAfter[u][tid := false]);
    }
    else
    {
        AllocatingAtOrAfter[ptr+1][tid] := true;
    }
}

procedure {:atomic} {:layer 1} AtomicReclaim({:linear "tid"} tid:int)
modifies freeSpace, Free, NumFreeAtOrAfter;
{
    var ptr: int;
    assume memAddr(ptr) && !Free[ptr];
    freeSpace := freeSpace + 1;
    Free[ptr] := true;
    NumFreeAtOrAfter := (lambda u: int :: NumFreeAtOrAfter[u] + (if memLo <= u && u <= ptr then 1 else 0));
}

procedure {:yields} {:layer 0} {:refines "AtomicDecrementFreeSpace"} DecrementFreeSpace({:linear "tid"} tid: X);
procedure {:yields} {:layer 0} {:refines "AtomicAllocIfPtrFree"} AllocIfPtrFree({:linear "tid"} tid:int, ptr:int) returns (spaceFound:bool);
procedure {:yields} {:layer 0} {:refines "AtomicReclaim"} Reclaim({:linear "tid"} tid:int);
