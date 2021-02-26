// run locally: Source/BoogieDriver/bin/Debug/netcoreapp3.1/BoogieDriver Test/sequences/intseq_vector.bpl -useArrayTheory -lib -monomorphize /env:2 /proverLog:tmp_cvc4.smt2 /proverOpt:PROVER_PATH=/home/yoniz/git/CVC4_1/builds/production/bin/cvc4 /proverOpt:O:strings-exp=true /proverOpt:SOLVER=CVC4 /trace
// RUN: %boogie -useArrayTheory -lib -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//////////////////////
// type declaration //
//////////////////////
// TODO: how can I support Vec<T> like in monomorphize/vector.bpl ? 
//       something like: type {:builtin "(Seq " + T.toString() + ")"} Vec<T>; ?
type {:builtin "(Seq Int)"} Vec;

///////////////////////////////////////////
// SMT-LIB-like definitions of functions //
///////////////////////////////////////////

// empty sequence
function {:builtin "(as seq.empty (Seq Int))"} Empty(): Vec;

// Binary and Ternary concat functions
function {:builtin "seq.++"} Concat(v: Vec, w: Vec) : Vec;
function {:builtin "seq.++"} Concat3(v: Vec, w: Vec, u: Vec): Vec;

// unit
function {:builtin "seq.unit"} Unit(i: int) : Vec;

// sub-sequence (extract)
function {:builtin "seq.extract"} Extract(v: Vec, offset: int, length: int): Vec;

// length
function {:builtin "seq.len"} Len(v: Vec): int;

// contains
function {:builtin "seq.contains"} Contains(v: Vec, u: Vec): bool;

// nth
function {:builtin "seq.nth"} Nth(v: Vec, i: int): int;

////////////////////////////////////////////////////////
// Extending the theory with more definable functions //
////////////////////////////////////////////////////////

// contains_elem via contains and unit
function {:inline} ContainsElem(v: Vec, x: int): bool
{
  Contains(v, Unit(x))
}

// append (via concat and unit)
function {:inline} Append(v: Vec, x: int) : Vec 
{ 
  Concat(v, Unit(x)) 
}

// update (via concat, extract and unit)
function {:inline} Update(v: Vec, i: int, x: int): Vec
{
  Concat3(Extract(v, 0, i), Unit(x), Extract(v, i+1, Len(v) - i - 1))
}


////////////
// tests ///
////////////

procedure test0()
{
  var s: Vec;

  s := Append(Empty(), 0);
  s := Append(s, 1);
  s := Append(s, 2);
  assert Len(s) == 3;
  assert Nth(s, 1) == 1;
  s := Update(s, 1, 3);
  assert Nth(s, 0) == 0;
  assert Nth(s, 1) == 3;
  assert Len(s) == 3;
}

procedure test1(s: Vec, x: int)
requires 0 <= x && x < Len(s);
requires (forall i: int :: 0 <= i && i < Len(s) ==> Nth(s, i) == 0);
ensures Nth(s, x) == 0;
{
}

procedure test2(s: Vec, x: int, y: int)
requires 0 <= x && x <= y && y < Len(s);
requires (forall i, j: int :: 0 <= i && i <= j && j < Len(s) ==> Nth(s, i) <= Nth(s, j));
ensures Nth(s, x) <= Nth(s, y);
{
}

  procedure equality(s: Vec, s': Vec)
  requires Len(s) == Len(s');
  requires (forall i: int :: 0 <= i && i < Len(s) ==> Nth(s, i) == Nth(s', i));
  ensures s == s';
  {
  }
  
 procedure update(s: Vec, pos: int, val: int) returns (s': Vec)
 requires 0 <= pos && pos < Len(s);
 requires Nth(s, pos) == val;
 ensures s' == s;
 {
   s' := Update(s, pos, val);
 }


  procedure lookup(s: Vec, x: int) returns (b: bool)
   //  ltr ok. rtl not times out
    ensures b == ContainsElem(s, x);
  {
    var i: int;
  
    b := false;
    i := 0;
    while (i < Len(s))
    invariant (forall u: int :: 0 <= u && u < i ==> x != Nth(s, u));
    invariant 0 <= i;
    {
      if (Nth(s, i) == x) {
        b := true;
        return;
      }
      i := i + 1;
    }
  }

// 
//  procedure sorted_update(s: Vec, pos: int, val: int) returns (s': Vec)
//  requires (forall i, j: int :: 0 <= i && i <= j && j < Len(s) ==> Nth(s, i) <= Nth(s, j));
//  requires 0 <= pos && pos < Len(s);
//  requires (forall i: int:: 0 <= i && i < pos ==> Nth(s, i) <= val);
//  requires (forall i: int :: pos < i && i < Len(s) ==> val <= Nth(s, i));
//  ensures (forall i, j: int :: 0 <= i && i <= j && j < Len(s') ==> Nth(s', i) <= Nth(s', j));
//  {
//    s' := Update(s, pos, val);
//  }
// 
// procedure sorted_insert(s: Vec, x: int) returns (s': Vec)
// requires (forall i, j: int :: 0 <= i && i <= j && j < Len(s) ==> Nth(s, i) <= Nth(s, j));
// ensures (forall i, j: int :: 0 <= i && i <= j && j < Len(s') ==> Nth(s', i) <= Nth(s', j));
// {
//   var pos: int;
//   var val: int;
// 
//   pos := 0;
//   while (pos < Len(s) && Nth(s, pos) <= x)
//   invariant 0 <= pos;
//   invariant (forall i: int:: 0 <= i && i < pos ==> Nth(s, i) <= x);
//   {
//     pos := pos + 1;
//   }
// 
//   val := x;
//   s' := s;
//   while (pos < Len(s'))
//   invariant 0 <= pos;
//   invariant (forall i: int:: 0 <= i && i < pos ==> Nth(s', i) <= val);
//   invariant (forall i, j: int :: 0 <= i && i <= j && j < Len(s') ==> Nth(s', i) <= Nth(s', j));
//   invariant (forall i: int :: pos <= i && i < Len(s') ==> val <= Nth(s', i));
//   {
//     s', val := Update(s', pos, val), Nth(s', pos); // swap s'[pos] and val
//     pos := pos + 1;
//   }
//   s' := Append(s', val);
// }


///////////////////////////////////////////////
// datatypes as values -- currently skipped  //
///////////////////////////////////////////////

// // type {:datatype} Value;
// // function {:constructor} Integer(i: int): Value;
// // function {:constructor} Vector(v: Vec Value): Value;
// // 
// // procedure test3(val: Value) returns (val': Value)
// // requires is#Vector(val) && Len(v#Vector(val)) == 1 && Nth(v#Vector(val), 0) == Integer(0);
// // ensures val == val';
// // {
// //   var s: Vec Value;
// // 
// //   s := Empty();
// //   s := Append(s, Integer(0));
// //   val' := Vector(s);
// // }
// // 
// // function has_zero(val: Value): (bool)
// // {
// //   if (is#Integer(val))
// //   then val == Integer(0)
// //   else (exists i: int :: 0 <= i && i < Len(v#Vector(val)) && has_zero(Nth(v#Vector(val), i)))
// // }
// // 
// // procedure traverse(val: Value) returns (b: bool)
// // ensures b == has_zero(val);
// // {
// //   var s: Vec Value;
// //   var i: int;
// // 
// //   b := false;
// //   if (is#Integer(val)) {
// //       b := val == Integer(0);
// //       return;
// //   }
// //   s := v#Vector(val);
// //   i := 0;
// //   while (i < Len(s))
// //   invariant !b;
// //   invariant 0 <= i;
// //   invariant (forall j: int :: 0 <= j && j < i ==> !has_zero(Nth(s, j)));
// //   {
// //     call b := traverse(Nth(s, i));
// //     if (b) {
// //         return;
// //     }
// //     assert !has_zero(Nth(s, i));
// //     i := i + 1;
// //   }
// // }
