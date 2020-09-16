// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:builtin "(Seq Int)"} IntSeq;
function {:builtin "(as seq.empty (Seq Int))"} EmptyIntSeq(): IntSeq;
function {:builtin "seq.len"} IntSeqLen(s: IntSeq): int;
function {:builtin "seq.++"} IntSeqConcat(s1: IntSeq, s2:IntSeq): IntSeq;
function {:builtin "seq.unit"} IntSeqUnit(i: int): IntSeq;
function {:builtin "seq.nth"} IntSeqNth(s: IntSeq, i: int): int;
function {:builtin "seq.extract"} IntSeqExtract(s: IntSeq, pos: int, len: int): IntSeq;
function Nth(s: IntSeq, i: int): int
{
  IntSeqNth(s, i)
}
function IntSeqUpdate(s: IntSeq, i: int, v: int): IntSeq;
axiom (forall s: IntSeq, i: int, v: int :: 0 <= i && i < IntSeqLen(s) ==>
        (var s' := IntSeqUpdate(s, i, v);
          IntSeqLen(s') == IntSeqLen(s) &&
          Nth(s', i) == v &&
          (forall j: int :: 0 <= j && i < IntSeqLen(s) && i != j ==> Nth(s', j) == Nth(s, j))
        )
      );
/*
function IntSeqUpdate(s: IntSeq, i: int, v: int): IntSeq {
  if (0 <= i && i < IntSeqLen(s))
  then
    (var s1, s2 := IntSeqExtract(s, 0, i), IntSeqExtract(s, i+1, IntSeqLen(s)-(i+1));
     IntSeqConcat(IntSeqConcat(s1, IntSeqUnit(v)), s2))
  else
    s
}
*/
function {:inline} IntSeqAppend(s:IntSeq, v: int): IntSeq {
  IntSeqConcat(s, IntSeqUnit(v))
}

procedure test0()
{
  var s: IntSeq;

  s := IntSeqConcat(EmptyIntSeq(), IntSeqUnit(0));
  s := IntSeqConcat(s, IntSeqUnit(1));
  s := IntSeqConcat(s, IntSeqUnit(2));
  assert IntSeqLen(s) == 3;
  assert IntSeqExtract(s, 1, 2) == IntSeqConcat(IntSeqUnit(1), IntSeqUnit(2));
  assert Nth(s, 1) == 1;
  s := IntSeqUpdate(s, 1, 3);
  assert Nth(s, 0) == 0;
  assert Nth(s, 1) == 3;
  assert IntSeqLen(s) == 3;
}

procedure test1(s: IntSeq, x: int)
requires 0 <= x && x < IntSeqLen(s);
requires (forall i: int :: 0 <= i && i < IntSeqLen(s) ==> Nth(s, i) == 0);
ensures Nth(s, x) == 0;
{

}

procedure test2(s: IntSeq, x: int, y: int)
requires 0 <= x && x <= y && y < IntSeqLen(s);
requires (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> Nth(s, i) <= Nth(s, j));
ensures Nth(s, x) <= Nth(s, y);
{

}

procedure lookup(s: IntSeq, x: int) returns (b: bool)
ensures b == (exists i: int :: 0 <= i && i < IntSeqLen(s) && x == Nth(s, i));
{
  var i: int;

  b := false;
  i := 0;
  while (i < IntSeqLen(s))
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

procedure sorted_update(s: IntSeq, pos: int, val: int) returns (s': IntSeq)
requires (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> Nth(s, i) <= Nth(s, j));
requires 0 <= pos && pos < IntSeqLen(s);
requires (forall i: int:: 0 <= i && i < pos ==> Nth(s, i) <= val);
requires (forall i: int :: pos < i && i < IntSeqLen(s) ==> val <= Nth(s, i));
ensures (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s') ==> Nth(s', i) <= Nth(s', j));
{
  s' := IntSeqUpdate(s, pos, val);
}

procedure sorted_insert(s: IntSeq, x: int) returns (s': IntSeq)
requires (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> Nth(s, i) <= Nth(s, j));
ensures (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> Nth(s, i) <= Nth(s, j));
{
  var pos: int;
  var val: int;

  pos := 0;
  while (pos < IntSeqLen(s) && Nth(s, pos) <= x)
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> Nth(s, i) <= x);
  {
    pos := pos + 1;
  }

  val := x;
  s' := s;
  while (pos < IntSeqLen(s'))
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> Nth(s', i) <= val);
  invariant (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s') ==> Nth(s', i) <= Nth(s', j));
  invariant (forall i: int :: pos <= i && i < IntSeqLen(s') ==> val <= Nth(s', i));
  {
    s', val := IntSeqUpdate(s', pos, val), Nth(s', pos); // swap s'[pos] and val
    pos := pos + 1;
  }
  s' := IntSeqAppend(s', val);
}
