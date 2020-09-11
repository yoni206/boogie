// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:builtin "(Seq Int)"} IntSeq;
function {:builtin "(as seq.empty (Seq Int))"} EmptyIntSeq(): IntSeq;
function {:builtin "seq.len"} IntSeqLen(s: IntSeq): int;
function {:builtin "seq.++"} IntSeqConcat(s1: IntSeq, s2:IntSeq): IntSeq;
function {:builtin "seq.unit"} IntSeqUnit(i: int): IntSeq;
function {:builtin "seq.nth"} IntSeqNth(s: IntSeq, i: int): int;
function {:builtin "seq.extract"} IntSeqExtract(s: IntSeq, pos: int, len: int): IntSeq;

function {:inline} IntSeqUpdate(s: IntSeq, i: int, v: int): IntSeq {
  if (0 <= i && i < IntSeqLen(s))
  then
    (var s1, s2 := IntSeqExtract(s, 0, i), IntSeqExtract(s, i+1, IntSeqLen(s)-(i+1));
     IntSeqConcat(IntSeqConcat(s1, IntSeqUnit(v)), s2))
  else
    s
}

function {:inline} IntSeqAppend(s:IntSeq, v: int): IntSeq {
  IntSeqConcat(s, IntSeqUnit(v))
}

/*
procedure test()
{
  var s: IntSeq;

  s := IntSeqConcat(EmptyIntSeq(), IntSeqUnit(0));
  s := IntSeqConcat(s, IntSeqUnit(1));
  s := IntSeqConcat(s, IntSeqUnit(2));
  assert IntSeqLen(s) == 3;
  assert IntSeqExtract(s, 1, 2) == IntSeqConcat(IntSeqUnit(1), IntSeqUnit(2));
  assert IntSeqNth(s, 1) == 1;
}

procedure lookup(s: IntSeq, x: int) returns (b: bool)
ensures b == (exists i: int :: 0 <= i && i < IntSeqLen(s) && x == IntSeqNth(s, i));
{
  var i: int;

  b := false;
  i := 0;
  while (i < IntSeqLen(s))
  invariant (forall u: int :: 0 <= u && u < i ==> x != IntSeqNth(s, u));
  invariant 0 <= i;
  {
    if (IntSeqNth(s, i) == x) {
      b := true;
      return;
    }
    i := i + 1;
  }
}
*/

function foo(s: IntSeq, x: int):int;

procedure test1(s: IntSeq, x: int)
requires 0 <= x && x < IntSeqLen(s);
requires (forall i: int :: 0 <= i && i < IntSeqLen(s) ==> IntSeqNth(s, i) == 0);
ensures IntSeqNth(s, x) == 0;
{

}

procedure test2(s: IntSeq, x: int, y: int)
requires 0 <= x && x <= y && y < IntSeqLen(s);
requires (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> IntSeqNth(s, i) <= IntSeqNth(s, j));
ensures IntSeqNth(s, x) <= IntSeqNth(s, y);
{

}

/*
procedure sorted_insert(s: IntSeq, x: int) returns (s': IntSeq)
requires (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> IntSeqNth(s, i) <= IntSeqNth(s, j));
ensures (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> IntSeqNth(s, i) <= IntSeqNth(s, j));
{
  var pos: int;
  var val: int;

  pos := 0;
  while (pos < IntSeqLen(s))
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> IntSeqNth(s, i) <= x);
  {
    if (IntSeqNth(s, pos) > x) {
      break;
    }
    pos := pos + 1;
  }

  assert (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s) ==> IntSeqNth(s, i) <= IntSeqNth(s, j)); assume false;

  val := x;
  s' := s;
  while (pos < IntSeqLen(s))
  invariant 0 <= pos;
  invariant (forall i, j: int :: 0 <= i && i <= j && j < IntSeqLen(s') ==> IntSeqNth(s', i) <= IntSeqNth(s', j));
  {
    s', val := IntSeqUpdate(s', pos, val), IntSeqNth(s', pos); // swap s'[pos] and val
    pos := pos + 1;
  }
  s' := IntSeqAppend(s', val);
}
*/
