procedure {:IS_abstraction}{:layer 2} A_StartRound'(r: Round, {:linear_in "perm"} r_lin: Round)
returns ({:pending_async "A_Join", "A_Propose"} PAs:[PA]int)
modifies pendingAsyncs;
{
  assert r == r_lin;
  assert Round(r);
  assert pendingAsyncs[StartRound_PA(r, r_lin)] > 0;

  /**************************************************************************/
  assert RoundCollector(r)[ConcludePerm(r)];         // Hint for left mover checks
  assert triggerRound(r-1);
  assert triggerNode(0);
  /**************************************************************************/

  PAs := MapAdd(JoinPAs(r), SingletonPA(Propose_PA(r, ProposePermissions(r))));

  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(StartRound_PA(r, r_lin)));
}

procedure {:IS_abstraction}{:layer 2} A_Propose'(r: Round, {:linear_in "perm"} ps: [Permission]bool)
returns ({:pending_async "A_Vote", "A_Conclude"} PAs:[PA]int)
modifies voteInfo, pendingAsyncs;
{
  var maxRound: int;
  var maxValue: Value;
  var ns: NodeSet;

  assert Round(r);
  assert pendingAsyncs[Propose_PA(r, ps)] > 0;
  assert ps == ProposePermissions(r);
  assert is#NoneVoteInfo(voteInfo[r]);

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[StartRound_PA(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' <= r ==> pendingAsyncs[Join_PA(r', n', p')] == 0);
  assert ps[ConcludePerm(r)];       // Hint for commutativity w.r.t. {Paxos, Propose}
  assert triggerRound(r);
  assert triggerRound(r-1);
  assert triggerNode(0);
  /**************************************************************************/

  if (*) {
    assume IsSubset(ns, joinedNodes[r]) && IsQuorum(ns);
    maxRound := MaxRound(r, ns, voteInfo);
    if (maxRound != 0)
    {
      maxValue := value#SomeVoteInfo(voteInfo[maxRound]);
    }
    voteInfo[r] := SomeVoteInfo(maxValue, NoNodes());
    PAs := MapAdd(VotePAs(r, maxValue), SingletonPA(Conclude_PA(r, maxValue, ConcludePerm(r))));
  } else {
    PAs := NoPAs();
  }

  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(Propose_PA(r, ps)));
}

procedure {:IS_abstraction}{:layer 2} A_Conclude'(r: Round, v: Value, {:linear_in "perm"} p: Permission)
modifies decision, pendingAsyncs;
{
  var q:NodeSet;

  assert Round(r);
  assert pendingAsyncs[Conclude_PA(r, v, p)] > 0;
  assert p == ConcludePerm(r);
  assert is#SomeVoteInfo(voteInfo[r]);
  assert value#SomeVoteInfo(voteInfo[r]) == v;

  /**************************************************************************/
  assert (forall n': Node, v': Value, p': Permission :: pendingAsyncs[Vote_PA(r, n', v', p')] == 0);
  assert triggerRound(r);
  /**************************************************************************/

  if (*) {
    assume IsSubset(q, ns#SomeVoteInfo(voteInfo[r])) && IsQuorum(q);
    decision[r] := SomeValue(v);
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(Conclude_PA(r, v, p)));
}

procedure {:IS_abstraction}{:layer 2} A_Join'(r: Round, n: Node, {:linear_in "perm"} p: Permission)
modifies joinedNodes, pendingAsyncs;
{
  assert Round(r);
  assert pendingAsyncs[Join_PA(r, n, p)] > 0;
  assert p == JoinPerm(r, n);

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[StartRound_PA(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' < r ==> pendingAsyncs[Join_PA(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' < r ==> pendingAsyncs[Propose_PA(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' < r ==> pendingAsyncs[Vote_PA(r', n', v', p')] == 0);
  assert triggerRound(r-1);
  assert triggerNode(n);
  /**************************************************************************/

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' < r);
    joinedNodes[r][n] := true;
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(Join_PA(r, n, p)));
}

procedure {:IS_abstraction}{:layer 2} A_Vote'(r: Round, n: Node, v: Value, {:linear_in "perm"} p: Permission)
modifies joinedNodes, voteInfo, pendingAsyncs;
{
  assert Round(r);
  assert p == VotePerm(r, n);
  assert pendingAsyncs[Vote_PA(r, n, v, p)] > 0;
  assert is#SomeVoteInfo(voteInfo[r]);
  assert value#SomeVoteInfo(voteInfo[r]) == v;
  assert !ns#SomeVoteInfo(voteInfo[r])[n];

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[StartRound_PA(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' <= r ==> pendingAsyncs[Join_PA(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' <= r ==> pendingAsyncs[Propose_PA(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' < r ==> pendingAsyncs[Vote_PA(r', n', v', p')] == 0);
  assert triggerRound(r-1);
  assert triggerNode(n);
  /**************************************************************************/

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' <= r);
    voteInfo[r] := SomeVoteInfo(v, ns#SomeVoteInfo(voteInfo[r])[n := true]);
    joinedNodes[r][n] := true;
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(Vote_PA(r, n, v, p)));
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
