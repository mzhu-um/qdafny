include "../libraries/src/NonlinearArithmetic/Power2.dfy"
include "../libraries/src/NonlinearArithmetic/Power.dfy"
include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
include "../libraries/src/NonlinearArithmetic/Mul.dfy"

// import opened Power
// import opened DivMod
// import opened Mul

// Binary to Natural Number Conversion 
module B2N {
  function method b2n(a : seq<nat>) : nat
    requires (forall k | 0 <= k < |a| :: a[k] == 0 || a[k] == 1)
  {
    if |a| == 0 then 0 else a[0] + 2 * b2n(a[1..])
  }


  lemma LemmaB2NAllZeros(a : seq<nat>)
    requires (forall k | 0 <= k < |a| :: a[k] == 0)
    decreases a
    ensures b2n(a) == 0
  {
  }

  lemma LemmaB2NTailingZeros(a : seq<nat>, i : nat)
    requires 0 <= i < |a|
    requires (forall k | 0 <= k < i :: a[k] == 0 || a[k] == 1)
    requires (forall k | i <= k < |a| :: a[k] == 0)
    ensures b2n(a) == b2n(a[0..i])
  {
    if (i == 0) {
      LemmaB2NAllZeros(a[i..]);
      assert b2n(a[i..]) == 0;
    } else {
      LemmaB2NTailingZeros(a[1..], i - 1);
      assert b2n(a[1..]) == b2n(a[1..][0..i-1]);
      assert (a[1..][0..i-1] == a[1..i]);
      assert b2n(a[1..]) == b2n(a[1..i]);
      assert a[0] + 2 * b2n(a[1..]) == a[0] + 2 * b2n(a[1..i]);
      assert b2n(a) == b2n(a[0..i]);
    }
  }
  
}

module QPrelude {
  import opened Power2
  import opened B2N
  datatype Mode =
    | Nor(b : seq<nat>)
    | Had(h : seq<int>)
    // c : a session
    // a session is a sequence of q registers
    // a q register in CH mode is a seq tuple representing the summation
    // fst pos in tuple is the ket, snd pos is the coef
    | CH(dof : nat, c : map<Qubits, seq<(nat, int)>>)

  lemma MinimumInQubits(s : set<Qubits>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s  ==> x.card <= y.card
  {
    var x :| x in s;
    if s == {x} {
      assert true; 
    } else {
      var s' := s - {x};
      MinimumInQubits(s');
    }
  }
    
  function DoubleCHSeq(s : seq<(nat, int)>, coef : int, add : nat) : seq<(nat, int)>
    decreases |s|
  {
    if |s| == 0 then s
    else var x := s[0];
      [(add + x.0, coef)] + DoubleCHSeq(s[1..], coef, add) 
  }

  // function method DupMap(m : map<Qubits, seq<(nat, int)>>) : map<Qubits, seq<(nat, int)>>
  //   reads m.Keys
  // {
  //   var keys := m.Keys;
  //   DupByKey(keys, m)
  // }

  // function method DupByKey(keys : set<Qubits>, m : map<Qubits, seq<(nat, int)>>) : map<Qubits, seq<(nat, int)>>
  //   decreases |keys|
  //   requires keys <= m.Keys
  //   reads keys
  // {
  //   if keys == {} then m
  //   else
  //     MinimumInQubits(keys);
  //     var k :| k in keys && forall y :: y in keys ==> k.card <= y.card;
  //     DupByKey(keys - { k }, m[k := m[k] + m[k]])
  // }

  method DupMap(m : map<Qubits, seq<(nat, int)>>) returns (m2 : map<Qubits, seq<(nat, int)>>)
    ensures m == old(m)
    ensures m.Keys == m2.Keys
    ensures forall k | k in m.Keys :: m[k] + m[k] == m2[k]
  {
    var keys := m.Keys;
    m2 := map[];
    while (keys != {})
      decreases |keys|
      invariant forall k | k in keys :: k in m.Keys
      invariant m2.Keys + keys == m.Keys
      invariant forall k | k in m2.Keys :: m[k] + m[k] == m2[k]
    {
      var k : Qubits :| k in keys;
      keys := keys - { k };
      m2 := m2[k := (m[k] + m[k])];
    }
  }

  method MergeMap(m : map<Qubits, seq<(nat, int)>>, m1 : map<Qubits, seq<(nat, int)>>) returns (m2 : map<Qubits, seq<(nat, int)>>)
    requires m.Keys == m1.Keys
    ensures m.Keys == m2.Keys
    ensures forall k | k in m.Keys :: m[k] + m1[k] == m2[k]
  {
    var keys := m.Keys;
    m2 := map[];
    while (keys != {})
      decreases |keys|
      invariant forall k | k in keys :: k in m.Keys
      invariant m2.Keys + keys == m.Keys
      invariant forall k | k in m2.Keys :: m[k] + m1[k] == m2[k]
    {
      var k : Qubits :| k in keys;
      keys := keys - { k };
      m2 := m2[k := (m[k] + m1[k])];
    }
  }


  class {:autocontracts} Qubits {
    ghost var count : nat;
    var m : Mode;
    var card : nat; 
    
    predicate Valid()
      reads this
    {
      // card > 0 &&
      this.Repr == { this } &&
      match m {
        case Nor(b) => |b| == card && forall i | 0 <= i < |b| :: b[i] == 0 || b[i] == 1
        case Had(h) => |h| == card
        case CH(dof, c) =>
          this in c && forall q | q in c :: |c[q]| == dof
      }
    }
  
    // Constructor
    // constructor EmptyCH()
    //   ensures card == 0
    //   ensures m.CH?
    //   ensures m.dof == 1;
    //   ensures m.c[0] == (0, 1);
    // {
    //   var empty := seq(1, _ => (0, 1));
    //   card := 0;
    //   m := CH(1, empty);
    // }
  
    constructor PrepareAny(n : nat, s : seq<nat>)
      requires |s| == n
      requires forall k | 0 <= k < n :: s[k] == 0 || s[k] == 1
      // ensures Wf()
      ensures m.Nor?
      ensures card == n
      ensures forall k | 0 <= k < n :: m.b[k] == s[k]
    {
      card := n;
      m := Nor(s);
    }

    // Mode Gates
    method H()
      requires m.Nor?
      ensures m.Had?
      ensures |m.h| == old(|m.b|) == card
      ensures forall i | 0 <= i < card :: old(m.b[i]) == 0 ==> m.h[i] == 1
      modifies this
  
    method X()
      requires m.Nor?
      ensures card == old(card)
      ensures m.Nor?
      ensures forall k | 0 <= k < |m.b| :: old(m.b[k] == 1) ==> m.b[k] == 0
      ensures forall k | 0 <= k < |m.b| :: old(m.b[k] == 0) ==> m.b[k] == 1
      modifies this
    // {
    //   m := Nor(seq(card, i reads this requires forall e | e in m.b :: e == 0 || e == 1 => 1 - m.b[i]));
    // }
  
    method XSlice(l : nat, r : nat)
      requires m.Nor?
      requires 0 <= l < r <= card
      ensures card == old(card)
      ensures m.Nor?
      ensures forall k | 0 <= k < l :: m.b[k] == old(m.b[k])
      ensures forall k | l <= k < r :: old(m.b[k] == 0) ==> m.b[k] == 1
      ensures forall k | l <= k < r :: old(m.b[k] == 1) ==> m.b[k] == 0
      ensures forall k | r <= k < card :: m.b[k] == old(m.b[k])
      modifies this
      
    // TODO : I may need to customize the trigger to make the automation smarter
    method HSplit(n : nat) returns (q : Qubits)
      requires m.Had? && 1 <= n <= card
      ensures m.Had?
      ensures fresh(q)
      ensures q.Valid() && q.m.Had? && q.card == n && q.card + card == old(card)
      ensures forall i | 0 <= i < n :: q.m.h[i] == old(m.h[i])
      ensures forall i | 0 <= i < card :: m.h[i] == old(m.h[n + i])
      modifies this
  

    // Note that both [Replicate] and [Classical] don't change other qubits in
    // the session. That's important as inconsistency could be introduced
    // without this restriction.
    method Classical(s : seq<nat>)
      requires m.CH? && this in m.c && m.dof == |s|
      ensures m.CH? && this in m.c && m.dof == |s|
      ensures m.c.Keys == old(m.c.Keys)
      ensures forall q | q in m.c.Keys :: q.card == old(q.card)
      // only the state of the current is changed, dof is unchanged
      ensures forall i | 0 <= i < m.dof :: s[i] == m.c[this][i].0
      ensures forall i | 0 <= i < m.dof :: old(m.c[this][i].1) == m.c[this][i].1
      // mutation on current qubit shouldn't affect other qubits
      ensures forall q | q in (m.c.Keys - { this }) :: q.m == old(q.m)
      // No mutation is done on the "state" of other qubits in the session
      ensures forall q | q in (m.c.Keys - { this }) :: m.c[q] == old(m.c[q])
      // everything is still valid
      ensures forall k | k in m.c.Keys :: k.Valid()
      modifies this, this.m.c.Keys
  
    method Replicate(s : Qubits)
      requires Valid() && m.CH?
      requires this in m.c && this != s
      // ensures fresh(s) && s.Valid() && s != this
      ensures unchanged(this)
      ensures s.m.CH?
      ensures s.Valid()
      ensures s.m.c == (this.m.c - { this })[s := this.m.c[this]]
      ensures s.card == this.card && s.m.dof == this.m.dof
      ensures this.m.c[this] == s.m.c[s]
      modifies s, s.Repr
    {
      s.card := card;
      var ss := this.m.c - { this };
      ss := ss[s := this.m.c[this]];
      s.m := CH(m.dof, ss);
      s.Repr := { s };
    }

    method SyncWith(x : Qubits)
      requires Valid() && m.CH?
      requires this in m.c && x !in m.c
      // consistent DOF
      ensures Valid() && x.Valid() && m.CH? && x.m.CH? && card == old(card)
      ensures x.m.dof == m.dof == old(m.dof) 
      // in the same session
      ensures x.m.c == m.c
      // only add [x] to the session
      ensures m.c.Keys == old(m.c.Keys) + { x }
      // initialize [x]
      ensures x.card == 0
      ensures m.c[x] == seq<(nat, int)>(m.dof, _ => (0, 1))
      // the rest are still
      ensures forall k | k in old(m.c.Keys) :: m.c[k] == old(m.c[k])
      modifies x, x.Repr, this, m.c.Keys
      
  method MoveTo(q : Qubits)
    requires Valid() && q.Valid()
    requires m.Had? || m.Nor?
    requires q.m.Nor? && q.card == 0
    ensures Valid() && q.Valid()
    ensures q.m == old(m) && q.card == old(card)
    ensures m == Nor(seq<nat>(0, _ => 0)) && card == 0
    modifies this, q


  // [MergeWith] and [MergeWithIn] are the only two places we mutate other
  // variables in the session
  method MergeWith(q : Qubits, x : Qubits)
      requires q.Valid() && x.Valid()
      requires x.m.Had? && m.CH? && q.m.CH? && card == q.card && m.dof == q.m.dof && x.card == 1
      requires m.c.Keys - { this } == q.m.c.Keys - { q }
      requires this in m.c.Keys && q in q.m.c.Keys && x !in m.c.Keys && x !in q.m.c.Keys 
      ensures q == old(q)
      ensures Valid() && m.CH? && forall p | p in m.c.Keys :: p.Valid()
      ensures m.CH? && x.m.CH? && x.m.dof == m.dof == 2 * old(m.dof)
      ensures m.c.Keys == old(m.c.Keys) + { x } == x.m.c.Keys
      // cardinality check
      ensures forall p | p in m.c.Keys :: p.card == old(p.card)
      // include [x] into entanglement set
      // merge [this] with [q]
      ensures m.c[this] == old(m.c[this]) + old(q.m.c[q])
      // merge the rest
      ensures forall p | p in old(m.c.Keys) - { this } :: m.c[p] == old(m.c[p] + q.m.c[p])
      // session equivalence
      ensures forall p | p in m.c.Keys :: p.m == m
      // construct [x]
      ensures forall i | 0 <= i < old(m.dof) :: x.m.c[x][i] == (0, 1)
      ensures forall i | old(m.dof) <= i < m.dof :: x.m.c[x][i] == (1, old(x.m.h[0]))
      modifies this, this.m.c.Keys, x
    {
      // concat [this] with [q]
      var s : seq<(nat, int)> := m.c[this] + q.m.c[q];
      // prepare the states of [x]
      var xx := x.m.h[0];
      var xs1 := seq<(nat, int)>(m.dof, _ => (0, 1));
      var xs2 := seq<(nat, int)>(m.dof, _ => (1, xx));
      var xs := xs1 + xs2;
      // duplicate states of unchanged states
      var dupc := MergeMap(m.c - {this}, q.m.c - {q});
      // add both [this] and [x] back
      var dup2 := dupc[this := s][x := xs];
      var odof := m.dof;
      var m' := CH(odof * 2, dup2);
      var keys := dup2.Keys;
      var keys' := {};
      assert Repr == { this };
      while (keys != {})
        decreases |keys|
        invariant keys' + keys == dup2.Keys
        invariant forall k | k in keys' :: m' == k.m && k.Valid() && k.Repr == { k }
        invariant forall k | k in dup2.Keys :: k.card == old(k.card)
      {
        var k : Qubits :| k in keys;
        k.m := m';
        k.Repr := { k };
        keys := keys - { k };
        keys' := keys' + { k };
      }
      assert Repr == { this };
      assert this.Valid() && fresh(Repr - old(Repr));
    }


    // Merge [this] with the register [q] and add [x] into the register [y]
    method MergeWithIn(q : Qubits, x : Qubits, y : Qubits)
      // valid boilerplate
      requires q.Valid() && x.Valid() && y.Valid()
      requires x.m.Had? && m.CH? && q.m.CH? && y.m.CH?
      requires card == q.card && m.dof == q.m.dof == y.m.dof && x.card == 1

      // keys prerequisites
      requires this in m.c.Keys && q in q.m.c.Keys && y in q.m.c.Keys
      requires m.c.Keys - { this } == q.m.c.Keys - { q }
      requires y.m.c.Keys == m.c.Keys
      requires forall p | p in this.m.c.Keys :: p.Valid()

      // DOF enforcement
      ensures m.CH? && y.m.CH? && m.dof == y.m.dof == 2 * old(m.dof)
      // key invariant
      ensures m.c.Keys == old(m.c.Keys)
      // cardinality check
      ensures forall p | p in m.c.Keys - { y } :: p.card == old(p.card)
      // tmp object invariant
      ensures q == old(q) && x == old(x)
      ensures Valid() && m.CH? && forall p | p in m.c.Keys :: p.Valid()
      // merge [x] with [y]
      ensures y.card == old(y.card) + 1
      ensures m.c[y] == old(m.c[y]) + DoubleCHSeq(old(m.c[y]), old(x.m.h[0]), old(m.dof))
      // merge [this] with [q]
      ensures m.c[this] == old(m.c[this]) + old(q.m.c[q])
      // merge the rest
      ensures forall p | p in old(m.c.Keys) - { this } :: m.c[p] == old(m.c[p] + q.m.c[p])
      // session equivalence
      ensures forall p | p in m.c.Keys :: p.m == m
      modifies this, this.m.c.Keys, x, y


    method Merge(q : Qubits)
      requires q.Valid() && q != this
      requires m.CH? && q.m.CH? && card == q.card && m.dof == q.m.dof
      ensures unchanged(q)
      ensures m.CH? && m.dof == 2 * old(m.dof) && card == old(card)
      ensures Valid()
      ensures m.c.Keys == old(m.c.Keys)
      ensures m.c[this] == old(m.c[this]) + old(q.m.c[q])
      modifies this


    // Cast Operator
    method NorToCH()
      requires m.Nor?
      ensures card == old(card)
      ensures m.CH? && m.dof == 1 && card == old(card) && Valid()
      ensures |m.c| == 1 && m.c.Keys == { this }
      ensures m.c[this][0] == (b2n(old(m.b)), 1)
      modifies this
  
    // method SplitPlus(n : nat) returns (q : Qubits)
    //   requires m.Had? 
    //   requires 0 < n <= card
    //   ensures q.m.Had? && q.card == n
    //   ensures m.Had?
    //   ensures card == (old(card) - n) && fresh(q)
    //   ensures q.Valid()
    //   ensures forall k | 0 <= k < n :: q.m.h[k] == old(m.h[k])
    //   ensures forall k | 0 <= k < |m.h| :: m.h[k] == old(m.h[k + n])
    //   modifies this
  
    // Apply H to switch Qubits to Hadamard Basis
    // method PlusRetCH()
    //   requires m.Had?
    //   requires forall i | 0 <= i < card :: m.h[i] == 1
    //   ensures m.CH?
    //   ensures m.dof == Pow2(card)
    //   ensures forall i | 0 <= i < m.dof :: m.c[i] == (i, 1) // amounts to say it's a sum
    //   modifies this
    // {
    //   var dof := Pow2(card);
    //   var c := seq(dof, i => (i, 1));
    //   assert (forall i | 0 <= i < dof :: c[i] == (i, 1));
    //   m := CH(dof, c);
    //   assert (forall i | 0 <= i < m.dof :: m.c[i] == (i, 1));
    // }
  
  
    // {
    //   var j := b2n(m.b);
    //   var t := seq(1, _ => (j, 1));
    //   m := CH(1, t);
    // }
  
    // method CatPlusCH(q : Qubits)
    //   requires m.CH? && q.m.Had?
    //   requires forall i | 0 <= i < m.dof :: m.c[i] == (i, 1)
    //   requires q.card == 1
    //   requires q.Valid()
    //   requires q.m.h[0] == 1
    //   requires m.dof == Pow2(card)
    //   modifies this
    //   ensures m.CH? && m.dof == 2 * old(m.dof)
    //   ensures card == old(card) + 1
    //   ensures forall i | 0 <= i < m.dof :: m.c[i] == (i, 1)
    // {
    //   reveal Pow2();
    //   var offset : nat := Pow2(card);
    //   var newH : seq<(nat, int)> :=
    //     seq(offset, i => m.c[i]) +
    //     seq(offset, i => (offset + m.c[i].0, 1));
    //   m := CH(2 * offset, newH);
    //   card := card + 1;
    // }
    
    // predicate PSumMod(l : nat, r : nat, a : nat, N : nat)
    //   reads this, Repr
    //   requires N > 0
    //   requires m.CH?
    //   requires 0 <= l < r <= m.dof
    // {
    //   forall k | l <= k < r :: (k, Pow(a, k) % N) == m.c[k]
    // }
  
    // predicate Saturated()
    //   requires m.CH?
    //   reads this, Repr
    // {
    //   m.dof == Pow2(card) && forall i | 0 <= i < |m.c| :: m.c[i] == (i, 1)
    // }
  }
}
