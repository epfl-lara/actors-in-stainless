import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps

import actors._

import LeaderElection._
import BoundedQuantifiers._

object LeaderElectionInvariant {

  def noDuplicate[T](l: List[T]): Boolean = {
    decreases(l.length)
    l match {
      case Nil() => true
      case Cons(x, xs) => !xs.contains(x) && noDuplicate(xs)
    }
  }

  @ghost
  def validBehavior(b: Behavior): Boolean =
    b.isInstanceOf[NonParticipant] ||
    b.isInstanceOf[Participant] ||
    b.isInstanceOf[KnowLeader]

  @ghost
  def validBehavior(behaviors: CMap[ActorRef, Behavior], ref: ActorRef): Boolean = validBehavior(behaviors(ref))

  @ghost
  def validBehaviors(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef]): Boolean = {
    refs.forall(r => validBehavior(behaviors, r))
  }

  @ghost
  def getNext(b: Behavior): ActorRef = {
    require(validBehavior(b))
    b match {
      case NonParticipant(r, _) => r
      case Participant(r, _) => r
      case KnowLeader(r, _, _) => r
    }
  }

  @ghost
  def getNext(behaviors: CMap[ActorRef, Behavior], ref: ActorRef): ActorRef = {
    require(validBehavior(behaviors(ref)))
    getNext(behaviors(ref))
  }

  @ghost
  def pointsTo(behaviors: CMap[ActorRef, Behavior], r1: ActorRef, r2: ActorRef) = {
    validBehavior(behaviors(r1)) &&
    getNext(behaviors, r1) == r2
  }

  @ghost
  def pointsToNext(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef], i: BigInt) = {
    require(!refs.isEmpty)

    0 <= i &&
    i < refs.length &&
    pointsTo(behaviors, refs(i), refs(increment(i, refs.length)))
  }

  @ghost
  def isRing(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef]) = {
    !refs.isEmpty &&
    intForall(refs.length, pointsToNext(behaviors, refs, _))
  }

  @ghost
  def samePointer(b1: Behavior, b2: Behavior) = {
    validBehavior(b1) &&
    validBehavior(b2) &&
    getNext(b1) == getNext(b2)
  }

  @ghost
  def getUID(b: Behavior): BigInt = {
    require(validBehavior(b))
    b match {
      case NonParticipant(_, uid) => uid
      case Participant(_, uid) => uid
      case KnowLeader(_, _, uid) => uid
    }
  }

  @ghost
  def getUID(behaviors: CMap[ActorRef, Behavior], r: ActorRef): BigInt = {
    require(validBehavior(behaviors, r))
    getUID(behaviors(r))
  }

  @ghost
  def sameUID(b1: Behavior, b2: Behavior) = {
    validBehavior(b1) &&
    validBehavior(b2) &&
    getUID(b1) == getUID(b2)
  }

  @opaque
  def forallContains[T](l: List[T], p: T => Boolean, x: T): Unit = {
    require(l.forall(p) && l.contains(x))
    decreases(l.length)

    if (!l.isEmpty && l.tail.contains(x))
      forallContains(l.tail, p, x)

  } ensuring(_ => p(x))

  @ghost
  def maxUID(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef]): (ActorRef, BigInt) = {
    require(!refs.isEmpty && validBehaviors(behaviors, refs))
    decreases(refs.length)

    val Cons(r, rs) = refs
    val uid = getUID(behaviors,r)
    if (rs.isEmpty) (r, uid)
    else {
      val (rTail, maxTail) = maxUID(behaviors, rs)
      if (maxTail >= uid) (rTail, maxTail)
      else (r, uid)
    }
  } ensuring { res =>
    val (r, uid) = res
    refs.contains(r) && {
      forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r)
      getUID(behaviors, r) == uid
    }
  }

  @opaque @ghost
  def validBehaviorGet(
    refs: List[ActorRef],
    behaviors: CMap[ActorRef, Behavior],
    i: BigInt
  ): Unit = {
    require(0 <= i && i < refs.length && validBehaviors(behaviors, refs))
    decreases(i)

    if (i > 0)
      validBehaviorGet(refs.tail, behaviors, i-1)

  } ensuring(_ => validBehavior(behaviors, refs(i)))

  def inBetween(n: BigInt, i: BigInt, j: BigInt, k: BigInt) = {
    0 <= i && i < n &&
    0 <= j && j < n &&
    0 <= k && k < n && (
      (i <= k && k <= j) ||
      (i > j && k >= i) ||
      (i > j && k <= j)
      )
  }

  // returns the index of the greater UID between from and to, and its UID
  @ghost
  def partialMaxUID(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    from: BigInt,
    to: BigInt
  ): (BigInt, BigInt) = {
    require(
      0 <= from && from < refs.length &&
      0 <= to && to < refs.length &&
      !refs.isEmpty && validBehaviors(behaviors, refs)
    )
    decreases(if (from <= to) to - from else to + refs.length - from)

    validBehaviorGet(refs, behaviors, to)

    val uid = getUID(behaviors, refs(to))
    if (from == to) (from, uid)
    else {
      val (i1, uid1) = partialMaxUID(behaviors, refs, from, decrement(to, refs.length))
      if (uid1 >= uid) (i1, uid1)
      else (to, uid)
    }
  } ensuring(res => {
    val (iMax, v) = res
    inBetween(refs.length, from, to, iMax) &&
    validBehavior(behaviors, refs(iMax)) &&
    getUID(behaviors, refs(iMax)) == v
  })

  @opaque @ghost
  def indexOfInRange[T](l: List[T], t: T): Unit = {
    require(l.contains(t))
    decreases(l.length)

    if (l.head != t)
      indexOfInRange(l.tail, t)

  } ensuring(_ => 0 <= l.indexOf(t) && l.indexOf(t) < l.length)

  @ghost
  def knowTrueLeader(behaviors: CMap[ActorRef,Behavior], refs: List[ActorRef], b: Behavior): Boolean = {
    require(!refs.isEmpty && validBehaviors(behaviors, refs))
    b match {
      case KnowLeader(_, leader, _) => leader == maxUID(behaviors, refs)._2
      case _ => true
    }
  }

  @ghost
  def knowTrueLeader(behaviors: CMap[ActorRef,Behavior], refs: List[ActorRef], r: ActorRef): Boolean = {
    require(!refs.isEmpty && validBehaviors(behaviors, refs))
    knowTrueLeader(behaviors, refs, behaviors(r))
  }

  @ghost
  def knowTrueLeader(behaviors: CMap[ActorRef,Behavior], refs: List[ActorRef]): Boolean = {
    require(!refs.isEmpty && validBehaviors(behaviors, refs))
    refs.forall(knowTrueLeader(behaviors, refs, _))
  }

  @ghost
  def electingTrueLeader(
    behaviors: CMap[ActorRef,Behavior],
    refs: List[ActorRef],
    iFrom: BigInt,
    m: Msg
  ): Boolean =
  {
    require(
      0 <= iFrom && iFrom < refs.length &&
      validBehaviors(behaviors, refs)
    )
    m match {
      case Elected(leader) =>
        leader == maxUID(behaviors, refs)._2
      case Election(startingActor, uid) =>
        refs.contains(startingActor) && {
          indexOfInRange(refs, startingActor)
          uid == partialMaxUID(behaviors, refs, refs.indexOf(startingActor), iFrom)._2 ||
          uid == maxUID(behaviors, refs)._2
        }
      case _ => true
    }
  }

  @ghost
  def electingTrueLeader(
    behaviors: CMap[ActorRef,Behavior],
    refs: List[ActorRef],
    iFrom: BigInt,
    channel: List[Msg]
  ): Boolean =
  {
    require(
      0 <= iFrom && iFrom < refs.length &&
      validBehaviors(behaviors, refs)
    )
    channel.forall(electingTrueLeader(behaviors, refs, iFrom, _))
  }

  @opaque @ghost
  def getContains[T](l: List[T], i: BigInt): Unit = {
    require(0 <= i && i < l.length)
    decreases(l.length)

    if (i > 0)
      getContains(l.tail, i-1)

  } ensuring(_ => l.contains(l(i)))

  @ghost
  def electingTrueLeader(
    behaviors: CMap[ActorRef,Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    i: BigInt
  ): Boolean =
  {
    require(validBehaviors(behaviors, refs))

    0 <= i &&
    i < refs.length &&
    electingTrueLeader(behaviors, refs, i, inboxes((refs(i), refs(increment(i, refs.length)))))
  }

  @ghost
  def electingTrueLeader(
    behaviors: CMap[ActorRef,Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef]
  ): Boolean = {
    require(!refs.isEmpty && validBehaviors(behaviors, refs))
    intForall(refs.length, electingTrueLeader(behaviors, inboxes, refs, _))
  }

  @ghost
  def nonParticipantNotInMessages(
    behaviors: CMap[ActorRef,Behavior],
    m: Msg,
    r: ActorRef
  ): Boolean = {
    ((behaviors(r), m) match {
      case (NonParticipant(_,_), Election(startingActor, _)) =>
        startingActor != r
      case _ => true
    })
  }

  @ghost
  def nonParticipantNotInMessages(
    behaviors: CMap[ActorRef,Behavior],
    refs: List[ActorRef],
    m: Msg
  ): Boolean = {
    refs.forall(nonParticipantNotInMessages(behaviors, m, _))
  }

  @ghost
  def nonParticipantNotInMessages(
    behaviors: CMap[ActorRef,Behavior],
    refs: List[ActorRef],
    channel: List[Msg]
  ): Boolean = {
    channel.forall(nonParticipantNotInMessages(behaviors, refs, _))
  }

  @ghost
  def nonParticipantNotInMessages(
    behaviors: CMap[ActorRef,Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    i: BigInt
  ): Boolean = {
    0 <= i && i < refs.length && {
      nonParticipantNotInMessages(behaviors, refs, inboxes((refs(i), refs(increment(i, refs.length)))))
    }
  }

  @ghost
  def nonParticipantNotInMessages(
    behaviors: CMap[ActorRef,Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef]
  ): Boolean = {
    intForall(refs.length, nonParticipantNotInMessages(behaviors, inboxes, refs, _))
  }

  @ghost
  def getUIDs(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef]): List[BigInt] = {
    require(validBehaviors(behaviors, refs))
    decreases(refs.length)

    refs match {
      case Nil() => Nil()
      case Cons(r, rs) =>
        Cons(getUID(behaviors, r), getUIDs(behaviors, rs))
    }
  }

  /****************************************************************************
   * The invariant of the leader election protocol.
   *
   * The important part of the invariant is `knowTrueLeader` which states that
   * if an Actor is in a `KnowLeader(_, leader, _)` state, then `leader` is the
   * maximum UID of all participants (in `refs`).
   *
   * We assume in the invariant that all actors are already initialized, i.e.
   * they have already received their `Initialize` message.
   ****************************************************************************/

  @ghost
  def invariant(s: ActorSystem, refs: List[ActorRef]) = {
    !refs.isEmpty &&
    noDuplicate(refs) &&
    validBehaviors(s.behaviors, refs) &&
    noDuplicate(getUIDs(s.behaviors, refs)) &&
    isRing(s.behaviors, refs) &&
    nonParticipantNotInMessages(s.behaviors, s.inboxes, refs) &&
    electingTrueLeader(s.behaviors, s.inboxes, refs) &&
    knowTrueLeader(s.behaviors, refs)
  }

}
