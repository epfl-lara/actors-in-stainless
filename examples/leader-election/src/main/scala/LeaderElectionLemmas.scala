import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps

import actors._

import LeaderElection._
import LeaderElectionInvariant._
import BoundedQuantifiers._

object LeaderElectionLemmas {

  @ghost @extern @opaque
  def assume(b: Boolean): Unit = {
    ??? : Unit
  } ensuring(_ => b)

  @opaque @ghost
  def appendForall[T](@induct l: List[T], p: T => Boolean, x: T) = {
    require(l.forall(p) && p(x))

  } ensuring(_ => (l :+ x).forall(p))

  @opaque @ghost
  def indexOfGet[T](l: List[T], i: BigInt): Unit = {
    require(noDuplicate(l) && 0 <= i && i < l.length)
    decreases(i)

    if (i > 0)
      indexOfGet(l.tail, i-1)

  } ensuring(_ => l.indexOf(l(i)) == i)

  @opaque @ghost
  def getIndexOf[T](l: List[T], x: T): Unit = {
    require(l.contains(x))
    decreases(l.length)

    indexOfInRange(l, x)

    if (l.tail.contains(x))
      getIndexOf(l.tail, x)

  } ensuring { _ =>
    indexOfInRange(l, x)
    l(l.indexOf(x)) == x
  }

  @opaque @ghost
  def indexOfInjective[T](l: List[T], x1: T, x2: T): Unit = {
    require(l.contains(x1) && l.contains(x2) && x1 != x2)
    decreases(l.length)

    if (!l.isEmpty && l.head != x1 && l.head != x2)
      indexOfInjective(l.tail, x1, x2)

  } ensuring(_ => l.indexOf(x1) != l.indexOf(x2))


  @opaque @ghost
  def getInjective[T](l: List[T], i: BigInt, j: BigInt): Unit = {
    require(
      noDuplicate(l) &&
      0 <= i && i < l.length &&
      0 <= j && j < l.length &&
      l(i) == l(j)
    )
    decreases(l.length)

    if (i > 0 && j > 0)
      getInjective(l.tail, i-1, j-1)

    if (i > 0)
      getContains(l.tail, i-1)

    if (j > 0)
      getContains(l.tail, j-1)

  } ensuring(_ => i == j)

  @opaque @ghost
  def incrementBetween(n: BigInt, i: BigInt, j: BigInt): Unit = {
    require(0 <= j && j < n && inBetween(n, i, j, increment(j, n)))

    ()
  } ensuring(_ => increment(j, n) == i)

  @opaque @ghost @library
  def partialMaxGreater(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    i: BigInt,
    j: BigInt,
    k: BigInt
  ): Unit = {
    require(
      validBehaviors(behaviors, refs) &&
      inBetween(refs.length, i, j, k) &&
      !refs.isEmpty
    )
    decreases(if (i <= j) j - i else refs.length - i + j)
    validBehaviorGet(refs, behaviors, k) // establish validBehavior(behaviors, refs(k))

    if (i != j && k != j)
      partialMaxGreater(behaviors, refs, i, decrement(j, refs.length), k)

  } ensuring { _ =>
    validBehaviorGet(refs, behaviors, k) // establish validBehavior(behaviors, refs(k))
    getUID(behaviors, refs(k)) <= partialMaxUID(behaviors, refs, i, j)._2
  }

  @opaque @ghost
  def maxGreater(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    r: ActorRef
  ): Unit = {
    require(
      validBehaviors(behaviors, refs) &&
      refs.contains(r)
    )
    decreases(refs.length)

    forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r) // validBehavior(behaviors, r)

    if (refs.tail.contains(r))
      maxGreater(behaviors, refs.tail, r)

  } ensuring { _ =>
    forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r)
    maxUID(behaviors, refs)._2 >= getUID(behaviors, r)
  }

  @opaque @ghost
  def sameMaxUID(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      !refs.isEmpty &&
      sameUID(behaviors(r), b) &&
      validBehaviors(behaviors, refs) &&
      validBehavior(b)
    )
    decreases(refs.length)

    validBehaviorsAfterUpdate(behaviors, refs, r, b)

    if (!refs.tail.isEmpty) {
      sameMaxUID(behaviors, refs.tail, r, b)
    }
  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    maxUID(behaviors, refs) == maxUID(behaviors.updated(r,b), refs)
  }

  @opaque @ghost @library
  def samePartialUID(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    from: BigInt,
    to: BigInt,
    r: ActorRef,
    b: Behavior
  ): Unit  = {
    require(
      0 <= from && from < refs.length &&
      0 <= to && to < refs.length &&
      validBehaviors(behaviors, refs) &&
      sameUID(behaviors(r), b) &&
      validBehavior(b)
    )
    decreases(if (from <= to) to - from else to + refs.length - from)

    validBehaviorsAfterUpdate(behaviors, refs, r, b)

    if (from != to)
      samePartialUID(behaviors, refs, from, decrement(to, refs.length), r, b)

  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    partialMaxUID(behaviors, refs, from, to) ==
      partialMaxUID(behaviors.updated(r,b), refs, from, to)
  }

  @opaque @ghost
  def pointsToNextAfterUpdate(@induct n: BigInt, behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef], r: ActorRef, b: Behavior): Unit = {
    require(n >= 0 && !refs.isEmpty && intForall(n, pointsToNext(behaviors, refs, _)) && samePointer(behaviors(r), b))

    ()
  } ensuring(_ => intForall(n, pointsToNext(behaviors.updated(r, b), refs, _)))

  @opaque @ghost
  def getUIDContained(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef], r: ActorRef): Unit = {
    require(validBehaviors(behaviors, refs) && refs.contains(r))
    decreases(refs.length)

    forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r)

    if (refs.tail.contains(r))
      getUIDContained(behaviors, refs.tail, r)

  } ensuring { _ =>
    forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r)
    getUIDs(behaviors, refs).contains(getUID(behaviors, r))
  }

  @opaque @ghost
  def getUIDInjective(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef], r1: ActorRef, r2: ActorRef): Unit = {
    require(
      validBehaviors(behaviors, refs) &&
      refs.contains(r1) &&
      refs.contains(r2) && {
        forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r1)
        forallContains(refs, (r: ActorRef) => validBehavior(behaviors, r), r2)
        getUID(behaviors, r1) == getUID(behaviors, r2) &&
        noDuplicate(getUIDs(behaviors, refs)) &&
        noDuplicate(refs)
      }
    )
    decreases(refs.length)

    if (refs.tail.contains(r1) && refs.tail.contains(r2))
      getUIDInjective(behaviors, refs.tail, r1, r2)

    if (refs.tail.contains(r1))
      getUIDContained(behaviors, refs.tail, r1)

    if (refs.tail.contains(r2))
      getUIDContained(behaviors, refs.tail, r2)

  } ensuring(_ => r1 == r2)


  /****************************************************************************
   * A few lemmas about `nonParticipantNotInMessages`
   ****************************************************************************/

  @opaque @ghost
  def nonParticipantNotInMessagesFresh(
    behaviors: CMap[ActorRef, Behavior],
    @induct refs: List[ActorRef],
    m: Msg
  ): Unit = {
    require(
      (m match {
        case Election(r, _) => !refs.contains(r)
        case _ => true
      })
    )

    ()
  } ensuring(_ =>
    nonParticipantNotInMessages(behaviors, refs, m)
  )

  @opaque @ghost
  def nonParticipantNotInMessagesUnique(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    r: ActorRef,
    m: Msg
  ): Unit = {
    require(
      refs.contains(r) &&
      noDuplicate(refs) &&
      !behaviors(r).isInstanceOf[NonParticipant] &&
      (m match {
        case Election(r2, _) => r2 == r
        case _ => true
      })
    )
    decreases(refs.length)

    if (!refs.isEmpty && refs.tail.contains(r)) {
      nonParticipantNotInMessagesUnique(behaviors, refs.tail, r, m)
      check(nonParticipantNotInMessages(behaviors, refs, m))
    } else if (!refs.isEmpty && refs.head == r) {
      assert(!refs.tail.contains(r))
      nonParticipantNotInMessagesFresh(behaviors, refs.tail, m)
      check(nonParticipantNotInMessages(behaviors, refs, m))
    }

    ()
  } ensuring(_ =>
    nonParticipantNotInMessages(behaviors, refs, m)
  )

  @opaque @ghost
  def nonParticipantNotInMessagesSameMessage(
    behaviors: CMap[ActorRef, Behavior],
    @induct refs: List[ActorRef],
    m1: Msg,
    m2: Msg
  ): Unit = {
    require(
      nonParticipantNotInMessages(behaviors, refs, m1) &&
      ((m1, m2) match {
        case (Election(r1, _), Election(r2, _)) => r1 == r2
        case (_, Election(r2, _)) => false
        case _ => true
      })
    )

    ()
  } ensuring(_ =>
    nonParticipantNotInMessages(behaviors, refs, m2)
  )

  @ghost
  def nonParticipantNotInMessagesElected(
    behaviors: CMap[ActorRef, Behavior],
    @induct refs: List[ActorRef],
    leader: BigInt
  ) = {
    ()
  } ensuring(_ => nonParticipantNotInMessages(behaviors, refs, Elected(leader)))

  /****************************************************************************
   * `uniqueUIDs` is preserved after a behavior update
   ****************************************************************************/

  @opaque @ghost
  def getUIDsAfterUpdate(
    behaviors: CMap[ActorRef, Behavior],
    @induct refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ) = {
    require(
      validBehaviors(behaviors, refs) &&
      sameUID(behaviors(r), b)
    )

    validBehaviorsAfterUpdate(behaviors, refs, r, b)

  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    getUIDs(behaviors, refs) == getUIDs(behaviors.updated(r,b), refs)
  }

  @opaque @ghost
  def uniqueUIDsAfterUpdate(
    behaviors: CMap[ActorRef, Behavior],
    @induct refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      validBehaviors(behaviors, refs) &&
      validBehavior(b) &&
      noDuplicate(getUIDs(behaviors, refs)) &&
      sameUID(behaviors(r), b)
    )

    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    getUIDsAfterUpdate(behaviors, refs, r, b)

  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    noDuplicate(getUIDs(behaviors.updated(r, b), refs))
  }


  /****************************************************************************
   * `isRing` is preserved after a behavior update
   ****************************************************************************/

  @opaque @ghost
  def isRingAfterUpdate(behaviors: CMap[ActorRef, Behavior], refs: List[ActorRef], r: ActorRef, b: Behavior): Unit = {
    require(isRing(behaviors, refs) && samePointer(behaviors(r), b))

    pointsToNextAfterUpdate(refs.length, behaviors, refs, r, b)

  } ensuring(_ => isRing(behaviors.updated(r, b), refs))


  /****************************************************************************
   * `validBehaviors` is preserved after a behavior update
   ****************************************************************************/

  @opaque @ghost
  def validBehaviorsAfterUpdate(behaviors: CMap[ActorRef, Behavior], @induct refs: List[ActorRef], r: ActorRef, b: Behavior): Unit = {
    require(validBehaviors(behaviors, refs) && validBehavior(b))

  } ensuring(_ => validBehaviors(behaviors.updated(r, b), refs))

  /****************************************************************************
   * `knowTrueLeaderAfterUpdate` is preserved after a behavior update
   ****************************************************************************/

  @opaque @ghost
  def knowTrueLeaderAfterUpdate(
    behaviors: CMap[ActorRef, Behavior],
    allRefs: List[ActorRef],
    @induct refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      !allRefs.isEmpty &&
      validBehaviors(behaviors, allRefs) &&
      refs.forall(knowTrueLeader(behaviors, allRefs, _)) &&
      validBehavior(b) &&
      sameUID(behaviors(r), b) &&
      knowTrueLeader(behaviors, allRefs, b)
    )

    sameMaxUID(behaviors, allRefs, r, b)
    validBehaviorsAfterUpdate(behaviors, allRefs, r, b)

  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, allRefs, r, b)
    refs.forall(knowTrueLeader(behaviors.updated(r, b), allRefs, _))
  }

  @opaque @ghost
  def knowTrueLeaderAfterUpdate(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      !refs.isEmpty &&
      validBehaviors(behaviors, refs) &&
      knowTrueLeader(behaviors, refs) &&
      validBehavior(b) &&
      sameUID(behaviors(r), b) &&
      knowTrueLeader(behaviors, refs, b)
    )

    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    knowTrueLeaderAfterUpdate(behaviors, refs, refs, r, b)
  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    knowTrueLeader(behaviors.updated(r, b), refs)
  }

  /****************************************************************************
   * Lemmas showing that electingTrueLeader is preserved after a behavior update
   ****************************************************************************/

  @opaque @ghost
  def electingTrueLeaderAfterBehaviorUpdate(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    iFrom: BigInt,
    m: Msg,
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      0 <= iFrom && iFrom < refs.length &&
      validBehaviors(behaviors, refs) &&
      electingTrueLeader(behaviors, refs, iFrom, m) &&
      validBehavior(b) &&
      sameUID(behaviors(r), b)
    )

    validBehaviorsAfterUpdate(behaviors, refs, r, b)

    m match {
      case Elected(leader) =>
        sameMaxUID(behaviors, refs, r, b)
      case Election(startingActor, uid) =>
        sameMaxUID(behaviors, refs, r, b)
        samePartialUID(behaviors, refs, refs.indexOf(startingActor), iFrom, r, b)
      case _ => ()
    }
  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    electingTrueLeader(behaviors.updated(r, b), refs, iFrom, m)
  }

  @opaque @ghost
  def electingTrueLeaderAfterBehaviorUpdate(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    iFrom: BigInt,
    channel: List[Msg],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      0 <= iFrom && iFrom < refs.length &&
      validBehaviors(behaviors, refs) &&
      electingTrueLeader(behaviors, refs, iFrom, channel) &&
      validBehavior(b) &&
      sameUID(behaviors(r), b)
    )
    decreases(channel.length)

    validBehaviorsAfterUpdate(behaviors, refs, r, b)

    if (!channel.isEmpty) {
      electingTrueLeaderAfterBehaviorUpdate(behaviors, refs, iFrom, channel.head, r, b) // for the first message
      electingTrueLeaderAfterBehaviorUpdate(behaviors, refs, iFrom, channel.tail, r, b)
    }
  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    electingTrueLeader(behaviors.updated(r, b), refs, iFrom, channel)
  }

  @opaque @ghost
  def electingTrueLeaderAfterBehaviorUpdate(
    n: BigInt,
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      n >= 0 &&
      validBehaviors(behaviors, refs) &&
      intForall(n, electingTrueLeader(behaviors, inboxes, refs, _)) &&
      validBehavior(b) &&
      sameUID(behaviors(r), b)
    )
    decreases(n)

    validBehaviorsAfterUpdate(behaviors, refs, r, b)

    if (n > 0) {
      getContains(refs, n-1)
      electingTrueLeaderAfterBehaviorUpdate(behaviors, refs, n-1, inboxes((refs(n-1), refs(increment(n-1, refs.length)))),  r, b) // for the n-1's channel
      electingTrueLeaderAfterBehaviorUpdate(n-1, behaviors, inboxes, refs, r, b)
    }

  } ensuring { _ =>
    validBehaviorsAfterUpdate(behaviors, refs, r, b)
    intForall(n, electingTrueLeader(behaviors.updated(r, b), inboxes, refs, _))
  }


  /****************************************************************************
   * Lemmas showing that nonParticipantNotInMessages is preserved after a
   * behavior update
   ****************************************************************************/

  @opaque @ghost
  def nonParticipantNotInMessagesAfterBehaviorUpdate(
    behaviors: CMap[ActorRef, Behavior],
    @induct refs: List[ActorRef],
    m: Msg,
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      nonParticipantNotInMessages(behaviors, refs, m) &&
      (behaviors(r) == b || !b.isInstanceOf[NonParticipant])
    )

    ()
  } ensuring(_ => nonParticipantNotInMessages(behaviors.updated(r, b), refs, m))

  @opaque @ghost
  def nonParticipantNotInMessagesAfterBehaviorUpdate(
    behaviors: CMap[ActorRef, Behavior],
    refs: List[ActorRef],
    channel: List[Msg],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      nonParticipantNotInMessages(behaviors, refs, channel) &&
      (behaviors(r) == b || !b.isInstanceOf[NonParticipant])
    )
    decreases(channel.length)

    if (!channel.isEmpty) {
      nonParticipantNotInMessagesAfterBehaviorUpdate(behaviors, refs, channel.head, r, b) // for the first message
      nonParticipantNotInMessagesAfterBehaviorUpdate(behaviors, refs, channel.tail, r, b)
    }
  } ensuring(_ => nonParticipantNotInMessages(behaviors.updated(r, b), refs, channel))

  @opaque @ghost
  def nonParticipantNotInMessagesAfterBehaviorUpdate(
    n: BigInt,
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    r: ActorRef,
    b: Behavior
  ): Unit = {
    require(
      n >= 0 &&
      intForall(n, nonParticipantNotInMessages(behaviors, inboxes, refs, _)) &&
      (behaviors(r) == b || !b.isInstanceOf[NonParticipant])
    )
    decreases(n)

    if (n > 0) {
      nonParticipantNotInMessagesAfterBehaviorUpdate(behaviors, refs, inboxes((refs(n-1), refs(increment(n-1, refs.length)))),  r, b) // for the n-1's channel
      nonParticipantNotInMessagesAfterBehaviorUpdate(n-1, behaviors, inboxes, refs, r, b)
    }

  } ensuring(_ => intForall(n, nonParticipantNotInMessages(behaviors.updated(r, b), inboxes, refs, _)))


  /****************************************************************************
   * `electingTrueLeader` is preserved after a channel update
   ****************************************************************************/

  @opaque @ghost
  def electingTrueLeaderAfterChannelUpdateAux(
    n: BigInt,
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt,
    channel: List[Msg]
  ): Unit = {
    require(
      n >= 0 &&
      0 <= iFrom && iFrom < refs.length &&
      validBehaviors(behaviors, refs) &&
      noDuplicate(refs) &&
      intForall(n, electingTrueLeader(behaviors, inboxes, refs, _)) &&
      electingTrueLeader(behaviors, refs, iFrom, channel)
    )
    decreases(n)

    if (n <= 0) {
      ()
    } else {
      electingTrueLeaderAfterChannelUpdateAux(n-1, behaviors, inboxes, refs, iFrom, channel)
      if (refs(iFrom) == refs(n-1)) {
        getInjective(refs, iFrom, n-1)
      }
    }

    ()

  } ensuring { _ =>
    val newInboxes = inboxes.updated((refs(iFrom), refs(increment(iFrom, refs.length))), channel)
    intForall(n, electingTrueLeader(behaviors, newInboxes, refs, _))
  }

  @opaque @ghost
  def electingTrueLeaderAfterChannelUpdate(
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt,
    channel: List[Msg]
  ): Unit = {
    require(
      0 <= iFrom && iFrom < refs.length &&
      validBehaviors(behaviors, refs) &&
      noDuplicate(refs) &&
      electingTrueLeader(behaviors, inboxes, refs) &&
      electingTrueLeader(behaviors, refs, iFrom, channel)
    )

    electingTrueLeaderAfterChannelUpdateAux(refs.length, behaviors, inboxes, refs, iFrom, channel)
  } ensuring { _ =>
    val newInboxes = inboxes.updated((refs(iFrom), refs(increment(iFrom, refs.length))), channel)
    electingTrueLeader(behaviors, newInboxes, refs)
  }

  /****************************************************************************
   * `nonParticipantNotInMessages` is preserved after a channel update
   ****************************************************************************/

  @opaque @ghost
  def nonParticipantNotInMessagesAfterChannelUpdate(
    @induct n: BigInt,
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt,
    channel: List[Msg]
  ): Unit = {
    require(
      n >= 0 &&
      0 <= iFrom && iFrom < refs.length &&
      intForall(n, nonParticipantNotInMessages(behaviors, inboxes, refs, _)) &&
      nonParticipantNotInMessages(behaviors, refs, channel)
    )

    ()

  } ensuring { _ =>
    val newInboxes = inboxes.updated((refs(iFrom), refs(increment(iFrom, refs.length))), channel)
    intForall(n, nonParticipantNotInMessages(behaviors, newInboxes, refs, _))
  }

  @opaque @ghost
  def nonParticipantNotInMessagesAfterChannelUpdate(
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt,
    channel: List[Msg]
  ): Unit = {
    require(
      0 <= iFrom && iFrom < refs.length &&
      nonParticipantNotInMessages(behaviors, inboxes, refs) &&
      nonParticipantNotInMessages(behaviors, refs, channel)
    )

    nonParticipantNotInMessagesAfterChannelUpdate(refs.length, behaviors, inboxes, refs, iFrom, channel)

  } ensuring { _ =>
    val newInboxes = inboxes.updated((refs(iFrom), refs(increment(iFrom, refs.length))), channel)
    nonParticipantNotInMessages(behaviors, newInboxes, refs)
  }
}
