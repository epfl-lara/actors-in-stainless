import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps

import actors._

import LeaderElection._
import LeaderElectionInvariant._
import LeaderElectionLemmas._
import BoundedQuantifiers._

object LeaderElectionNonParticipant {

  /****************************************************************************
   * Proof that `electingTrueLeader` and `nonParticipantNotInMessages` hold
   * after a `NonParticipant` sends a message after receiving `StartElection`
   ****************************************************************************/

  @opaque @ghost
  def nonParticipantReceivesStartElection(
    newBehaviors: CMap[ActorRef, Behavior],
    inboxes2: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt
  ): Unit = {
    require {
      validBehaviors(newBehaviors, refs) &&
      0 <= iFrom && iFrom < refs.length &&
      electingTrueLeader(newBehaviors, inboxes2, refs) &&
      nonParticipantNotInMessages(newBehaviors, inboxes2, refs) &&
      noDuplicate(refs) &&
      {
        val iTo = increment(iFrom, refs.length)
        val to = refs(iTo)
        electingTrueLeader(newBehaviors, inboxes2, refs, iTo) &&
        pointsToNext(newBehaviors, refs, iTo) &&
        newBehaviors(to).isInstanceOf[Participant] && {
          val Participant(next, uid) = newBehaviors(to)
          nonParticipantNotInMessages(newBehaviors, refs, Election(to, uid))
        }
      }
    }

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val Participant(next, uid) = newBehaviors(to)
    val ms = inboxes2(from -> to)
    val newChannel = inboxes2(to -> next) :+ Election(to, uid)
    val newInboxes = inboxes2.updated(to -> next, newChannel)

    getContains(refs, iTo)

    val (_, currentMax) = partialMaxUID(newBehaviors, refs, iTo, iTo)
    assert(uid == currentMax)
    indexOfGet(refs, iTo)
    assert(electingTrueLeader(newBehaviors, refs, iTo, Election(to, uid)))

    appendForall(inboxes2(to -> next), (m: Msg) => electingTrueLeader(newBehaviors, refs, iTo, m), Election(to, uid))
    assert(electingTrueLeader(newBehaviors, refs, iTo, newChannel))

    electingTrueLeaderAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)

    elimForall(refs.length, i => nonParticipantNotInMessages(newBehaviors, inboxes2, refs, i), iTo)
    assert(nonParticipantNotInMessages(newBehaviors, refs, inboxes2(to -> next)))
    appendForall(inboxes2(to -> next), (m: Msg) => nonParticipantNotInMessages(newBehaviors, refs, m), Election(to, uid))
    assert(nonParticipantNotInMessages(newBehaviors, refs, newChannel))
    nonParticipantNotInMessagesAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(nonParticipantNotInMessages(newBehaviors, newInboxes, refs))

  } ensuring { _ =>
    val iTo = increment(iFrom, refs.length)
    val to = refs(iTo)
    val Participant(next, uid) = newBehaviors(to)
    val newChannel = inboxes2(to -> next) :+ Election(to, uid)
    val newInboxes = inboxes2.updated(to -> next, newChannel)
    electingTrueLeader(newBehaviors, newInboxes, refs) &&
    nonParticipantNotInMessages(newBehaviors, newInboxes, refs)
  }

  /****************************************************************************
   * Proof that `electingTrueLeader` and `nonParticipantNotInMessages` hold
   * after a `NonParticipant` sends a message after receiving
   * `Election(startingActor, uid2)`
   ****************************************************************************/

  @opaque @ghost
  def nonParticipantReceivesElection(
    newBehaviors: CMap[ActorRef, Behavior],
    inboxes2: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt,
    startingActor: ActorRef,
    uid2: BigInt
  ): Unit = {
    require {
      validBehaviors(newBehaviors, refs) &&
      0 <= iFrom && iFrom < refs.length &&
      electingTrueLeader(newBehaviors, inboxes2, refs) &&
      nonParticipantNotInMessages(newBehaviors, inboxes2, refs) &&
      noDuplicate(refs) &&
      {
        val from = refs(iFrom)
        val iTo = increment(iFrom, refs.length)
        val to = refs(iTo)
        getContains(refs, iFrom)
        startingActor != to &&
        electingTrueLeader(newBehaviors, refs, iFrom, Election(startingActor, uid2)) &&
        newBehaviors(to).isInstanceOf[Participant] &&
        electingTrueLeader(newBehaviors, inboxes2, refs, iTo) &&
        pointsToNext(newBehaviors, refs, iTo) && {
          val Participant(next, uid) = newBehaviors(to)
          nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, max(uid, uid2)))
        }
      }
    }

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val Participant(next, uid) = newBehaviors(to)
    val ms = inboxes2(from -> to)
    val newChannel = inboxes2(to -> next) :+ Election(startingActor, max(uid, uid2))
    val newInboxes = inboxes2.updated(to -> next, newChannel)

    getContains(refs, iTo)

    indexOfInRange(refs, startingActor)
    indexOfGet(refs, iFrom)

    if (uid2 == partialMaxUID(newBehaviors, refs, refs.indexOf(startingActor), refs.indexOf(from))._2) {
      indexOfGet(refs, iTo)
      indexOfGet(refs, iFrom)
      indexOfInjective(refs, startingActor, to) // refs.indexOf(startingActor) != refs.indexOf(to)
      assert(max(uid, uid2) == partialMaxUID(newBehaviors, refs, refs.indexOf(startingActor), refs.indexOf(to))._2)
      check(electingTrueLeader(newBehaviors, refs, iTo, Election(startingActor, max(uid, uid2))))
    } else {
      maxGreater(newBehaviors, refs, to)
      assert(max(uid, uid2) == uid2)
      assert(max(uid, uid2) == maxUID(newBehaviors, refs)._2)
      check(electingTrueLeader(newBehaviors, refs, iTo, Election(startingActor, max(uid, uid2))))
    }
    appendForall(
      inboxes2(to -> next),
      (m: Msg) => electingTrueLeader(newBehaviors, refs, iTo, m), Election(startingActor, max(uid, uid2))
    )
    assert(electingTrueLeader(newBehaviors, refs, iTo, newChannel))
    electingTrueLeaderAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)

    assert(electingTrueLeader(newBehaviors, newInboxes, refs))

    elimForall(refs.length, i => nonParticipantNotInMessages(newBehaviors, inboxes2, refs, i), iTo)
    assert(nonParticipantNotInMessages(newBehaviors, refs, inboxes2(to -> next)))
    appendForall(inboxes2(to -> next), (m: Msg) => nonParticipantNotInMessages(newBehaviors, refs, m), Election(startingActor, max(uid, uid2)))
    assert(nonParticipantNotInMessages(newBehaviors, refs, newChannel))
    nonParticipantNotInMessagesAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(nonParticipantNotInMessages(newBehaviors, newInboxes, refs))

  } ensuring { _ =>
    val iTo = increment(iFrom, refs.length)
    val to = refs(iTo)
    val Participant(next, uid) = newBehaviors(to)
    val newChannel = inboxes2(to -> next) :+ Election(startingActor, max(uid, uid2))
    val newInboxes = inboxes2.updated(to -> next, newChannel)
    electingTrueLeader(newBehaviors, newInboxes, refs) &&
    nonParticipantNotInMessages(newBehaviors, newInboxes, refs)
  }

  /****************************************************************************
   * The whole invariant is preserved when a `NonParticipant` receives a message
   ****************************************************************************/

  @opaque @ghost
  def nonParticipantReceives(s: ActorSystem, refs: List[ActorRef], iFrom: BigInt): Unit = {
    require(
      invariant(s, refs) &&
      0 <= iFrom && iFrom < refs.length &&
      s.behaviors(refs(increment(iFrom, refs.length))).isInstanceOf[NonParticipant]
    )

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val newSystem = s.step(from, to)
    val NonParticipant(next, uid) = s.behaviors(to)
    val channel = s.inboxes(from -> to)
    val newBehaviors = newSystem.behaviors

    uniqueUIDsAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
    validBehaviorsAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
    isRingAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
    assert(isRing(newBehaviors, refs))
    electingTrueLeaderAfterBehaviorUpdate(refs.length, s.behaviors, s.inboxes, refs, to, newBehaviors(to))
    nonParticipantNotInMessagesAfterBehaviorUpdate(refs.length, s.behaviors, s.inboxes, refs, to, newBehaviors(to))
    knowTrueLeaderAfterUpdate(s.behaviors, refs, to, newBehaviors(to))

    channel match {
      case Nil() => ()
      case Cons(m, ms) =>

        val inboxes2 = s.inboxes.updated(from -> to, ms)

        // Proof that electingTrueLeader holds for newBehaviors, inboxes2
        getContains(refs, iTo)
        elimForall(refs.length, electingTrueLeader(newBehaviors, s.inboxes, refs, _), iFrom)
        assert(electingTrueLeader(newBehaviors, refs, iFrom, channel))
        elimForall(refs.length, electingTrueLeader(s.behaviors, s.inboxes, refs, _), iFrom)
        assert(electingTrueLeader(s.behaviors, refs, iFrom, channel))
        electingTrueLeaderAfterChannelUpdate(newBehaviors, s.inboxes, refs, iFrom, ms)

        // Proof that nonParticipantNotInMessages holds for newBehaviors, inboxes2
        elimForall(refs.length, nonParticipantNotInMessages(newBehaviors, s.inboxes, refs, _), iFrom)
        assert(nonParticipantNotInMessages(newBehaviors, refs, ms))
        nonParticipantNotInMessagesAfterChannelUpdate(newBehaviors, s.inboxes, refs, iFrom, ms)
        assert(nonParticipantNotInMessages(newBehaviors, inboxes2, refs))

        // Proof that refs contains next
        elimForall(refs.length, pointsToNext(s.behaviors, refs, _), iTo)
        assert(next == refs(increment(iTo, refs.length)))
        getContains(refs, increment(iTo, refs.length))
        assert(refs.contains(next))

        m match {
          case StartElection =>

            elimForall(refs.length, electingTrueLeader(newBehaviors, s.inboxes, refs, _), iTo)
            assert(electingTrueLeader(newBehaviors, inboxes2, refs, iTo))

            elimForall(refs.length, nonParticipantNotInMessages(s.behaviors, s.inboxes, refs, _), iFrom)
            forallContains(refs, (r: ActorRef) => nonParticipantNotInMessages(s.behaviors, m, r), to)

            nonParticipantNotInMessagesUnique(newBehaviors, refs, to, Election(to, uid))
            assert(nonParticipantNotInMessages(newBehaviors, refs, Election(to, uid)))

            nonParticipantReceivesStartElection(
              newBehaviors,
              inboxes2,
              refs,
              iFrom
            )

            val newChannel = inboxes2(to -> next) :+ Election(to, uid)
            assert(newSystem.inboxes == inboxes2.updated(to -> next, newChannel))
            check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
            check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))

          case Election(startingActor, uid2) =>

            elimForall(refs.length, electingTrueLeader(newBehaviors, s.inboxes, refs, _), iTo)
            assert(electingTrueLeader(newBehaviors, inboxes2, refs, iTo))

            // Proof that startingActor != to
            elimForall(refs.length, nonParticipantNotInMessages(s.behaviors, s.inboxes, refs, _), iFrom)
            forallContains(refs, (r: ActorRef) => nonParticipantNotInMessages(s.behaviors, m, r), to)
            assert(startingActor != to)

            assert(nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, uid2)))
            nonParticipantNotInMessagesSameMessage(newBehaviors, refs, Election(startingActor, uid2), Election(startingActor, max(uid, uid2)))
            assert(nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, max(uid, uid2))))

            nonParticipantReceivesElection(
              newBehaviors,
              inboxes2,
              refs,
              iFrom,
              startingActor,
              uid2
            )

            val newChannel = inboxes2(to -> next) :+ Election(startingActor, max(uid, uid2))
            assert(newSystem.inboxes == inboxes2.updated(to -> next, newChannel))
            check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
            check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))

          case _ =>
            assert(newSystem.inboxes == inboxes2)
            check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
            check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))
        }


        check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
        check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))
    }

    assert(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
    assert(validBehaviors(newBehaviors, refs))
    assert(isRing(newBehaviors, refs))
    assert(knowTrueLeader(newBehaviors, refs))
    assert(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))

    assert(invariant(newSystem, refs))
  }
}
