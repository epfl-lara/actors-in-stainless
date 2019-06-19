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

object LeaderElectionParticipant {

  /****************************************************************************
   * Proof that `electingTrueLeader` and `nonParticipantNotInMessages` hold
   * after a `Participant` sends a message after receiving `Elected(leader)`
   ****************************************************************************/

  @opaque @ghost
  def participantReceivesElected(
    newBehaviors: CMap[ActorRef, Behavior],
    inboxes2: CMap[(ActorRef, ActorRef), List[Msg]],
    refs: List[ActorRef],
    iFrom: BigInt,
    leader: BigInt
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
        getContains(refs, iTo) // to establish: refs.contains(to)
        electingTrueLeader(newBehaviors, refs, iTo, Elected(leader)) &&
        electingTrueLeader(newBehaviors, inboxes2, refs, iTo) &&
        pointsToNext(newBehaviors, refs, iTo) &&
        newBehaviors(to).isInstanceOf[KnowLeader]
      }
    }

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val KnowLeader(next, leader2, uid) = newBehaviors(to)
    val ms = inboxes2(from -> to)
    val newChannel = inboxes2(to -> next) :+ Elected(leader)
    val newInboxes = inboxes2.updated(to -> next, newChannel)

    assert(next == refs(increment(iTo, refs.length)))

    // Proof that electingTrueLeader(newBehaviors, newInboxes, refs) holds
    appendForall(inboxes2(to -> next), (m: Msg) => electingTrueLeader(newBehaviors, refs, iTo, m), Elected(leader))
    assert(electingTrueLeader(newBehaviors, refs, iTo, newChannel))
    electingTrueLeaderAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(electingTrueLeader(newBehaviors, newInboxes, refs))

    // Proof that nonParticipantNotInMessages(newBehaviors, newInboxes, refs) holds
    elimForall(refs.length, i => nonParticipantNotInMessages(newBehaviors, inboxes2, refs, i), iTo)
    assert(nonParticipantNotInMessages(newBehaviors, refs, inboxes2(to -> next)))
    nonParticipantNotInMessagesElected(newBehaviors, refs, leader)
    assert(nonParticipantNotInMessages(newBehaviors, refs, Elected(leader)))
    appendForall(inboxes2(to -> next), (m: Msg) => nonParticipantNotInMessages(newBehaviors, refs, m), Elected(leader))
    assert(nonParticipantNotInMessages(newBehaviors, refs, newChannel))
    nonParticipantNotInMessagesAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(nonParticipantNotInMessages(newBehaviors, newInboxes, refs))

  } ensuring { _ =>
    val iTo = increment(iFrom, refs.length)
    val to = refs(iTo)
    val KnowLeader(next, leader2, uid) = newBehaviors(to)
    val newChannel = inboxes2(to -> next) :+ Elected(leader)
    val newInboxes = inboxes2.updated(to -> next, newChannel)
    electingTrueLeader(newBehaviors, newInboxes, refs) &&
    nonParticipantNotInMessages(newBehaviors, newInboxes, refs)
  }

  /****************************************************************************
   * Proof that `electingTrueLeader` and `nonParticipantNotInMessages` hold
   * after a `Participant` (with `uid`) sends a message after receiving
   * `Election(startingActor, uid2)` with `uid2 == uid`
   ****************************************************************************/

  @opaque @ghost
  def participantReceivesElectionEqual(
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
      noDuplicate(getUIDs(newBehaviors, refs)) &&
      {
        val from = refs(iFrom)
        val iTo = increment(iFrom, refs.length)
        val to = refs(iTo)
        getContains(refs, iFrom)
        electingTrueLeader(newBehaviors, refs, iFrom, Election(startingActor, uid2)) &&
        newBehaviors(to).isInstanceOf[KnowLeader] &&
        electingTrueLeader(newBehaviors, inboxes2, refs, iTo) &&
        pointsToNext(newBehaviors, refs, iTo) && {
          val KnowLeader(next, leader, uid) = newBehaviors(to)
          uid2 == uid &&
          nonParticipantNotInMessages(newBehaviors, refs, Elected(uid))
        }
      }
    }

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val KnowLeader(next, leader, uid) = newBehaviors(to)
    val ms = inboxes2(from -> to)
    val newChannel = inboxes2(to -> next) :+ Elected(uid)
    val newInboxes = inboxes2.updated(to -> next, newChannel)

    getContains(refs, iTo) // refs.contains(to)
    indexOfGet(refs, iFrom) // refs.indexOf(refs(iFrom)) == iFrom

    // Proof of electingTrueLeader(newBehaviors, refs, to, Elected(uid))
    val (iPartialMax, partialMax) = partialMaxUID(newBehaviors, refs, refs.indexOf(startingActor), iFrom)
    if (uid == partialMax) {
      val iS = refs.indexOf(startingActor)
      getContains(refs, iPartialMax) // refs.contains(refs(iPartialMax))
      getUIDInjective(newBehaviors, refs, refs(iPartialMax), to) // refs(iPartialMax) == to
      indexOfGet(refs, iPartialMax) // refs.indexOf(refs(iPartialMax)) == iPartialMax
      indexOfGet(refs, iTo) // refs.indexOf(to) == iTo
      assert(refs.indexOf(refs(iPartialMax)) == refs.indexOf(to))
      assert(iPartialMax == iTo)
      incrementBetween(refs.length, iS, iFrom) // iTo == iS
      assert(uid == partialMaxUID(newBehaviors, refs, refs.indexOf(startingActor), refs.indexOf(startingActor))._2)
      assert(uid == partialMaxUID(newBehaviors, refs, iTo, iFrom)._2)
      val (rMax, overallMax) = maxUID(newBehaviors, refs)
      indexOfInRange(refs, rMax)
      assert(inBetween(refs.length, iTo, iFrom, refs.indexOf(rMax)))
      partialMaxGreater(newBehaviors, refs, iTo, iFrom, refs.indexOf(rMax)) // uid >= overallMax
      getIndexOf(refs, rMax) // refs(refs.indexOf(rMax)) == rMax
      maxGreater(newBehaviors, refs, to) // uid <= overallMax
      assert(electingTrueLeader(newBehaviors, refs, iTo, Elected(uid)))
      check(uid == maxUID(newBehaviors, refs)._2)
    } else {
      check(uid == maxUID(newBehaviors, refs)._2)
    }

    // Proof of electingTrueLeader(newBehaviors, newInboxes, refs)
    appendForall(
      inboxes2(to -> next),
      (m: Msg) => electingTrueLeader(newBehaviors, refs, iTo, m), Elected(uid)
    )
    assert(electingTrueLeader(newBehaviors, refs, iTo, newChannel))
    electingTrueLeaderAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(electingTrueLeader(newBehaviors, newInboxes, refs))

    // Proof of nonParticipantNotInMessages(newBehaviors, newInboxes, refs)
    elimForall(refs.length, i => nonParticipantNotInMessages(newBehaviors, inboxes2, refs, i), iTo)
    assert(nonParticipantNotInMessages(newBehaviors, refs, inboxes2(to -> next)))
    appendForall(inboxes2(to -> next), (m: Msg) => nonParticipantNotInMessages(newBehaviors, refs, m), Elected(uid))
    assert(nonParticipantNotInMessages(newBehaviors, refs, newChannel))
    nonParticipantNotInMessagesAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(nonParticipantNotInMessages(newBehaviors, newInboxes, refs))

  } ensuring { _ =>
    val iTo = increment(iFrom, refs.length)
    val to = refs(iTo)
    val KnowLeader(next, leader, uid) = newBehaviors(to)
    val newChannel = inboxes2(to -> next) :+ Elected(uid)
    val newInboxes = inboxes2.updated(to -> next, newChannel)
    uid == maxUID(newBehaviors, refs)._2 &&
    electingTrueLeader(newBehaviors, newInboxes, refs) &&
    nonParticipantNotInMessages(newBehaviors, newInboxes, refs)
  }


  /****************************************************************************
   * Proof that `electingTrueLeader` and `nonParticipantNotInMessages` hold
   * after a `Participant` (with `uid`) sends a message after receiving
   * `Election(startingActor, uid2)` with `uid2 > uid`
   ****************************************************************************/

  @opaque @ghost
  def participantReceivesElectionLarger(
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
        electingTrueLeader(newBehaviors, refs, iFrom, Election(startingActor, uid2)) &&
        newBehaviors(to).isInstanceOf[Participant] &&
        electingTrueLeader(newBehaviors, inboxes2, refs, iTo) &&
        pointsToNext(newBehaviors, refs, iTo) && {
          val Participant(next, uid) = newBehaviors(to)
          uid2 > uid &&
          nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, uid2))
        }
      }
    }

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val Participant(next, uid) = newBehaviors(to)
    val ms = inboxes2(from -> to)
    val newChannel = inboxes2(to -> next) :+ Election(startingActor, uid2)
    val newInboxes = inboxes2.updated(to -> next, newChannel)

    getContains(refs, iTo)

    // Proof of electingTrueLeader(newBehaviors, newInboxes, refs)
    indexOfGet(refs, iTo)
    indexOfGet(refs, iFrom)
    val (iMax, partialMax) = partialMaxUID(newBehaviors, refs, refs.indexOf(startingActor), iFrom)
    if (uid2 == partialMax) {
      if (refs.indexOf(startingActor) == iTo) {
        val (rMax, overallMax) = maxUID(newBehaviors, refs)
        indexOfInRange(refs, rMax)
        assert(inBetween(refs.length, iTo, iFrom, refs.indexOf(rMax)))
        getIndexOf(refs, rMax) // refs(refs.indexOf(rMax)) == rMax
        partialMaxGreater(newBehaviors, refs, iTo, iFrom, refs.indexOf(rMax)) // uid2 >= overallMax
        getContains(refs, iMax) // refs.contains(refs(iMax))
        maxGreater(newBehaviors, refs, refs(iMax)) // uid2 <= overallMax
        check(uid2 == overallMax)
      } else {
        check(uid2 == partialMaxUID(newBehaviors, refs, refs.indexOf(startingActor), refs.indexOf(to))._2)
      }
    } else {
      check(uid2 == maxUID(newBehaviors, refs)._2)
    }
    assert(electingTrueLeader(newBehaviors, refs, iTo, Election(startingActor, uid2)))
    appendForall(
      inboxes2(to -> next),
      (m: Msg) => electingTrueLeader(newBehaviors, refs, iTo, m),
      Election(startingActor, uid2)
    )
    assert(electingTrueLeader(newBehaviors, refs, iTo, newChannel))
    electingTrueLeaderAfterChannelUpdate(newBehaviors, inboxes2, refs, iTo, newChannel)
    assert(electingTrueLeader(newBehaviors, newInboxes, refs))

    elimForall(refs.length, i => nonParticipantNotInMessages(newBehaviors, inboxes2, refs, i), iTo)
    assert(nonParticipantNotInMessages(newBehaviors, refs, inboxes2(to -> next)))
    appendForall(inboxes2(to -> next), (m: Msg) => nonParticipantNotInMessages(newBehaviors, refs, m),  Election(startingActor, uid2))
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
   * The whole invariant is preserved when a `Participant` receives a message
   ****************************************************************************/

  @opaque @ghost
  def participantReceives(s: ActorSystem, refs: List[ActorRef], iFrom: BigInt): Unit = {
    require(
      invariant(s, refs) &&
      0 <= iFrom && iFrom < refs.length &&
      s.behaviors(refs(increment(iFrom, refs.length))).isInstanceOf[Participant]
    )

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val newSystem = s.step(from, to)
    val Participant(next, uid) = s.behaviors(to)
    val channel = s.inboxes(from -> to)
    val newBehaviors = newSystem.behaviors

    uniqueUIDsAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
    validBehaviorsAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
    isRingAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
    assert(isRing(newBehaviors, refs))
    electingTrueLeaderAfterBehaviorUpdate(refs.length, s.behaviors, s.inboxes, refs, to, newBehaviors(to))
    nonParticipantNotInMessagesAfterBehaviorUpdate(refs.length, s.behaviors, s.inboxes, refs, to, newBehaviors(to))

    channel match {
      case Nil() => ()
      case Cons(m, ms) =>

        val inboxes2 = s.inboxes.updated(from -> to, ms)

        getContains(refs, iFrom)
        getContains(refs, iTo)

        // // Proof that electingTrueLeader holds for s.behaviors, channel
        // elimForall(refs.length, electingTrueLeader(s.behaviors, s.inboxes, refs, _), iFrom)
        // assert(electingTrueLeader(s.behaviors, refs, from, channel))

        // Proof that electingTrueLeader holds for newBehaviors, inboxes2
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
          case Elected(leader) =>

            elimForall(refs.length, electingTrueLeader(newBehaviors, s.inboxes, refs, _), iTo)
            assert(electingTrueLeader(newBehaviors, inboxes2, refs, iTo))

            elimForall(refs.length, nonParticipantNotInMessages(s.behaviors, s.inboxes, refs, _), iFrom)
            forallContains(refs, (r: ActorRef) => nonParticipantNotInMessages(s.behaviors, m, r), to)

            nonParticipantNotInMessagesUnique(newBehaviors, refs, to, Elected(leader))
            assert(nonParticipantNotInMessages(newBehaviors, refs, Elected(leader)))

            participantReceivesElected(
              newBehaviors,
              inboxes2,
              refs,
              iFrom,
              leader
            )

            // Proof that the new behavior KnowLeader() corresponds to a leader
            assert(leader == maxUID(s.behaviors, refs)._2)
            assert(knowTrueLeader(s.behaviors, refs, newBehaviors(to)))
            knowTrueLeaderAfterUpdate(s.behaviors, refs, to, newBehaviors(to))

            val newChannel = inboxes2(to -> next) :+ Elected(leader)
            assert(newSystem.inboxes == inboxes2.updated(to -> next, newChannel))
            check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
            check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))

          case Election(startingActor, uid2) =>

            elimForall(refs.length, electingTrueLeader(newBehaviors, s.inboxes, refs, _), iTo)
            assert(electingTrueLeader(newBehaviors, inboxes2, refs, iTo))

            // Proof that startingActor != to
            // elimForall(refs.length, nonParticipantNotInMessages(s.behaviors, s.inboxes, refs, _), iFrom)
            // forallContains(refs, (r: ActorRef) => nonParticipantNotInMessages(s.behaviors, m, r), to)
            // assert(startingActor != to)

            // assert(nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, uid2)))
            // nonParticipantNotInMessagesSameMessage(newBehaviors, refs, Election(startingActor, uid2), Election(startingActor, max(uid, uid2)))
            // assert(nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, max(uid, uid2))))

            if (uid2 == uid) {
              nonParticipantNotInMessagesFresh(newBehaviors, refs, Elected(uid))
              participantReceivesElectionEqual(
                newBehaviors,
                inboxes2,
                refs,
                iFrom,
                startingActor,
                uid2
              )
              val newChannel = inboxes2(to -> next) :+ Elected(uid)
              assert(newSystem.inboxes == inboxes2.updated(to -> next, newChannel))
              sameMaxUID(s.behaviors, refs, to, newBehaviors(to))
              check(knowTrueLeader(s.behaviors, refs, newBehaviors(to)))
              check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
              check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))
            }
            else if (uid2 > uid) {
              elimForall(refs.length, nonParticipantNotInMessages(newBehaviors, s.inboxes, refs, _), iFrom)
              assert(nonParticipantNotInMessages(newBehaviors, refs, Election(startingActor, uid2)))
              participantReceivesElectionLarger(
                newBehaviors,
                inboxes2,
                refs,
                iFrom,
                startingActor,
                uid2
              )
              val newChannel = inboxes2(to -> next) :+ Election(startingActor, uid2)
              assert(newSystem.inboxes == inboxes2.updated(to -> next, newChannel))
              check(knowTrueLeader(s.behaviors, refs, newBehaviors(to)))
              check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
              check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))
            } else {
              assert(newSystem.inboxes == inboxes2)
              check(knowTrueLeader(s.behaviors, refs, newBehaviors(to)))
              check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
              check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))
            }

            knowTrueLeaderAfterUpdate(s.behaviors, refs, to, newBehaviors(to))

            check(knowTrueLeader(newBehaviors, refs))
            check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
            check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))

          case _ =>
            assert(newSystem.inboxes == inboxes2)

            knowTrueLeaderAfterUpdate(s.behaviors, refs, to, newBehaviors(to))
            check(knowTrueLeader(newBehaviors, refs))
            check(electingTrueLeader(newBehaviors, newSystem.inboxes, refs))
            check(nonParticipantNotInMessages(newBehaviors, newSystem.inboxes, refs))
        }

        check(knowTrueLeader(newBehaviors, refs))
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
