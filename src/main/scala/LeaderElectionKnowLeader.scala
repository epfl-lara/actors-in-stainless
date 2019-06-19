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

object LeaderElectionKnowLeader {

  /****************************************************************************
   * The whole invariant is preserved when a `KnowLeader` receives any message
   ****************************************************************************/

  @opaque @ghost
  def knowLeaderReceives(s: ActorSystem, refs: List[ActorRef], iFrom: BigInt): Unit = {
    require(
      invariant(s, refs) &&
      0 <= iFrom && iFrom < refs.length &&
      s.behaviors(refs(increment(iFrom, refs.length))).isInstanceOf[KnowLeader]
    )

    val iTo = increment(iFrom, refs.length)
    val from = refs(iFrom)
    val to = refs(iTo)
    val newSystem = s.step(from, to)
    val KnowLeader(next, leader, uid) = s.behaviors(to)
    val channel = s.inboxes(from -> to)
    val newBehaviors = newSystem.behaviors

    uniqueUIDsAfterUpdate(s.behaviors, refs, to, newSystem.behaviors(to))
    validBehaviorsAfterUpdate(s.behaviors, refs, to, newSystem.behaviors(to))
    isRingAfterUpdate(s.behaviors, refs, to, newSystem.behaviors(to))
    assert(isRing(newSystem.behaviors, refs))
    electingTrueLeaderAfterBehaviorUpdate(refs.length, s.behaviors, s.inboxes, refs, to, newSystem.behaviors(to))
    nonParticipantNotInMessagesAfterBehaviorUpdate(refs.length, s.behaviors, s.inboxes, refs, to, newSystem.behaviors(to))

    // The behavior doesn't change so the new behavior still satisfies `knowTrueLeader`
    getContains(refs, iTo)
    forallContains(refs, (r: ActorRef) => knowTrueLeader(s.behaviors, refs, r), to)
    assert(newBehaviors(to) == s.behaviors(to))
    assert(knowTrueLeader(s.behaviors, refs, s.behaviors(to)))
    assert(knowTrueLeader(s.behaviors, refs, newBehaviors(to)))
    knowTrueLeaderAfterUpdate(s.behaviors, refs, to, newSystem.behaviors(to))

    channel match {
      case Nil() => ()
      case Cons(m, ms) =>

        val inboxes2 = s.inboxes.updated(from -> to, ms)

        // Proof that electingTrueLeader holds for newBehaviors, inboxes2
        elimForall(refs.length, electingTrueLeader(newSystem.behaviors, s.inboxes, refs, _), iFrom)
        assert(electingTrueLeader(newSystem.behaviors, refs, iFrom, channel))
        elimForall(refs.length, electingTrueLeader(s.behaviors, s.inboxes, refs, _), iFrom)
        assert(electingTrueLeader(s.behaviors, refs, iFrom, channel))
        electingTrueLeaderAfterChannelUpdate(newSystem.behaviors, s.inboxes, refs, iFrom, ms)

        // Proof that nonParticipantNotInMessages holds for newBehaviors, inboxes2
        elimForall(refs.length, nonParticipantNotInMessages(newSystem.behaviors, s.inboxes, refs, _), iFrom)
        assert(nonParticipantNotInMessages(newBehaviors, refs, ms))
        nonParticipantNotInMessagesAfterChannelUpdate(newBehaviors, s.inboxes, refs, iFrom, ms)
        assert(nonParticipantNotInMessages(newBehaviors, inboxes2, refs))

        // Proof that refs contains next
        elimForall(refs.length, pointsToNext(s.behaviors, refs, _), iTo)
        assert(next == refs(increment(iTo, refs.length)))
        getContains(refs, increment(iTo, refs.length))
        assert(refs.contains(next))

        assert(newSystem.inboxes == inboxes2)
        check(electingTrueLeader(newSystem.behaviors, newSystem.inboxes, refs))
        check(nonParticipantNotInMessages(newSystem.behaviors, newSystem.inboxes, refs))
    }

    assert(electingTrueLeader(newSystem.behaviors, newSystem.inboxes, refs))
    assert(validBehaviors(newSystem.behaviors, refs))
    assert(isRing(newSystem.behaviors, refs))
    assert(knowTrueLeader(newSystem.behaviors, refs))
    assert(nonParticipantNotInMessages(newSystem.behaviors, newSystem.inboxes, refs))

    assert(invariant(newSystem, refs))
  }
}
