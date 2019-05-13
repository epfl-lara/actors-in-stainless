import stainless.lang._
import stainless.proof.check
import stainless.collection._
import stainless.annotation._

import scala.util.Random

import actors._

object KVS {

  case class Variable(x: BigInt)
  sealed abstract class Event {
    val v: Variable
    val value: BigInt
  }
  case class ReadEvent(v: Variable, value: BigInt) extends Event
  case class WriteEvent(v: Variable, value: BigInt) extends Event

  case object DisplayBehavior extends Msg
  case class Initialize(refs: List[ActorRef]) extends Msg
  case class UserWrite(x: Variable, i: BigInt) extends Msg
  case class UserRead(x: Variable) extends Msg
  case class SystemWrite(x: Variable, i: BigInt, previousEvents: Set[Event]) extends Msg

  def appliedAllWrites(receiverHistory: Set[Event], messageHistory: Set[Event])(implicit ctx: ActorContext): Boolean =
    messageHistory.subsetOf(receiverHistory)

  case class Uninitialized() extends Behavior {
    override def processMsg(m: Msg)(implicit ctx: ActorContext) = {
      m match {
        case Initialize(refs) =>
          Process(refs, CMap(_ => 0), Set(), List())

        case _ =>
          this
      }
    }
  }

  case class Process(refs: List[ActorRef], mem: CMap[Variable,BigInt], appliedWrites: Set[Event], localEvents: List[Event]) extends Behavior {
    def broadcast(refs: List[ActorRef], m: Msg)(implicit ctx: ActorContext): Unit = {
      refs match {
        case Nil() => ()
        case Cons(r, rs) =>
          r ! m
          broadcast(rs, m)
      }
    }

    override def processMsg(m: Msg)(implicit ctx: ActorContext) = {
      m match {
        case DisplayBehavior =>
          // Stainless doesn't like `toString`
          // stainless.io.StdOut.println(List.mkString(localEvents.reverse, "\n", ((e: Event) => e.toString)))
          this

        case UserWrite(x, i) =>
          broadcast(refs, SystemWrite(x, i, appliedWrites))
          Process(refs, mem.updated(x, i), appliedWrites ++ Set(WriteEvent(x, i)), WriteEvent(x, i) :: localEvents)

        case SystemWrite(x, i, previousWrites) =>
          if (appliedAllWrites(appliedWrites, previousWrites))
            Process(refs, mem.updated(x, i), appliedWrites ++ Set(WriteEvent(x, i)), localEvents)
          else {
            ctx.self ! m
            this
          }

        case UserRead(x) =>
          Process(refs, mem, appliedWrites, ReadEvent(x, mem(x)) :: localEvents)

        case _ => this
      }
    }
  }

  @ignore
  def main(args: Array[String]) = {
    if (args.length != 4) {
      println("Usage: kvs numberOfActors eventsPerActor numberOfVariables maxValue")
      println("Try for instance: kvs 3 20 2 1000")
    } else {
      val system = akka.actor.ActorSystem("KVS")
      val numberOfActors = args(0).toInt
      val eventsPerActor = args(1).toInt
      val numberOfVariables = args(2).toInt
      val maxValue = args(3).toInt

      val actorRefs = (1 to numberOfActors).map(i =>
        i ->
          ActorRef(
            "Process_" + i.toString,
            system.actorOf(
              akka.actor.Props(new ActorWrapper(new Uninitialized())),
              name = i.toString,
            )
          )
      ).toMap

      // We first initialize each actor by setting up references to other actors
      for (i <- 1 to numberOfActors) {
        implicit val ctx = ActorContext(actorRefs(i), Nil())
        actorRefs(i) ! Initialize(List(actorRefs.filterNot(_._1 == i).values.toSeq: _*))
      }

      // Then we wait a bit
      Thread.sleep(1000)

      // And we perform some random writes and reads
      for (i <- 1 to numberOfActors) {
        for (j <- 1 to eventsPerActor) {
          Thread.sleep(100)
          val x = Variable(Random.nextInt(numberOfVariables))
          val value = Random.nextInt(maxValue) + 1
          val msg =
            if (Random.nextBoolean())
              UserWrite(x, value)
            else
              UserRead(x)
          implicit val ctx = ActorContext(actorRefs(i), Nil())
          actorRefs(Random.nextInt(numberOfActors) + 1) ! msg
        }
      }

      // Finally, we display the history of each actor
      for (i <- 1 to numberOfActors) {
        Thread.sleep(3000)
        println("=============")
        println("Actor: " + i)
        implicit val ctx = ActorContext(actorRefs(i), Nil())
        actorRefs(i) ! DisplayBehavior
        println("\n")
      }
    }
  }
}
