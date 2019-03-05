import stainless.lang._
import stainless.collection._
import stainless.annotation._

object counter {

  import actors._

  case class PrimBehav(backup: ActorRef, counter: Counter) extends Behavior {
    require(backup.name == "backup")

    override
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
      case Inc() =>
        backup ! Inc()
        PrimBehav(backup, counter.increment)

      case _ => this
    }
  }

  case class BackBehav(counter: Counter) extends Behavior {

    override
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
      case Inc() =>
        BackBehav(counter.increment)

      case _ => this
    }
  }

  @extern
  def noSender = akka.actor.ActorRef.noSender

  val Primary = ActorRef("primary", noSender)
  val Backup  = ActorRef("backup", noSender)

  case class Inc() extends Msg

  case class Counter(value: BigInt) {
    require(value >= 0)

    def increment: Counter = Counter(value + 1)

    def <=(that: Counter): Boolean = this.value <= that.value
  }

  @ghost
  def invariant(s: ActorSystem): Boolean = {
    s.inboxes(Backup -> Backup).isEmpty &&
    s.inboxes(Backup -> Primary).isEmpty &&
    s.inboxes(Primary -> Primary).isEmpty &&
    s.inboxes(Primary -> Backup).forall(_ == Inc()) && {
      (s.behaviors(Primary), s.behaviors(Backup)) match {
        case (PrimBehav(_, p), BackBehav(b)) =>
          p.value == b.value + s.inboxes(Primary -> Backup).length

        case _ => false
      }
    }
  }

  def validRef(ref: ActorRef) = {
    ref == Primary || ref == Backup
  }

  @ghost
  def theorem(s: ActorSystem, from: ActorRef, to: ActorRef): Boolean = {
    require(invariant(s) && validRef(from) && validRef(to))
    val newSystem = s.step(from, to)
    invariant(newSystem)
  }.holds

}
