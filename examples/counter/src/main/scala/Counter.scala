import stainless.lang._
import stainless.proof._
import stainless.collection._
import stainless.annotation._

object Counter {

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

  @extern @pure
  val noSender = akka.actor.ActorRef.noSender

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
    s.inboxes(Primary -> Primary).forall(_ == Inc()) &&
    s.inboxes(Primary -> Backup).forall(_ == Inc()) && {
      (s.behaviors(Primary), s.behaviors(Backup)) match {
        case (PrimBehav(bRef, p), BackBehav(b)) if bRef == Backup =>
          p.value == b.value + s.inboxes(Primary -> Backup).length

        case _ => false
      }
    }
  }

  @induct @ghost
  def appendInc(msgs: List[Msg]) = {
    require(msgs.forall(_ == Inc()))
    ()
  } ensuring(_ => (msgs :+ Inc()).forall(_ == Inc()))

  @ghost
  def validRef(ref: ActorRef) = {
    ref == Primary || ref == Backup
  }

  @ghost
  def theoremPrimary(s: ActorSystem, from: ActorRef): Boolean = {
    require(invariant(s) && validRef(from))

    val newSystem = s.step(from, Primary)
    appendInc(s.inboxes(Primary -> Backup))
    invariant(newSystem)
  }.holds

  @ghost
  def theoremBackup(s: ActorSystem, from: ActorRef): Boolean = {
    require(invariant(s) && validRef(from))

    val newSystem = s.step(from, Backup)
    invariant(newSystem)
  }.holds

  @ignore
  def main(args: Array[String]): Unit = {
    val initCounter = Counter(0)

    val system = akka.actor.ActorSystem("Counter")

    val backupRef = ActorRef(
      "backup",
      system.actorOf(
        akka.actor.Props(new ActorWrapper(BackBehav(initCounter))),
        name = "backup"
      )
    )

    val primaryRef = ActorRef(
      "primary",
      system.actorOf(
        akka.actor.Props(new ActorWrapper(PrimBehav(backupRef, initCounter))),
        name = "primary"
      )
    )

    implicit val ctx = ActorContext(primaryRef, Nil())

    import system.dispatcher
    import scala.concurrent.duration._
    system.scheduler.schedule(500.millis, 1000.millis) {
      primaryRef ! Inc()
    }
  }

}
