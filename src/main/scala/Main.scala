import stainless.lang._
import stainless.annotation._
import stainless.collection._

import actors._
import counter._

object Main {

  @extern
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
