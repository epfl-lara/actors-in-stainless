
package stainless.collection

import stainless.lang._
import stainless.collection._
import stainless.annotation._

case class CMap[A, B](f: A => B) {

  def apply(k: A): B = {
    f(k)
  }

  def updated(k: A, v: B): CMap[A, B] = {
    CMap((x: A) => if (x == k) v else f(x))
  }

  def getOrElse(k: A, v: B): B = {
    f(k)
  }

  def contains(k: A): Boolean =
    true

}

object CMap {

  @library
  def fromList[A, B](list: List[(A, B)])(default: B): CMap[A, B] = {
    list.foldLeft(CMap((x: A) => default)) { case (acc, (k, v)) =>
      acc.updated(k, v)
    }
  } ensuring { res =>
    forall { (k: A) =>
      val p = list.find(_._1 == k)
      if (p.isDefined) res(k) == p.get._2
      else res(k) == default
    }
  }

}
