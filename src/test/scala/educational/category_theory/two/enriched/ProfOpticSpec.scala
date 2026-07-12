package educational.category_theory.two.enriched

import educational.category_theory.two.enriched.ExistentialAndProfunctorOptics._
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.must.Matchers

class ProfOpticSpec extends AnyFunSpec with Matchers {
  import FunctionTupleModel._

  final case class Box[A](value: A, label: String)

  private val boxValue: GeneralOptic[Int, String, Box[Int], Box[String]] =
    Optic[Obj, Arr, Obj, Arr, Obj, Arr, Pair, Unit, Pair, Pair, Int, String, Box[Int], Box[String], String](
      amaf = action,
      amag = action,
      aoa = (),
      aos = (),
      aob = (),
      aot = (),
      al = (box: Box[Int]) => (box.label, box.value),
      ar = (pair: (String, String)) => Box(pair._2, pair._1),
      aox = ()
    )

  describe("the function profunctor and tuple Tambara fixture") {
    it("dimap precomposes and postcomposes") {
      val transformed: String => String =
        functionProfunctor
          .dimap[Int, String, Int, String]((), (), (), ())(_.length)(_.toString)(_ + 1)
      transformed("abc") mustBe "4"
    }

    it("tambara preserves the residual value") {
      val lifted: ((String, Int)) => (String, String) =
        functionTambara.tambara[Int, String, String]((), (), ())(_.toString)
      lifted(("context", 42)) mustBe (("context", "42"))
    }
  }

  describe("ex2prof") {
    it("updates the focus while preserving the residual context") {
      val update: Box[Int] => Box[String] =
        ex2prof(boxValue).run[Arr](_.toString)
      update(Box(42, "answer")) mustBe Box("42", "answer")
    }

    it("updates the focus while preserving the residual label") {
      val update: Box[Int] => Box[String] =
        ex2prof(boxValue).run[Arr](n => s"value=$n")

      update(Box(42, "answer")) mustBe
        Box("value=42", "answer")

      update(Box(-7, "negative")) mustBe
        Box("value=-7", "negative")
    }

    it("supports different focus transformations") {
      val increment: Box[Int] => Box[Int] =
        ex2prof(
          optic[Int, Int, Box[Int], Box[Int], String](
            left = box => (box.label, box.value),
            right = pair => Box(pair._2, pair._1)
          )
        ).run[Arr](_ + 1)

      increment(Box(41, "answer")) mustBe
        Box(42, "answer")
    }
  }

  describe("prof2ex") {
    it("round-trips observationally through the profunctor representation") {
      val prof = ex2prof(boxValue)
      val rebuilt = prof2ex(prof)(action, action, (), ())

      val originalUpdate: Box[Int] => Box[String] =
        prof.run[Arr](n => s"value=$n")

      val rebuiltUpdate: Box[Int] => Box[String] =
        ex2prof(rebuilt).run[Arr](n => s"value=$n")

      val samples = List(
        Box(0, "zero"),
        Box(1, "one"),
        Box(-7, "negative"),
        Box(42, "answer")
      )

      samples.map(originalUpdate) mustBe samples.map(rebuiltUpdate)
    }
  }
}

object FunctionTupleModel {
  type Obj[A] = Unit
  type Arr[A, B] = A => B
  type Pair[A, B] = (A, B)

  implicit def objectWitness[A]: Obj[A] = ()

  val category: VCategory[Obj, Arr] =
    new VCategory[Obj, Arr] {
      override def unit[X](implicit ox: Obj[X]): Arr[X, X] = x => x
      override def comp[X, Y, Z](implicit ox: Obj[X]):
          Arr[Y, Z] => Arr[X, Y] => Arr[X, Z] =
        g => f => x => g(f(x))
    }

  val pairBifunctor: VBifunctor[Obj, Arr, Obj, Arr, Obj, Arr, Pair] =
    new VBifunctor[Obj, Arr, Obj, Arr, Obj, Arr, Pair] {
      override def cc: VCategory[Obj, Arr] = category
      override def cd: VCategory[Obj, Arr] = category
      override def ce: VCategory[Obj, Arr] = category
      override def xy[X, Y](implicit ox: Obj[X], oy: Obj[Y]): Obj[Pair[X, Y]] = ()
      override def bimap[X1, X2, Y1, Y2](implicit
          ox1: Obj[X1], ox2: Obj[X2],
          oy1: Obj[Y1], oy2: Obj[Y2]): Arr[X1, X2] => Arr[Y1, Y2] => Arr[Pair[X1, Y1], Pair[X2, Y2]] =
        f => g => xy => (f(xy._1), g(xy._2))
    }

  val monoidal: MonoidalVCategory[Obj, Arr, Pair, Unit] =
    new MonoidalVCategory[Obj, Arr, Pair, Unit] {
      override def c: VCategory[Obj, Arr] = category
      override def tensor: VBifunctor[Obj, Arr, Obj, Arr,Obj, Arr, Pair] = pairBifunctor
      override def id: Obj[Unit] = ()
      override def α[X, Y, Z](implicit ox: Obj[X], oy: Obj[Y], oz: Obj[Z]):
      Arr[Pair[X, Pair[Y, Z]], Pair[Pair[X, Y], Z]] =
        xyz => ((xyz._1, xyz._2._1), xyz._2._2)
      override def α_inv[X, Y, Z](implicit ox: Obj[X], oy: Obj[Y], oz: Obj[Z]):
      Arr[Pair[Pair[X, Y], Z], Pair[X, Pair[Y, Z]]] = xyz => (xyz._1._1, (xyz._1._2, xyz._2))
      override def λ[X](implicit ox: Obj[X]): Arr[Pair[X, Unit], X] = _._1
      override def λ_inv[X](implicit ox: Obj[X]): Arr[X, Pair[X, Unit]] = x => (x, ())
      override def ρ[X](implicit ox: Obj[X]): Arr[Pair[Unit, X], X] = _._2
      override def ρ_inv[X](implicit ox: Obj[X]): Arr[X, Pair[Unit, X]] = x => ((), x)
    }

  val action: StrongMonoidalVAction[Obj, Arr, Pair, Unit, Obj, Arr, Pair] =
    new StrongMonoidalVAction[Obj, Arr, Pair, Unit, Obj, Arr, Pair] {
      override def mc: MonoidalVCategory[Obj, Arr, Pair, Unit] = monoidal
      override def bif: VBifunctor[Obj, Arr, Obj, Arr, Obj, Arr, Pair] = pairBifunctor
      override def c: VCategory[Obj, Arr] = category
      override def unitor[X](implicit ox: Obj[X]): Arr[Pair[Unit, X], X] = _._2
      override def unitorinv[X](implicit ox: Obj[X]): Arr[X, Pair[Unit, X]] = x => ((), x)
      override def multiplicator[X, P, Q](implicit ox: Obj[X], op: Obj[P], oq: Obj[Q]):
          Arr[Pair[P, Pair[Q, X]], Pair[Pair[P, Q], X]] =
        pqx => ((pqx._1, pqx._2._1), pqx._2._2)
      override def multiplicatorinv[X, P, Q](implicit ox: Obj[X], op: Obj[P], oq: Obj[Q]):
          Arr[Pair[Pair[P, Q], X], Pair[P, Pair[Q, X]]] =
        pqx => (pqx._1._1, (pqx._1._2, pqx._2))
    }

  val functionProfunctor: VProfunctor[Obj, Arr, Obj, Arr, Arr] =
    new VProfunctor[Obj, Arr, Obj, Arr, Arr] {
      override def cc: VCategory[Obj, Arr] = category
      override def cd: VCategory[Obj, Arr] = category

      override def dimap[X1, X2, Y1, Y2](
                                          implicit
                                          ox1: Obj[X1],
                                          ox2: Obj[X2],
                                          oy1: Obj[Y1],
                                          oy2: Obj[Y2]
                                        ): Arr[X2, X1] => Arr[Y1, Y2] => Arr[X1, Y1] => Arr[X2, Y2] =
        pre => post => pab => x2 => post(pab(pre(x2)))
    }

  implicit val functionTambara: Tambara[Obj, Arr, Obj, Arr, Obj, Arr, Pair, Unit, Pair, Pair, Arr] =
    new Tambara[Obj, Arr, Obj, Arr, Obj, Arr, Pair, Unit, Pair, Pair, Arr] {
      override def maf: StrongMonoidalVAction[Obj, Arr, Pair, Unit, Obj, Arr, Pair] = action
      override def mag: StrongMonoidalVAction[Obj, Arr, Pair, Unit, Obj, Arr, Pair] = action
      override def pp: VProfunctor[Obj, Arr, Obj, Arr, Arr] = functionProfunctor
      override def tambara[X, Y, W](implicit ox: Obj[X], oy: Obj[Y], ow: Obj[W]):
      Arr[X, Y] => Arr[Pair[W, X], Pair[W, Y]] =
        pab => wx => (wx._1, pab(wx._2))
    }

  type GeneralOptic[A, B, S, T] = Optic[Obj, Arr, Obj, Arr, Obj, Arr, Pair, Unit, Pair, Pair, A, B, S, T]

  def optic[A, B, S, T, R](left: S => Pair[R, A], right: Pair[R, B] => T): GeneralOptic[A, B, S, T] =
    Optic[Obj, Arr, Obj, Arr, Obj, Arr, Pair, Unit, Pair, Pair, A, B, S, T, R](
      amaf = action,
      amag = action,
      aoa = (),
      aos = (),
      aob = (),
      aot = (),
      al = left,
      ar = right,
      aox = ()
    )
}