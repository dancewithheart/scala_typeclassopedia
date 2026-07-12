package educational.category_theory.two.enriched

/**

Haskell
type ProfOptic   objc c objd d objm m o i f g a b s t = forall p .
     ( Tambara objc c objd d objm m o i f g p
     , MonoidalAction objm m o i objc c f
     , MonoidalAction objm m o i objd d g
     , objc a , objd b , objc s , objd t
     ) => p a b -> p s t
 */
trait ProfOptic[
  OBJC[_], C[_,_],
  OBJD[_], D[_,_],
  OBJM[_], M[_,_],
  O[_,_], I,
  F[_,_], G[_,_],
  A, B, S, T] {

  def run[P[_,_]](pab: P[A, B])(implicit
    TP: Tambara[OBJC, C, OBJD, D,OBJM, M, O, I, F, G, P]
  ): P[S,T]
}

object ExistentialAndProfunctorOptics {
  /**
  Transforms an existential optic into its profunctor representation. This is
  one side of a Yoneda embedding.

  Haskell:
   ex2prof :: forall objc c objd d objm m o i f g a b s t .
      Optic     objc c objd d objm m o i f g a b s t
      -> ProfOptic objc c objd d objm m o i f g a b s t
   ex2prof (Optic l r) =
      dimap @objc @c @objd @d l r .
      tambara @objc @c @objd @d @objm @m @o @i

   The conversion has exactly two steps:
   1. Use tambara to lift P[A, B] through the residual action.
   2. Use dimap with the two legs of the existential optic.

   P[A,B]
   -- tambara[X] --> P[F[X,A], G[X,B]]
   -- dimap(l,r) --> P[S,T]

   */
  def ex2prof[OBJC[_], C[_,_], OBJD[_], D[_,_],OBJM[_], M[_,_], O[_,_], I,F[_,_], G[_,_],A, B, S, T](
     optic: Optic[OBJC, C, OBJD, D, OBJM, M, O, I, F, G, A, B, S, T]
   ): ProfOptic[OBJC, C, OBJD, D,OBJM, M, O, I,F, G, A, B, S, T] =
    new ProfOptic[OBJC, C, OBJD, D, OBJM, M, O, I, F, G, A, B, S, T] {
      def run[P[_, _]](pab: P[A, B])(implicit
                       TP: Tambara[ OBJC, C, OBJD, D,OBJM, M, O, I,F, G, P]): P[S, T] = {
        val lifted: P[F[optic.X, A], G[optic.X, B]] =
          TP.tambara[A, B, optic.X](optic.oa,optic.ob,optic.ox)(pab)
        val ofa: OBJC[F[optic.X, A]] =
          TP.maf.bif.xy[optic.X, A](optic.ox,optic.oa)
        val ogb: OBJD[G[optic.X, B]] =
          TP.mag.bif.xy[optic.X, B](optic.ox,optic.ob)

        TP.pp
          .dimap[F[optic.X, A], S, G[optic.X, B], T](
            ofa,
            optic.os,
            ogb,
            optic.ot)(optic.l)(optic.r)(lifted)
      }
    }

  def prof2ex[
    OBJC[_], C[_, _],
    OBJD[_], D[_, _],
    OBJM[_], M[_, _],
    O[_, _], I,
    F[_, _], G[_, _],
    A, B, S, T
  ](
     optic: ProfOptic[
       OBJC, C, OBJD, D,
       OBJM, M, O, I,
       F, G, A, B, S, T
     ]
   )(
     actionF: StrongMonoidalVAction[OBJM, M, O, I, OBJC, C, F],
     actionG: StrongMonoidalVAction[OBJM, M, O, I, OBJD, D, G],
     oa: OBJC[A],
     ob: OBJD[B]
   ): Optic[
    OBJC, C, OBJD, D,
    OBJM, M, O, I,
    F, G, A, B, S, T
  ] = {

    type Repr[X, Y] = Optic[
      OBJC, C, OBJD, D,
      OBJM, M, O, I,
      F, G, A, B, X, Y
    ]

    // Profunctor instance for fixed-focus optics
    val reprProfunctor: VProfunctor[OBJC, C, OBJD, D, Repr] =
      new VProfunctor[OBJC, C, OBJD, D, Repr] {
        override def cc: VCategory[OBJC, C] = actionF.c
        override def cd: VCategory[OBJD, D] = actionG.c
        override def dimap[X1, X2, Y1, Y2](implicit
          ox1: OBJC[X1],
          ox2: OBJC[X2],
          oy1: OBJD[Y1],
          oy2: OBJD[Y2]
        ): C[X2, X1] => D[Y1, Y2] => Repr[X1, Y1] => Repr[X2, Y2] =
          pre => post => current => {
            type R = current.X
            val or: OBJM[R] = current.ox
            val grb: OBJD[G[R, B]] = actionG.bif.xy[R, B](or, current.ob)
            val newLeft: C[X2, F[R, A]] =
              actionF.c.comp[X2, X1, F[R, A]](ox2)(current.l)(pre)
            val newRight: D[G[R, B], Y2] =
              actionG.c.comp[G[R, B], Y1, Y2](grb)(post)(current.r)
            val result: Repr[X2, Y2] =
              Optic(
                amaf = actionF,
                amag = actionG,
                aoa = current.oa,
                aos = ox2,
                aob = current.ob,
                aot = oy2,
                al = newLeft,
                ar = newRight,
                aox = or
              )
            result
          }
      }

    // Tambara instance for fixed-focus optics
    implicit val reprTambara: Tambara[OBJC, C, OBJD, D, OBJM, M, O, I, F, G, Repr] =
      new Tambara[OBJC, C, OBJD, D, OBJM, M, O, I, F, G, Repr] {
        override def maf: StrongMonoidalVAction[OBJM, M, O, I, OBJC, C, F] = actionF
        override def mag: StrongMonoidalVAction[OBJM, M, O, I, OBJD, D, G] = actionG
        override def pp: VProfunctor[OBJC, C, OBJD, D, Repr] = reprProfunctor
        override def tambara[X, Y, W](implicit
           ox: OBJC[X],
           oy: OBJD[Y],
           ow: OBJM[W]
         ): Repr[X, Y] => Repr[F[W, X], G[W, Y]] =
          current => {
            type R = current.X
            val or: OBJM[R] = current.ox
            val combinedResidual: OBJM[O[W, R]] = actionF.mc.tensor.xy[W, R](ow, or)
            val fra: OBJC[F[R, A]] = actionF.bif.xy[R, A](or, current.oa)
            val grb: OBJD[G[R, B]] = actionG.bif.xy[R, B](or, current.ob)
            val fwx: OBJC[F[W, X]] = actionF.bif.xy[W, X](ow, ox)
            val gwy: OBJD[G[W, Y]] = actionG.bif.xy[W, Y](ow, oy)
            val idW: M[W, W] = actionF.mc.c.unit[W](ow)
            val mappedLeft: C[F[W, X], F[W, F[R, A]]] =
              actionF.bif.bimap[W, W, X, F[R, A]](ow, ow, ox, fra)(idW)(current.l)
            val multipliedLeft: C[F[W, F[R, A]], F[O[W, R], A]] =
              actionF.multiplicator[A, W, R](current.oa, ow, or)
            val newLeft: C[F[W, X], F[O[W, R], A]] =
              actionF.c.comp[F[W, X], F[W, F[R, A]], F[O[W, R], A]](fwx)(
                  multipliedLeft)(mappedLeft)
            val multipliedRight: D[G[O[W, R], B], G[W, G[R, B]]] =
              actionG.multiplicatorinv[B, W, R](current.ob, ow, or)
            val mappedRight: D[G[W, G[R, B]], G[W, Y]] =
              actionG.bif.bimap[W, W, G[R, B], Y](ow, ow, grb, oy)(idW)(current.r)
            val gCombinedB: OBJD[G[O[W, R], B]] =
              actionG.bif.xy[O[W, R], B](combinedResidual, current.ob)
            val newRight: D[G[O[W, R], B], G[W, Y]] =
              actionG.c
                .comp[G[O[W, R], B], G[W, G[R, B]], G[W, Y]](gCombinedB)(
                  mappedRight
                )(multipliedRight)
            val result: Repr[F[W, X], G[W, Y]] =
              Optic(
                amaf = actionF,
                amag = actionG,
                aoa = current.oa,
                aos = fwx,
                aob = current.ob,
                aot = gwy,
                al = newLeft,
                ar = newRight,
                aox = combinedResidual
              )
            result
          }
      }

    // identity optic
    val identity: Repr[A, B] =
      Optic[OBJC, C, OBJD, D, OBJM, M, O, I, F, G, A, B, A, B, I](
        amaf = actionF,
        amag = actionG,
        aoa = oa,
        aos = oa,
        aob = ob,
        aot = ob,
        al = actionF.unitorinv[A](oa),
        ar = actionG.unitor[B](ob),
        aox = actionF.mc.id
      )

    optic.run[Repr](identity)
  }
}
