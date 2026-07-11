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
}
