import scala.collection.mutable
import scala.util.parsing.combinator._

import Expr._
import Typ._

@main def main() =
  val src = raw"""
    let x = \y.\z. if y then z else z in
    let z = false in
    let f = \a.\b.\c.a b c in
    let id = \x. x in
    let t = id true in
    let ten = id 10 in
    f id x z
  """
  val expr = Parser.parseAll(Parser.program, src) match
    case Parser.Success(matched, _) => matched
    case Parser.Failure(msg, _) => throw Exception(s"Failure: $msg")
    case Parser.Error(msg, _) => throw Exception(s"Failure: $msg")
  println(expr.typecheck.pretty())

enum Expr:
  case EBool(b: Boolean)
  case EInt(n: Int)
  case EApp(e1: Expr, e2: Expr)
  case ELam(v: String, e: Expr)
  case EVar(v: String)
  case ELet(v: String, e1: Expr, e2: Expr)
  case EIf(e1: Expr, e2: Expr, e3: Expr)

  override def toString() = this match
    case EBool(b) => b.toString
    case EInt(n) => n.toString
    case EApp(e1, e2) => s"($e1 $e2)"
    case ELam(v, e) => s"(\\$v. $e)"
    case EVar(v) => v
    case ELet(v, e1, e2) => s"let $v = $e1 in $e2"
    case EIf(e1, e2, e3) => s"if $e1 then $e2 else $e3"

  def typecheck: Typ =
    val infer = Infer()
    infer.monomorphize(infer.typecheck(this, Map())).simplifyVars

enum Typ:
  case TCon(name: String, ts: Seq[Typ])
  case TVar(n: Int)

  override def toString() = this match
    case TCon("->", Seq(t1, t2)) => s"($t1 -> $t2)"
    case TCon(name, ts) if ts.nonEmpty => s"$name ${ts.mkString(" ")}"
    case TCon(name, _) => name
    case TVar(n) =>
      val primes = n / 26
      val char = (n % 26 + 'a').toChar
      s"?$char${"'" * primes}"

  def pretty(nested: Boolean = false): String = this match
    case TCon("->", Seq(t1 @ TCon("->", _), t2)) if nested =>
      s"(${t1.pretty(true)} -> ${t2.pretty(false)})"
    case TCon("->", Seq(t1 @ TCon("->", _), t2)) =>
      s"${t1.pretty(true)} -> ${t2.pretty(false)}"
    case TCon("->", ts) if nested =>
      ts.map(_.pretty(false)).mkString("(", " -> ", ")")
    case TCon("->", ts) =>
      ts.map(_.pretty(false)).mkString(" -> ")
    case TCon(name, ts) if ts.isEmpty => name
    case TCon(name, ts) if nested =>
      s"($name ${ts.map(_.pretty(true)).mkString(" ")})"
    case TCon(name, ts) =>
      s"$name ${ts.map(_.pretty(true)).mkString(" ")}"
    case TVar(_) => this.toString

  def mapVars(m: Map[Int, Int]): Typ = this match
    case TVar(v) => TVar(m(v))
    case TCon(name, ts) => TCon(name, ts.map(_.mapVars(m)))

  def simplifyVars: Typ = mapVars(getVars.zipWithIndex.toMap)

  def getVars: Set[Int] = this match
    case TVar(v) => Set(v)
    case TCon(_, ts) => ts.toSet.flatMap(_.getVars)

  def occurs(v: Int): Boolean = this match
    case TVar(v2) => v == v2
    case TCon(_, ts) => ts.exists(_.occurs(v))

val BoolCon = TCon("Bool", Seq.empty)
val IntCon = TCon("Int", Seq.empty)

case class Scheme(val vs: Set[Int], val t: Typ):
  override def toString() =
    if vs.nonEmpty then
      s"forall ${vs.map(TVar(_)).mkString(" ")}. ${t.pretty()}"
    else
      s"$t"

final class Infer:
  private val s: mutable.Map[Int, Typ] = mutable.Map()
  private val g: mutable.Map[Int, Scheme] = mutable.Map()
  private var varCount = 0

  def freshVar: TVar =
    val v = varCount
    varCount += 1
    TVar(v)

  def freshenVars(t: Typ): Typ =
    t.mapVars(t.getVars.map(_ -> freshVar.n).toMap)

  def monomorphize(t: Typ): Typ = t match
    case TVar(v) if g contains v => freshenVars(g(v).t)
    case _ => t

  def normalize(t: Typ): Typ = t match
    case TCon(name, ts) => TCon(name, ts.map(normalize(_)))
    case TVar(v) if g contains v => t
    case TVar(v) if s contains v =>
      s(v) = normalize(s(v))
      s(v)
    case TVar(_) => t

  def updateVar(v: Int, t: Typ) =
    s.put(v, t).foreach(unify(_, t))

  def unify(t1: Typ, t2: Typ): Unit = (t1, t2) match
    case (TCon(n1, ts1), TCon(n2, ts2)) if n1 == n2 => ts1.zip(ts2).foreach(unify(_, _))
    case (TVar(v1), TVar(v2)) if v1 == v2 => ()
    case (tv @ TVar(v), t) if g contains v => unify(monomorphize(tv), t)
    case (t, tv @ TVar(v)) if g contains v => unify(monomorphize(tv), t)
    case (TVar(v), t) if !t.occurs(v) => updateVar(v, t)
    case (t, TVar(v)) if !t.occurs(v) => updateVar(v, t)
    case (t1, t2) => throw Exception(s"unification failure: $t1 with $t2")

  def typecheck(e: Expr, ctx: Map[String, Typ]): Typ = e match
    case EBool(_) => BoolCon
    case EInt(_) => IntCon
    case EVar(v) => ctx(v)

    case EApp(e1, e2) =>
      val t1 = typecheck(e1, ctx)
      val t2 = typecheck(e2, ctx)
      val t3 = freshVar
      unify(t1, TCon("->", Seq(t2, t3)))
      normalize(t3)

    case ELam(v, e) =>
      val t1 = freshVar
      val t2 = typecheck(e, ctx + (v -> t1))
      normalize(TCon("->", Seq(t1, t2)))

    case ELet(v, e1, e2) =>
      val t1 = typecheck(e1, ctx)
      val vs = t1.getVars
      val t2 =
        if vs.nonEmpty then
          val tv = freshVar
          g(tv.n) = Scheme(vs, t1)
          s(tv.n) = t1
          tv
        else
          t1
      normalize(typecheck(e2, ctx + (v -> t2)))

    case EIf(e1, e2, e3) =>
      val t1 = typecheck(e1, ctx)
      val t2 = typecheck(e2, ctx)
      val t3 = typecheck(e3, ctx)
      unify(t1, BoolCon)
      unify(t2, t3)
      normalize(t2)

object Parser extends RegexParsers, PackratParsers:
  override def skipWhitespace = true
  override val whiteSpace = "[ \t\n\r]+".r

  lazy val id: PackratParser[String] =
    not("let" | "in" | "if" | "then" | "else" | "true" | "false") ~>
    raw"[a-zA-Z][\w']*".r ^^ { _.toString }
  lazy val atomexpr: PackratParser[Expr] = (
    raw"[\d]+".r ^^ { x => EInt(x.toInt) }
    | raw"true|false".r ^^ { x => EBool(x.toBoolean) }
    | ("let" ~> id <~ "=") ~ expr ~ ("in" ~> expr) ^^ {
        case id ~ e1 ~ e2 => ELet(id, e1, e2)
      }
    | ("if" ~> expr <~ "then") ~ expr ~ ("else" ~> expr) ^^ {
        case e1 ~ e2 ~ e3 => EIf(e1, e2, e3)
      }
    | ("\\" ~> id <~ ".") ~ expr ^^ {
        case id ~ e => ELam(id, e)
      }
    | id ^^ { EVar(_) }
    | "(" ~> expr <~ ")"
  )
  lazy val expr: PackratParser[Expr] =
    expr ~ atomexpr ^^ { case e1 ~ e2 => EApp(e1, e2) } | atomexpr
  lazy val program: PackratParser[Expr] = phrase(expr)
