import scala.collection.mutable
import scala.util.parsing.combinator.*

import Expr.*
import Typ.*
import Value.*

@main def main() =
  val src = raw"""
    let x = \y.\z. if y then z else z in
    let z = false in
    let f = \a.\b.\c.a b c in
    let id = \x. x in
    let t = id true in
    let ten = id 10 in
    (f id x z, 10)
  """
  val expr = Parser.parseAll(Parser.program, src) match
    case Parser.Success(matched, _) => matched
    case Parser.Failure(msg, _)     => throw Exception(s"Failure: $msg")
    case Parser.Error(msg, _)       => throw Exception(s"Failure: $msg")
  println(s"type: ${expr.typecheck.pretty()}")
  println(s"value: ${expr.eval()}")

val boolCon = TCon("Bool", Seq.empty)
val intCon = TCon("Int", Seq.empty)
// format: off
val prelude = Map(
  "is_zero" -> VNative(intCon ->: boolCon, {
    case VInt(n) => VBool(n == 0)
    case v       => throw TypeError("Expected Int, got $v")
  }),
  "pred" -> VNative(intCon ->: intCon, {
    case VInt(n) => VInt(n - 1)
    case v       => throw TypeError("Expected Int, got $v")
  }),
  "mult" -> VNative(intCon ->: intCon ->: intCon, {
    case VInt(x) => VNative(intCon ->: intCon, {
        case VInt(y) => VInt(x * y)
        case v       => throw TypeError("Expected Int, got $v")
      })
    case v => throw TypeError("Expected Int, got $v")
  }),
)
// format: on

enum Expr:
  case EBool(b: Boolean)
  case EInt(n: Int)
  case EApp(e1: Expr, e2: Expr)
  case ELam(v: String, e: Expr)
  case EVar(v: String)
  case ELet(v: String, e1: Expr, e2: Expr)
  case ERec(v: String, e1: Expr, e2: Expr)
  case EIf(e1: Expr, e2: Expr, e3: Expr)
  case ETup(es: List[Expr])

  override def toString() = this match
    case EBool(b)        => b.toString
    case EInt(n)         => n.toString
    case EApp(e1, e2)    => s"($e1 $e2)"
    case ELam(v, e)      => s"(\\$v. $e)"
    case EVar(v)         => v
    case ELet(v, e1, e2) => s"let $v = $e1 in $e2"
    case ERec(v, e1, e2) => s"rec $v = $e1 in $e2"
    case EIf(e1, e2, e3) => s"if $e1 then $e2 else $e3"
    case ETup(es)        => es.mkString("(", ", ", ")")

  def typecheck: Typ =
    val infer = Infer()
    val t = infer.typecheck(this, prelude.map(_ -> _.getType))
    infer.monomorphize(t).simplifyVars

  def eval(ctx: Map[String, Value] = prelude): Value = this match
    case EBool(b)   => VBool(b)
    case EInt(n)    => VInt(n)
    case EVar(v)    => ctx(v)
    case ELam(v, e) => VLam(ctx, v, e)
    case ETup(es)   => VTup(es.map(_.eval(ctx)))

    case EApp(e1, e2) =>
      val v1 = e1.eval(ctx)
      val v2 = e2.eval(ctx)
      v1(v2)

    case ELet(id, e1, e2) =>
      val v = e1.eval(ctx)
      e2.eval(ctx + (id -> v))

    case ERec(id, e1, e2) =>
      val v = e1.eval(ctx)
      e2.eval(ctx + (id -> v.updateCtx(id, v)))

    case EIf(e1, e2, e3) =>
      e1.eval(ctx) match
        case VBool(true)  => e2.eval(ctx)
        case VBool(false) => e3.eval(ctx)
        case v            => throw TypeError("Expected Bool, got $v")

enum Typ:
  case TCon(name: String, ts: Seq[Typ])
  case TVar(n: Int)

  override def toString() = this match
    case TCon("->", Seq(t1, t2))       => s"($t1 -> $t2)"
    case TCon("()", ts)                => ts.mkString("(", ", ", ")")
    case TCon(name, ts) if ts.nonEmpty => s"($name ${ts.mkString(" ")})"
    case TCon(name, _)                 => name
    case TVar(n) =>
      val primes = n / 26
      val char = (n % 26 + 'a').toChar
      s"?$char${"'" * primes}"

  def pretty(open: String = "", close: String = ""): String = this match
    case TCon("->", Seq(t1 @ TCon("->", _), t2)) =>
      s"$open${t1.pretty("(", ")")} -> ${t2.pretty()}$close"
    case TCon("->", ts) =>
      ts.map(_.pretty()).mkString(open, " -> ", close)
    case TCon("()", ts) => ts.map(_.pretty()).mkString("(", ", ", ")")
    case TCon(name, ts) =>
      if ts.isEmpty then name
      else s"$open$name ${ts.map(_.pretty("(", ")")).mkString(" ")}$close"
    case TVar(_) => s"$this"

  def mapVars(m: Map[Int, Int]): Typ = this match
    case TVar(v)        => TVar(m(v))
    case TCon(name, ts) => TCon(name, ts.map(_.mapVars(m)))

  def simplifyVars = mapVars(getVars.zipWithIndex.toMap)

  def getVars: Set[Int] = this match
    case TVar(v)     => Set(v)
    case TCon(_, ts) => ts.toSet.flatMap(_.getVars)

  def occurs(v: Int): Boolean = this match
    case TVar(v2)    => v == v2
    case TCon(_, ts) => ts.exists(_.occurs(v))

  def ->:(t: Typ) = TCon("->", Seq(t, this))

case class Scheme(val vs: Set[Int], val t: Typ):
  override def toString() =
    if vs.nonEmpty then
      s"forall ${vs.map(TVar(_)).mkString(" ")}. ${t.pretty()}"
    else s"$t"

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
    case _                       => t

  def normalize(t: Typ): Typ = t match
    case TCon(name, ts)          => TCon(name, ts.map(normalize(_)))
    case TVar(v) if g contains v => t
    case TVar(v) if s contains v =>
      s(v) = normalize(s(v))
      s(v)
    case TVar(_) => t

  def updateVar(v: Int, t: Typ) =
    s.put(v, t).foreach(unify(_, t))

  def unify(t1: Typ, t2: Typ): Unit = (t1, t2) match
    case (TCon(n1, ts1), TCon(n2, ts2))
        if n1 == n2 && ts1.length == ts2.length =>
      ts1.zip(ts2).foreach(unify(_, _))
    case (TVar(v1), TVar(v2)) if v1 == v2  => ()
    case (tv @ TVar(v), t) if g contains v => unify(monomorphize(tv), t)
    case (t, tv @ TVar(v)) if g contains v => unify(monomorphize(tv), t)
    case (TVar(v), t) if !t.occurs(v)      => updateVar(v, t)
    case (t, TVar(v)) if !t.occurs(v)      => updateVar(v, t)
    case (t1, t2)                          => throw Exception(s"unification failure: $t1 with $t2")

  def polymorphize(t: Typ) =
    val vs = t.getVars
    if vs.isEmpty then t
    else
      val tv = freshVar
      g(tv.n) = Scheme(vs, t)
      s(tv.n) = t
      tv

  def typecheck(e: Expr, ctx: Map[String, Typ]): Typ = e match
    case EBool(_) => boolCon
    case EInt(_)  => intCon
    case EVar(v)  => normalize(ctx(v))
    case ETup(es) => TCon("()", es.map(typecheck(_, ctx)))

    case EApp(e1, e2) =>
      val tv = freshVar
      unify(typecheck(e1, ctx), typecheck(e2, ctx) ->: tv)
      normalize(tv)

    case ELam(v, e) =>
      val t1 = freshVar
      val t2 = typecheck(e, ctx + (v -> t1))
      normalize(t1 ->: t2)

    case ELet(v, e1, e2) =>
      val t = polymorphize(typecheck(e1, ctx))
      normalize(typecheck(e2, ctx + (v -> t)))

    case ERec(v, e1, e2) =>
      val recv = freshVar
      val t1 = typecheck(e1, ctx + (v -> recv))
      unify(t1, recv)
      val t2 = polymorphize(t1)
      normalize(typecheck(e2, ctx + (v -> t2)))

    case EIf(e1, e2, e3) =>
      unify(typecheck(e1, ctx), boolCon)
      val t = typecheck(e2, ctx)
      unify(t, typecheck(e3, ctx))
      normalize(t)

object Parser extends RegexParsers, PackratParsers:
  override def skipWhitespace = true
  override val whiteSpace = "[ \t\n\r]+".r

  lazy val id: PackratParser[String] =
    not("let" | "rec" | "in" | "if" | "then" | "else" | "true" | "false") ~>
      raw"[a-zA-Z][\w']*".r ^^ { _.toString }
  lazy val atomexpr: PackratParser[Expr] = (
    raw"[\d]+".r ^^ { x => EInt(x.toInt) }
      | raw"true|false".r ^^ { x => EBool(x.toBoolean) }
      | ("let" ~> id <~ "=") ~ expr ~ ("in" ~> expr) ^^ { case id ~ e1 ~ e2 =>
        ELet(id, e1, e2)
      }
      | ("rec" ~> id <~ "=") ~ expr ~ ("in" ~> expr) ^^ { case id ~ e1 ~ e2 =>
        ERec(id, e1, e2)
      }
      | ("if" ~> expr <~ "then") ~ expr ~ ("else" ~> expr) ^^ {
        case e1 ~ e2 ~ e3 => EIf(e1, e2, e3)
      }
      | ("\\" ~> id <~ ".") ~ expr ^^ { case id ~ e =>
        ELam(id, e)
      }
      | id ^^ { EVar(_) }
      | "(" ~> (expr <~ ",").+ ~ expr <~ ",".? <~ ")" ^^ { case es ~ e =>
        ETup(es :+ e)
      }
      | "(" ~> expr <~ ")"
  )
  lazy val expr: PackratParser[Expr] =
    expr ~ atomexpr ^^ { case e1 ~ e2 => EApp(e1, e2) } | atomexpr
  lazy val program: PackratParser[Expr] = phrase(expr)

final class TypeError(msg: String) extends Exception(msg)

enum Value:
  case VLam(var ctx: Map[String, Value], param: String, body: Expr)
  case VNative(t: Typ, f: Value => Value)
  case VInt(n: Int)
  case VBool(b: Boolean)
  case VTup(vs: List[Value])

  def apply(that: Value) = this match
    case VLam(ctx, param, body) => body.eval(ctx + (param -> that))
    case VNative(_, f)          => f(that)
    case _                      => throw TypeError(s"Expected applicable, got $this")

  def updateCtx(k: String, v: Value): Value = this match
    case v @ VLam(_, _, _) =>
      v.ctx = v.ctx.updated(k, v)
      v
    case v => v

  override def toString = this match
    case VLam(_, _, _) => "[lambda]"
    case VNative(_, _) => "[native function]"
    case VInt(n)       => s"$n"
    case VBool(b)      => s"$b"
    case VTup(vs)      => vs.mkString("(", ", ", ")")

  def getType: Typ = this match
    case VBool(_)      => boolCon
    case VInt(_)       => intCon
    case VNative(t, _) => t
    case VTup(vs)      => TCon("()", vs.map(_.getType))
    case VLam(ctx, id, e) =>
      val infer = Infer()
      infer.typecheck(ELam(id, e), ctx.map(_ -> _.getType)).simplifyVars
