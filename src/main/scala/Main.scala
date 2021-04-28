import scala.collection.mutable
import scala.util.parsing.combinator._

@main def main() =
  val src = raw"""
    let x = \y. if y then 0 else 1 in
    let z = false in
    x z
  """
  val expr = Parser.parseAll(Parser.program, src) match
    case Parser.Success(matched, _) => matched
    case Parser.Failure(msg, _) => throw Exception(s"Failure: $msg")
    case Parser.Error(msg, _) => throw Exception(s"Failure: $msg")
  println(expr)
  val t = expr.typecheck
  println(t.simplifyVars)

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
    infer.typecheck(this, Map())
import Expr._

enum Typ:
  case TInt
  case TBool
  case TArr(t1: Typ, t2: Typ)
  case TVar(n: Int)

  override def toString() = this match
    case TInt => "int"
    case TBool => "bool"
    case TArr(t1: Typ, t2: Typ) => s"$t1 -> $t2"
    case TVar(n: Int) =>
      val primes = n / 26
      val char = (n % 26 + 'a').toChar
      s"?$char${"'" * primes}"

  def simplifyVars: Typ =
    def simplify(t: Typ, m: Map[Int, Int]): Typ = t match
      case TInt | TBool => t
      case TVar(v) => TVar(m(v))
      case TArr(t1, t2) => TArr(simplify(t1, m), simplify(t2, m))
    val m = this.getVars.zipWithIndex.toMap
    simplify(this, m)

  def getVars: Set[Int] = this match
    case TInt | TBool => Set()
    case TVar(v) => Set(v)
    case TArr(t1, t2) => t1.getVars ++ t2.getVars

  def occurs(v: Int): Boolean = this match
    case TInt | TBool => false
    case TVar(v2) => v == v2
    case TArr(t1, t2) => t1.occurs(v) || t2.occurs(v)
import Typ._

final class Infer:
  private val s: mutable.Map[Int, Typ] = mutable.Map()
  private var varCount = 0

  def freshVar(): Typ =
    val v = varCount
    varCount += 1
    TVar(v)

  def normalize(t: Typ): Typ = t match
    case TInt | TBool => t
    case TVar(v) => s.get(v).map(normalize).getOrElse(t)
    case TArr(t1, t2) => TArr(normalize(t1), normalize(t2))

  def updateVar(v: Int, t: Typ) =
    s.put(v, t).foreach(unify(_, t))

  def unify(t1: Typ, t2: Typ): Unit =
    (normalize(t1), normalize(t2)) match
      case (TInt, TInt) | (TBool, TBool) => ()
      case (TVar(v1), TVar(v2)) if v1 == v2 => ()
      case (TVar(v), t) if !t.occurs(v) => updateVar(v, t)
      case (t, TVar(v)) if !t.occurs(v) => updateVar(v, t)
      case (TArr(l1, r1), TArr(l2, r2)) => unify(l1, l2); unify(r1, r2)
      case (t1, t2) => throw Exception(s"unification failure: $t1 with $t2")

  def typecheck(e: Expr, ctx: Map[String, Typ]): Typ = e match
    case EBool(_) => TBool
    case EInt(_) => TInt
    case EApp(e1, e2) =>
      val t1 = typecheck(e1, ctx)
      val t2 = typecheck(e2, ctx)
      val t3 = freshVar()
      unify(t1, TArr(t2, t3))
      normalize(t3)
    case ELam(v, e) =>
      val t1 = freshVar()
      val t2 = typecheck(e, ctx + (v -> t1))
      TArr(t1, normalize(t2))
    case EVar(v) => ctx(v)
    case ELet(v, e1, e2) =>
      val t1 = typecheck(e1, ctx)
      val t2 = typecheck(e2, ctx + (v -> t1))
      normalize(t2)
    case EIf(e1, e2, e3) =>
      val t1 = typecheck(e1, ctx)
      val t2 = typecheck(e2, ctx)
      val t3 = typecheck(e3, ctx)
      unify(t1, TBool)
      unify(t2, t3)
      normalize(t2)

object Parser extends RegexParsers, PackratParsers:
  override def skipWhitespace = true
  override val whiteSpace = "[ \t\n\r]+".r

  lazy val id: PackratParser[String] =
    not("let" | "in" | "if" | "then" | "else") ~>
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
