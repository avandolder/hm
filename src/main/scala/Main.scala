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
  val (s, t) = expr.typecheck(Map())
  println(simplifyVars(normalize(s, t)))

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
import Typ._

type Subst = Map[Int, Typ]

def occurs(v: Int, t: Typ): Boolean = t match
  case TInt | TBool => false
  case TVar(v2) => v == v2
  case TArr(t1, t2) => occurs(v, t1) || occurs(v, t2)

def getVars(t: Typ): Set[Int] = t match
  case TInt | TBool => Set()
  case TVar(v) => Set(v)
  case TArr(t1, t2) => getVars(t1) ++ getVars(t2)

def normalize(s: Subst, t: Typ): Typ = t match
  case TInt | TBool => t
  case TVar(v) => s.get(v).map(normalize(s, _)).getOrElse(t)
  case TArr(t1, t2) => TArr(normalize(s, t1), normalize(s, t2))

def simplifyVars(t: Typ): Typ =
  def simplify(t: Typ, m: Map[Int, Int]): Typ = t match
    case TInt | TBool => t
    case TVar(v) => TVar(m(v))
    case TArr(t1, t2) => TArr(simplify(t1, m), simplify(t2, m))
  val m = getVars(t).zipWithIndex.toMap
  simplify(t, m)

def merge(s1: Subst, s2: Subst): Subst =
  val s = s1.keySet
    .intersect(s2.keySet)
    .foldLeft(Map())((s: Subst, v) => unify(s, s1(v), s2(v)))
  s1 ++ s2 ++ s

def unify(s: Subst, t1: Typ, t2: Typ): Subst =
  (normalize(s, t1), normalize(s, t2)) match
    case (TInt, TInt) | (TBool, TBool) => s
    case (TVar(v1), TVar(v2)) if v1 == v2 => s
    case (TVar(v), t) if !occurs(v, t) => s + (v -> t)
    case (t, TVar(v)) if !occurs(v, t) => s + (v -> t)
    case (TArr(l1, r1), TArr(l2, r2)) =>
      val s1 = unify(s, l1, l2)
      val s2 = unify(s, r1, r2)
      merge(s1, s2)
    case (t1, t2) => throw Exception(s"unification failure: $t1 with $t2")

var varCount = 0
def freshVar(): Typ =
  val v = varCount
  varCount += 1
  TVar(v)

extension (e: Expr) def typecheck(ctx: Map[String, Typ]): (Subst, Typ) = e match
  case EBool(_) => (Map(), TBool)
  case EInt(_) => (Map(), TInt)
  case EApp(e1, e2) =>
    val (s1, t1) = e1.typecheck(ctx)
    val (s2, t2) = e2.typecheck(ctx)
    val t3 = freshVar()
    val s = unify(merge(s1, s2), t1, TArr(t2, t3))
    (s, normalize(s, t3))
  case ELam(v, e) =>
    val t1 = freshVar()
    val (s, t2) = e.typecheck(ctx + (v -> t1))
    (s, TArr(t1, normalize(s, t2)))
  case EVar(v) => (Map(), ctx(v))
  case ELet(v, e1, e2) =>
    val (s1, t1) = e1.typecheck(ctx)
    val (s2, t2) = e2.typecheck(ctx + (v -> t1))
    val s = merge(s1, s2)
    (s, normalize(s, t2))
  case EIf(e1, e2, e3) =>
    val (s1, t1) = e1.typecheck(ctx)
    val (s2, t2) = e2.typecheck(ctx)
    val (s3, t3) = e3.typecheck(ctx)
    val s4 = unify(s1, t1, TBool)
    val s5 = unify(merge(s2, s3), t2, t3)
    val s = merge(s4, s5)
    (s, normalize(s, t2))

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
