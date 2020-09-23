
package scalabench

import fastparse._, NoWhitespace._
import org.scalameter.api._

object Main extends Bench.LocalTime {

  def ws[_: P]             = P((" " | "\n").rep())
  def isLatin(c : Char)    = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
  def open[_: P]           = P("(" ~ ws)
  def close[_: P]          = P(")" ~ ws)
  def ident[_: P]          = P(CharPred(isLatin).rep(1) ~ ws)
  def sexp[_: P] : P[Unit] = P((open ~ sexp.rep(1) ~ close) | ident)
  def isDigit(c : Char)    = ('0' <= c && c <= '9')
  def sexpInp              = "(" + "(foo (foo (foo ((bar baza)))))" * 33333 + ")"

  def longw[_: P]          = P("thisisalongkeyword")
  def longws[_: P]         = P((longw ~ ws).rep(1) ~ End)
  def longwsInp            = "thisisalongkeyword   " * 55555

  def numeral[_: P]        = P(CharPred(isDigit).rep(1) ~ ws)
  def comma[_: P]          = P("," ~ ws)
  def numcsv[_: P]         = P(numeral ~ (comma ~ numeral).rep() ~ End)
  def numcsvInp:String     = (1 to 100000).map(n => ",  " + n.toString()).mkString("")

  performance of "sexp" in {
    using(Gen.unit("")) in {
      _ => parse(sexpInp, sexp(_))
    }
  }

  performance of "longws" in {
    using(Gen.unit("")) in {
      _ => parse(longwsInp, longws(_))
    }
  }

  performance of "numcsv" in {
    using(Gen.unit("")) in {
      _ => parse(numcsvInp, numcsv(_))
    }
  }
}

// ::Benchmark sexp::
// Parameters( -> ()): 30.108641 ms

// ::Benchmark longws::
// Parameters( -> ()): 5.65306 ms

// ::Benchmark numcsv::
// Parameters( -> ()): 12.507556 ms
