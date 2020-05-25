#[macro_use]
extern crate bencher;
#[macro_use]
extern crate nom;

pub use bencher::Bencher;
pub use nom::{
  IResult,
  bytes::complete::{*},
  character::complete::{*},
  sequence::{*},
  branch::{*},
  error::{*}
};

pub fn skip_many1<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, (), E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut i = i.clone();
    match f(i.clone()) {
      Err(nom::Err::Error(err)) =>
	return Err(nom::Err::Error(E::append(i, ErrorKind::Many1, err))),
      Err(e) => return Err(e),
      Ok((i1, _)) => {
        i = i1;

        loop {
          match f(i.clone()) {
            Err(nom::Err::Error(_)) => return Ok((i, ())),
            Err(e) => return Err(e),
            Ok((i1, _)) => {
              if i1 == i {
                return Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Many1)));
              }
              i = i1;
            }
          }
        }
      }
    }
  }
}

pub fn skip_many0<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, (), E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut i = i.clone();
    loop {
      match f(i.clone()) {
        Err(nom::Err::Error(_)) => return Ok((i, ())),
        Err(e) => return Err(e),
        Ok((i1, _)) => {
          if i1 == i {
            return Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Many0)));
          }
          i = i1;
        }
      }
    }
  }
}

mod u8_bench {
  use super::{*};

  named!{eof<&[u8],&[u8],()>, eof!()}

  fn ws(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    take_while(|c| c == (' ' as u8) || c == ('\n' as u8))(i)
  }

  fn open(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(char('('), ws)(i)
  }

  fn close(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(char(')'), ws)(i)
  }

  fn ident(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(alphanumeric1, ws)(i)
  }

  fn sexp(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    alt((preceded(open, preceded(skip_many1(sexp), close)), ident))(i)
  }

  fn src(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(sexp, eof)(i)
  }

  fn longw(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    tag("thisisalongkeyword")(i)
  }

  fn longws(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(skip_many1(preceded(longw, ws)), eof)(i)
  }

  fn numeral(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(take_while1(|c| ('0' as u8) <= c && c <= ('9' as u8)), ws)(i)
  }

  fn numcsv(i : &[u8]) -> IResult<&[u8], &[u8], ()>{
    preceded(numeral, preceded(skip_many0(preceded(char(','), preceded(ws, numeral))), eof))(i)
  }

  pub fn sexp_bench(bench: &mut Bencher) {
    let sexpinp =
      String::from("(") +
      "(foo (foo (foo ((bar baza)))))".repeat(33333).as_str() +
      ")";
    bench.iter (|| {
      src(sexpinp.as_bytes()).is_ok()
    });
  }

  pub fn numcsv_bench(bench: &mut Bencher) {
    let numcsv_inp : String =
      String::from("0")
      + (1..100000).map(|i| String::from(",   ") + i.to_string().as_str())
    		 .collect::<Vec<_>>().join("").as_str();
    bench.iter (|| {
      numcsv(numcsv_inp.as_bytes()).is_ok()
    });
  }

  pub fn longws_bench(bench: &mut Bencher) {
    let longws_inp = "thisisalongkeyword   ".repeat(55555);
    bench.iter (|| {
      longws(longws_inp.as_bytes()).is_ok()
    });
  }
}


mod utf8_bench {

  use super::{*};
  named!{eof<&str, &str, ()>, eof!()}

  fn ws(i : &str) -> IResult<&str, &str, ()>{
    take_while(|c| c == ' ' || c == '\n')(i)
  }

  fn open(i : &str) -> IResult<&str, &str, ()>{
    preceded(char('('), ws)(i)
  }

  fn close(i : &str) -> IResult<&str, &str, ()>{
    preceded(char(')'), ws)(i)
  }

  fn ident(i : &str) -> IResult<&str, &str, ()>{
    preceded(alphanumeric1, ws)(i)
  }

  fn sexp(i : &str) -> IResult<&str, &str, ()>{
    alt((preceded(open, preceded(skip_many1(sexp), close)), ident))(i)
  }

  fn src(i : &str) -> IResult<&str, &str, ()>{
    preceded(sexp, eof)(i)
  }

  fn longw(i : &str) -> IResult<&str, &str, ()>{
    tag("thisisalongkeyword")(i)
  }

  fn longws(i : &str) -> IResult<&str, &str, ()>{
    preceded(skip_many1(preceded(longw, ws)), eof)(i)
  }

  fn numeral(i : &str) -> IResult<&str, &str, ()>{
    preceded(take_while1(|c| '0' <= c && c <= '9'), ws)(i)
  }

  fn numcsv(i : &str) -> IResult<&str, &str, ()>{
    preceded(numeral, preceded(skip_many0(preceded(char(','), preceded(ws, numeral))), eof))(i)
  }

  pub fn sexp_bench(bench: &mut Bencher) {
    let sexpinp =
      String::from("(") +
      "(foo (foo (foo ((bar baza)))))".repeat(33333).as_str() +
      ")";
    bench.iter (|| {
      src(sexpinp.as_str()).is_ok()
    });
  }

  pub fn numcsv_bench(bench: &mut Bencher) {
    let numcsv_inp : String =
      String::from("0")
      + (1..100000).map(|i| String::from(",   ") + i.to_string().as_str())
    		 .collect::<Vec<_>>().join("").as_str();
    bench.iter (|| {
      numcsv(numcsv_inp.as_str()).is_ok()
    });
  }

  pub fn longws_bench(bench: &mut Bencher) {
    let longws_inp = "thisisalongkeyword   ".repeat(55555);
    bench.iter (|| {
      longws(longws_inp.as_str()).is_ok()
    });
  }
}


benchmark_group!(u8_benches, u8_bench::sexp_bench, u8_bench::numcsv_bench, u8_bench::longws_bench);
benchmark_group!(utf8_benches, utf8_bench::sexp_bench, utf8_bench::numcsv_bench, utf8_bench::longws_bench);
benchmark_main!(utf8_benches, u8_benches);
