#[macro_use]
extern crate nom;

use nom::{
  IResult,
  bytes::complete::{*},
  character::complete::{*},
  sequence::{*},
  branch::{*},
  error::{*},
};

use std::time::{Instant};

named!{eof(&str) -> &str, eof!()}

fn skip_many1<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, (), E>
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

fn skip_many0<I, O, E, F>(f: F) -> impl Fn(I) -> IResult<I, (), E>
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
            return Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Many1)));
          }
          i = i1;
        }
      }
    }
  }
}

fn ws(i : &str) -> IResult<&str, &str>{
  take_while(|c| c == ' ' || c == '\n')(i)
}

fn open(i : &str) -> IResult<&str, &str>{
  preceded(char('('), ws)(i)
}

fn close(i : &str) -> IResult<&str, &str>{
  preceded(char(')'), ws)(i)
}

fn ident(i : &str) -> IResult<&str, &str>{
  preceded(alphanumeric1, ws)(i)
}

fn sexp(i : &str) -> IResult<&str, &str>{
  alt((preceded(open, preceded(skip_many1(sexp), close)), ident))(i)
}

fn src(i : &str) -> IResult<&str, &str>{
  preceded(sexp, eof)(i)
}

fn longw(i : &str) -> IResult<&str, &str>{
  tag("thisisalongkeyword")(i)
}

fn longws(i : &str) -> IResult<&str, &str>{
  preceded(skip_many1(preceded(longw, ws)), eof)(i)
}

fn numeral(i : &str) -> IResult<&str, &str>{
  preceded(take_while1(|c| '0' <= c && c <= '9'), ws)(i)
}

fn numcsv(i : &str) -> IResult<&str, &str>{
  preceded(numeral, preceded(skip_many0(preceded(char(','), preceded(ws, numeral))), eof))(i)
}

fn main() {
  let sexpinp =
    String::from("(") +
    "(foo (foo (foo ((bar baza)))))".repeat(33333).as_str() +
    ")";

  let longws_inp = "thisisalongkeyword   ".repeat(55555);

  let numcsv_inp : String =
    String::from("0")
    + (1..100000).map(|i| String::from(",   ") + i.to_string().as_str())
		 .collect::<Vec<_>>().join("").as_str();

  let times = 20;

  let t = Instant::now();
  for _ in 1..times {
    println!("{:?}", src(sexpinp.as_str()).is_ok())
  }
  println!("{:?}", t.elapsed() / times);

  let t = Instant::now();
  for _ in 1..times {
    println!("{:?}", longws(longws_inp.as_str()).is_ok())
  }
  println!("{:?}", t.elapsed() / times);

  let t = Instant::now();
  for _ in 1..times {
    println!("{:?}", numcsv(numcsv_inp.as_str()).is_ok())
  }
  println!("{:?}", t.elapsed() / times);

}
