# String.eq is sound: when it answers True, the two strings are equal.
#
# Base defines String.eq through String.cmp, Char.cmp, U32.cmp and Word.cmp
# but states no such fact, so a proof that learned String.eq(a, b) == True
# could not replace b with a. The proof descends the same ladder as
# comparison.bend: bits, then U32, Char and String.
#
# Import it and rewrite with string_eq_sound(a, b, h) : {a == b : String}.

import Base

def Tag2(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def ff(e: {False{} == True{} : Bool}) -> Empty:
  %e : Tag2(_)
  Unit{}

def bool_eq_sound(a: Bool, b: Bool, h: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, ff(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, ff(h))

def fin_head(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {ab == bb : Bool}:
  match c:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, ff(h))
    case EQ{}:
      bool_eq_sound(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, ff(h))

def fin_tail(ab: Bool, bb: Bool, c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, ff(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, ff(h))

def word_eq_sound(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %fin_head(ab, bb, Word.cmp(p, at, bt), h) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %word_eq_sound(p, at, bt, fin_tail(ab, bb, Word.cmp(p, at, bt), h)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}


def u32_eq_sound(a: U32, b: U32, h: {Cmp.is_eq(U32.cmp(a, b)) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %word_eq_sound(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def char_cmp_c(a: Char, b: Char) -> Cmp:
  match a b:
    case Chr{x} Chr{y}:
      U32.cmp(x, y)

def char_eq_sound(a: Char, b: Char, h: {Cmp.is_eq(char_cmp_c(a, b)) == True{} : Bool}) -> {a == b : Char}:
  match a b:
    case Chr{x} Chr{y}:
      %u32_eq_sound(x, y, h) : {Chr{x} == Chr{_} : Char}
      {==}

def rec_is_eq(h1: Char, h2: Char, rr: (String & String) & Cmp) -> {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}:
  match rr:
    case ((a, b), c):
      {==}

def eq_sym_is(c: Cmp, +d: Cmp, e: {c == d : Cmp}, h: {Cmp.is_eq(c) == True{} : Bool}) -> {Cmp.is_eq(d) == True{} : Bool}:
  %e : {Cmp.is_eq(_) == True{} : Bool}
  h

def step_sound(+x: U32, +y: U32, +t1: String, +t2: String, c: Cmp, ec: {c == U32.cmp(x, y) : Cmp}, h: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))) == True{} : Bool}, ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, ff(h))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, ff(h))
    case EQ{}:
      %u32_eq_sound(x, y, eq_sym_is(EQ{}, U32.cmp(x, y), ec, {==})) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), True{}, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), String.eq(t1, t2), rec_is_eq(Chr{x}, Chr{y}, String.cmp(t1, t2))), h)) : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

def string_eq_sound(a: String, b: String, +h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{x, t}:
      Empty.absurd({SNil{} == SCon{x, t} : String}, ff(h))
    case SCon{x, t} SNil{}:
      Empty.absurd({SCon{x, t} == SNil{} : String}, ff(h))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      step_sound(x, y, t1, t2, U32.cmp(x, y), {==}, h, hh => string_eq_sound(t1, t2, hh))
