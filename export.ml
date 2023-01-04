open Js_of_ocaml
open Toyreals

let q_to_js q =
  object%js
    val num = q.qnum
    val den = q.qden
  end

let q_from_js q =
  {qnum = q##.num; qden = q##.den}

let qi_to_js qs =
  object%js
    val min = q_to_js qs.min
    val max = q_to_js qs.max0
  end

let qi_from_js qs =
  {min = q_from_js qs##.min; max0 = q_from_js qs##.max}

let ri_from_js xs =
  {min = xs##.min; max0 = xs##.max}

let _ =
  Js.export "R"
    (object%js
       method make f = make_Stream (fun i -> qi_from_js (Js.Unsafe.fun_call f [| Js.Unsafe.inject i |]))
       method nth x k = qi_to_js (str_nth k x)
       method _Q2R q = q2R (q_from_js q)
       method _Z2R n = z2R n
       method lt_or_dec_ x y z a = lt_or_dec x y z a
       method compare x y = compare0 x y
       method plus x y = plus x y
       method opp x = opp0 x
       method minus x y = minus x y
       method mult x y = mult x y
       method inv x = inv x
       method div x y = div0 x y
       method nested_RI_int_ f = nested_RI_int (fun i -> ri_from_js (Js.Unsafe.fun_call f [| Js.Unsafe.inject i |]))
       method round x = round x
     end)
