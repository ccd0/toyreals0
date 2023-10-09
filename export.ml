open Js_of_ocaml
open Toyreals

let q_to_js q =
  object%js
    val t = Js.string "Q"
    val num = q.qnum
    val den = q.qden
  end

let q_from_js q =
  {qnum = q##.num; qden = q##.den}

let r_to_js x =
  object%js
    val t = Js.string "R"
    val bounds = x
  end

let r_from_js x =
  x##.bounds

let qi_to_js qs =
  object%js
    val t = Js.string "QI"
    val min = q_to_js qs.min
    val max = q_to_js qs.max0
  end

let qi_from_js qs =
  {min = q_from_js qs##.min; max0 = q_from_js qs##.max}

let ri_from_js xs =
  {min = r_from_js xs##.min; max0 = r_from_js xs##.max}

let frr_from_js f =
  fun x -> r_from_js (Js.Unsafe.fun_call f [| Js.Unsafe.inject (r_to_js x) |])

let _ =
  Js.export "R"
    (object%js
       method make f = r_to_js (make_Stream (fun i -> qi_from_js (Js.Unsafe.fun_call f [| Js.Unsafe.inject i |])))
       method nth x k = qi_to_js (str_nth k (r_from_js x))
       method _Q2R q = r_to_js (q2R (q_from_js q))
       method _Z2R n = r_to_js (z2R n)
       method lt_or_dec_ x y z a = lt_or_dec (r_from_js x) (r_from_js y) (r_from_js z) (r_from_js a)
       method compare x y = compare0 (r_from_js x) (r_from_js y)
       method plus x y = r_to_js (plus (r_from_js x) (r_from_js y))
       method opp x = r_to_js (opp0 (r_from_js x))
       method minus x y = r_to_js (minus (r_from_js x) (r_from_js y))
       method mult x y = r_to_js (mult (r_from_js x) (r_from_js y))
       method inv x = r_to_js (inv (r_from_js x))
       method div x y = r_to_js (div0 (r_from_js x) (r_from_js y))
       method nested_RI_int_ f = r_to_js (nested_RI_int (fun i -> ri_from_js (Js.Unsafe.fun_call f [| Js.Unsafe.inject i |])))
       method round x = round (r_from_js x)
       method piecewise a f g x = r_to_js (piecewise (r_from_js a) (frr_from_js f) (frr_from_js g) (r_from_js x))
       method abs x = r_to_js (abs0 (r_from_js x))
     end)
