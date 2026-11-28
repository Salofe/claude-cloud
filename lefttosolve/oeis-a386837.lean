import OMAStatements.S_oeis_a386837

/-!
Proof of Mathar's order-3 recurrence for A386837,
a(n) = Sum_{k=0..n} C(4n+2,k) C(4n-k-1,n-k), by creative telescoping (a Zeilberger certificate,
found by computer algebra and checked here).

For `N ≥ 1` and `k ≤ N` the summand is the hypergeometric term
  `F(N, k) = (4N+2)! / (k! (N-k)! (3N-1)! (4N+2-k)(4N+1-k)(4N-k))`
(`term_eq`); set `F(N, k) = 0` for `k > N` (`f`). Its ratios are rational functions,
`F(N, k+1) = F(N, k) sg(N, k)` and `F(N-1, k) = F(N, k) rh(N, k)` (`f_succ`, `f_pred`), for every
`k`, both sides vanishing at the boundary. With `x = n ≥ 5` and the certificate
`Rc(x, k) = k Qp(x, k) / (Dn(x) (4x-1-k)(4x-2-k)...(4x-11-k))`, where `Qp` is an explicit
polynomial (of degree 13 in `k`) and `Dn(x) = 32x(2x-1)(2x+1)(4x-5)(4x-3)(4x-1)(4x+1)`, the
identity of rational functions (`key`, all denominators nonzero for `0 ≤ k ≤ x`)
  `c0 + c1 rh(x,k) + c2 rh(x,k) rh(x-1,k) + c3 rh(x,k) rh(x-1,k) rh(x-2,k)
     = Rc(x,k+1) sg(x,k) - Rc(x,k)`
gives, with `G k = Rc(n,k) F(n,k)`,
  `c0 F(n,k) + c1 F(n-1,k) + c2 F(n-2,k) + c3 F(n-3,k) = G (k+1) - G k`   for `0 ≤ k ≤ n`.
Summing over `k = 0..n` telescopes to `G (n+1) - G 0 = 0`, which is the recurrence for `n ≥ 5`;
the cases `n = 3, 4` are direct computations.
-/

namespace OMA.Helpers

open OMA.S_oeis_a386837 Finset

/-- The ratio `F(n, k+1) / F(n, k)`. -/
noncomputable def sg (x y : ℚ) : ℚ := (x - y) * (4 * x + 2 - y) / ((y + 1) * (4 * x - 1 - y))

/-- The ratio `F(n-1, k) / F(n, k)`. -/
noncomputable def rh (x y : ℚ) : ℚ :=
  (x - y) * (3 * x - 1) * (3 * x - 2) * (3 * x - 3) * (4 * x + 2 - y) * (4 * x + 1 - y) * (4 * x - y) /
    ((4 * x + 2) * (4 * x + 1) * (4 * x) * (4 * x - 1) * (4 * x - 2 - y) * (4 * x - 3 - y) *
      (4 * x - 4 - y))

/-- `rh (x - 0) y`, expanded. -/
noncomputable def rhA (x y : ℚ) : ℚ :=
  (x - y) * (3 * x - 1) * (3 * x - 2) * (3 * x - 3) * (4 * x + 2 - y) * (4 * x + 1 - y) * (4 * x - y) /
    ((4 * x + 2) * (4 * x + 1) * (4 * x) * (4 * x - 1) * (4 * x - 2 - y) * (4 * x - 3 - y) * (4 * x - 4 - y))

/-- `rh (x - 1) y`, expanded. -/
noncomputable def rhB (x y : ℚ) : ℚ :=
  (x - 1 - y) * (3 * x - 4) * (3 * x - 5) * (3 * x - 6) * (4 * x - 2 - y) * (4 * x - 3 - y) * (4 * x - 4 - y) /
    ((4 * x - 2) * (4 * x - 3) * (4 * x - 4) * (4 * x - 5) * (4 * x - 6 - y) * (4 * x - 7 - y) * (4 * x - 8 - y))

/-- `rh (x - 2) y`, expanded. -/
noncomputable def rhC (x y : ℚ) : ℚ :=
  (x - 2 - y) * (3 * x - 7) * (3 * x - 8) * (3 * x - 9) * (4 * x - 6 - y) * (4 * x - 7 - y) * (4 * x - 8 - y) /
    ((4 * x - 6) * (4 * x - 7) * (4 * x - 8) * (4 * x - 9) * (4 * x - 10 - y) * (4 * x - 11 - y) * (4 * x - 12 - y))

/-- Coefficient of `y ^ 0` in the numerator of the certificate. -/
def q0 (x : ℚ) : ℚ :=
  -513426565632098304 * x ^ 21 + 12708836635139112960 * x ^ 20 - 145376454616968855552 * x ^ 19 + 1017327996011876057088 * x ^ 18 - 4858180248884446740480 * x ^ 17 + 16715857412738177298432 * x ^ 16 - 42624177813291929352192 * x ^ 15 + 81494344629810438082560 * x ^ 14 - 116533229378350274082816 * x ^ 13 + 122077339884736213454592 * x ^ 12 - 88469087332428316694400 * x ^ 11 + 36815684277693219935616 * x ^ 10 + 650685902771423190528 * x ^ 9 - 11677331883921421455360 * x ^ 8 + 7435852495260971839104 * x ^ 7 - 2072223275521700417664 * x ^ 6 + 68361650797580643072 * x ^ 5 + 120813854228567294976 * x ^ 4 - 31433899036715458560 * x ^ 3 + 2580194606984755200 * x ^ 2 - 3431711162880000 * x

/-- Coefficient of `y ^ 1` in the numerator of the certificate. -/
def q1 (x : ℚ) : ℚ :=
  1885237433852755968 * x ^ 20 - 45328558266159464448 * x ^ 19 + 503486473567277678592 * x ^ 18 - 3419580658766356217856 * x ^ 17 + 15840281897703401754624 * x ^ 16 - 52840528160263917238272 * x ^ 15 + 130587118046582644944384 * x ^ 14 - 242020806762312501249792 * x ^ 13 + 335919053893062496240512 * x ^ 12 - 342999638541567300474816 * x ^ 11 + 245379265967574785215488 * x ^ 10 - 106320703759078526173248 * x ^ 9 + 8774531462018323125696 * x ^ 8 + 21443681994761061829056 * x ^ 7 - 14611754418206911371264 * x ^ 6 + 4222646231102095548096 * x ^ 5 - 300139005061432895040 * x ^ 4 - 151444109231484266880 * x ^ 3 + 41136220420252519680 * x ^ 2 - 3164472634580928000 * x + 686342232576000

/-- Coefficient of `y ^ 2` in the numerator of the certificate. -/
def q2 (x : ℚ) : ℚ :=
  -3107002161617436672 * x ^ 19 + 72192842083418701824 * x ^ 18 - 774036774438330826752 * x ^ 17 + 5068034983310001340416 * x ^ 16 - 22601194024533318036480 * x ^ 15 + 72486646545817102887168 * x ^ 14 - 172036548422497666230528 * x ^ 13 + 306013572416142912164352 * x ^ 12 - 407923778090484308492640 * x ^ 11 + 401565998368753786143984 * x ^ 10 - 280610206546730324422488 * x ^ 9 + 125130834787095108047928 * x ^ 8 - 21392997085736378173680 * x ^ 7 - 12221313156934552191552 * x ^ 6 + 9837536692189423149384 * x ^ 5 - 2970305597757835375560 * x ^ 4 + 339267037987121071968 * x ^ 3 + 29317430443607360352 * x ^ 2 - 10543569409037773440 * x + 629857831721817600

/-- Coefficient of `y ^ 3` in the numerator of the certificate. -/
def q3 (x : ℚ) : ℚ :=
  3062026494973771776 * x ^ 18 - 68484615478013657088 * x ^ 17 + 705494582496212484096 * x ^ 16 - 4429373394347081957376 * x ^ 15 + 18902008873902758890752 * x ^ 14 - 57891462071865187336704 * x ^ 13 + 130956179885546110771392 * x ^ 12 - 221690660160318673369248 * x ^ 11 + 281125893242696484908856 * x ^ 10 - 263865312497608503478644 * x ^ 9 + 177575661936810320827476 * x ^ 8 - 79306467944651420366304 * x ^ 7 + 17991440010249151267584 * x ^ 6 + 2195646988020912613980 * x ^ 5 - 3015421842486650639772 * x ^ 4 + 929462767188733347960 * x ^ 3 - 120685048311390141936 * x ^ 2 + 2460237673249558368 * x + 556932694991541120

/-- Coefficient of `y ^ 4` in the numerator of the certificate. -/
def q4 (x : ℚ) : ℚ :=
  -2021265632513064960 * x ^ 17 + 43370179502406819840 * x ^ 16 - 427518939648720125952 * x ^ 15 + 2561398518495937195008 * x ^ 14 - 10401188550461673931584 * x ^ 13 + 30225771712881745462800 * x ^ 12 - 64690529664463574051160 * x ^ 11 + 103341344000202270200160 * x ^ 10 - 123423455616880317921834 * x ^ 9 + 109105028518631730260910 * x ^ 8 - 69543872187324333920616 * x ^ 7 + 30172771600639101502332 * x ^ 6 - 7629954408053765236722 * x ^ 5 + 361634130068694964494 * x ^ 4 + 427244731810246163532 * x ^ 3 - 135462272026057677576 * x ^ 2 + 15993138680182116144 * x - 554240644939563840

/-- Coefficient of `y ^ 5` in the numerator of the certificate. -/
def q5 (x : ℚ) : ℚ :=
  946147743550513152 * x ^ 16 - 19417999491718410240 * x ^ 15 + 182453714167560265728 * x ^ 14 - 1038195430195046478336 * x ^ 13 + 3988838270567723568048 * x ^ 12 - 10924479929103007971672 * x ^ 11 + 21946529709194018985846 * x ^ 10 - 32772563575098222639303 * x ^ 9 + 36443845517229026331555 * x ^ 8 - 29904716527019710498416 * x ^ 7 + 17698508739391517831940 * x ^ 6 - 7216661093574387602091 * x ^ 5 + 1834002677666929686279 * x ^ 4 - 207094766712630510558 * x ^ 3 - 19565329903721309220 * x ^ 2 + 8220692891582636904 * x - 650367722236134240

/-- Coefficient of `y ^ 6` in the numerator of the certificate. -/
def q6 (x : ℚ) : ℚ :=
  -323643192823425024 * x ^ 15 + 6335162874503069184 * x ^ 14 - 56520911946531068928 * x ^ 13 + 303932583062373803904 * x ^ 12 - 1098044641084307723172 * x ^ 11 + 2812933161159263329527 * x ^ 10 - 5255965195436710926270 * x ^ 9 + 7255213494832492602165 * x ^ 8 - 7407902892908364233607 * x ^ 7 + 5541723771622828747371 * x ^ 6 - 2970502112617311232566 * x ^ 5 + 1094911063097803082541 * x ^ 4 - 256940266943308173597 * x ^ 3 + 32270677396372731708 * x ^ 2 - 993821735978094996 * x - 126509413139004240

/-- Coefficient of `y ^ 7` in the numerator of the certificate. -/
def q7 (x : ℚ) : ℚ :=
  81992919949180416 * x ^ 14 - 1526581878738941952 * x ^ 13 + 12880530434682275328 * x ^ 12 - 65101946515339212288 * x ^ 11 + 219623170278960099855 * x ^ 10 - 521644741688479419945 * x ^ 9 + 896609487241199913003 * x ^ 8 - 1128287659333847609934 * x ^ 7 + 1039094716616449080543 * x ^ 6 - 692097811610815719963 * x ^ 5 + 325041967883358322011 * x ^ 4 - 102914040321231115446 * x ^ 3 + 20296455075234913068 * x ^ 2 - 2136458143810275768 * x + 80903811161789280

/-- Coefficient of `y ^ 8` in the numerator of the certificate. -/
def q8 (x : ℚ) : ℚ :=
  -15392251973596608 * x ^ 13 + 271850244206320944 * x ^ 12 - 2160067913719477920 * x ^ 11 + 10200114830891354562 * x ^ 10 - 31871645323217296704 * x ^ 9 + 69444035802035007894 * x ^ 8 - 108293204443561863507 * x ^ 7 + 122018068728748183500 * x ^ 6 - 98964788539041693216 * x ^ 5 + 56793184546111050852 * x ^ 4 - 22278213685006173513 * x ^ 3 + 5613129814715178408 * x ^ 2 - 806445755095679892 * x + 49378555643436720

/-- Coefficient of `y ^ 9` in the numerator of the certificate. -/
def q9 (x : ℚ) : ℚ :=
  2114793487913040 * x ^ 12 - 35337938910444360 * x ^ 11 + 263238694940136048 * x ^ 10 - 1153498233283130697 * x ^ 9 + 3306376311419591916 * x ^ 8 - 6522044294294419770 * x ^ 7 + 9064204333128907470 * x ^ 6 - 8925320403267599691 * x ^ 5 + 6164324454767241630 * x ^ 4 - 2902858936209183954 * x ^ 3 + 881322667667901768 * x ^ 2 - 154253150462983896 * x + 11732046613025760

/-- Coefficient of `y ^ 10` in the numerator of the certificate. -/
def q10 (x : ℚ) : ℚ :=
  -206617443175044 * x ^ 11 + 3258428120760375 * x ^ 10 - 22648041556656870 * x ^ 9 + 91390158734200581 * x ^ 8 - 237554267095267557 * x ^ 7 + 417194671661184711 * x ^ 6 - 504561873875083422 * x ^ 5 + 419616075378000513 * x ^ 4 - 234676085481585255 * x ^ 3 + 83807449548054588 * x ^ 2 - 17128852785601884 * x + 1508831448305040

/-- Coefficient of `y ^ 11` in the numerator of the certificate. -/
def q11 (x : ℚ) : ℚ :=
  13581515492883 * x ^ 10 - 201700011751443 * x ^ 9 + 1301807317121655 * x ^ 8 - 4796445844249170 * x ^ 7 + 11151182202420999 * x ^ 6 - 17066448983761881 * x ^ 5 + 17384451109856931 * x ^ 4 - 11612192037077274 * x ^ 3 + 4851043482302124 * x ^ 2 - 1138000264304040 * x + 112727441210400

/-- Coefficient of `y ^ 12` in the numerator of the certificate. -/
def q12 (x : ℚ) : ℚ :=
  -537538923162 * x ^ 9 + 7505614657674 * x ^ 8 - 44779775773545 * x ^ 7 + 149296976181126 * x ^ 6 - 305502850876770 * x ^ 5 + 396492414461352 * x ^ 4 - 325009946049759 * x ^ 3 + 161353791701640 * x ^ 2 - 43659754674732 * x + 4839265008720

/-- Coefficient of `y ^ 13` in the numerator of the certificate. -/
def q13 (x : ℚ) : ℚ :=
  9652090491 * x ^ 8 - 126651168918 * x ^ 7 + 696168971784 * x ^ 6 - 2082943777842 * x ^ 5 + 3687672394809 * x ^ 4 - 3925603594872 * x ^ 3 + 2428405851636 * x ^ 2 - 786239092368 * x + 99795991680

/-- The numerator of the certificate. -/
def Qp (x y : ℚ) : ℚ :=
  q0 x + q1 x * y + q2 x * y ^ 2 + q3 x * y ^ 3 + q4 x * y ^ 4 + q5 x * y ^ 5 + q6 x * y ^ 6 + q7 x * y ^ 7 + q8 x * y ^ 8 + q9 x * y ^ 9 + q10 x * y ^ 10 + q11 x * y ^ 11 + q12 x * y ^ 12 + q13 x * y ^ 13

/-- The `x`-part of the denominator of the certificate. -/
def Dn (x : ℚ) : ℚ := 32 * x * (2 * x - 1) * (2 * x + 1) * (4 * x - 5) * (4 * x - 3) * (4 * x - 1) * (4 * x + 1)

/-- The certificate. -/
noncomputable def Rc (x y : ℚ) : ℚ :=
  y * Qp x y / (Dn x * ((4 * x - 1 - y) * (4 * x - 2 - y) * (4 * x - 3 - y) * (4 * x - 4 - y) * (4 * x - 5 - y) * (4 * x - 6 - y) * (4 * x - 7 - y) * (4 * x - 8 - y) * (4 * x - 9 - y) * (4 * x - 10 - y) * (4 * x - 11 - y)))

/-- `Rc x (y + 1)`, expanded. -/
noncomputable def RcB (x y : ℚ) : ℚ :=
  (y + 1) * Qp x (y + 1) / (Dn x * ((4 * x - 2 - y) * (4 * x - 3 - y) * (4 * x - 4 - y) * (4 * x - 5 - y) * (4 * x - 6 - y) * (4 * x - 7 - y) * (4 * x - 8 - y) * (4 * x - 9 - y) * (4 * x - 10 - y) * (4 * x - 11 - y) * (4 * x - 12 - y)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key (x y : ℚ) (hx : 5 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ x) :
    (586413 * x ^ 4 - 1231200 * x ^ 3 + 775101 * x ^ 2 - 143286 * x) + (15946643 * x ^ 4 - 186214804 * x ^ 3 + 598016755 * x ^ 2 - 732654974 * x + 305230680) * rhA x y + (-486785818 * x ^ 4 + 4173881918 * x ^ 3 - 13213813986 * x ^ 2 + 17666672178 * x - 8311662708) * (rhA x y * rhB x y) +
      (-502146048 * x ^ 4 + 3325025792 * x ^ 3 - 8087800256 * x ^ 2 + 8562823968 * x - 3326533056) * (rhA x y * rhB x y * rhC x y) =
      RcB x y * sg x y - Rc x y := by
  have h0 : (y + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h1 : (4 * x - y : ℚ) ≠ 0 := by intro h; linarith
  have h2 : (x * 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h3 : (4 * x - 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h4 : (x * 4 - 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h5 : (4 * x - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h6 : (x * 4 - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h7 : (4 * x - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have h8 : (x * 4 - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have h9 : (4 * x - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h10 : (x * 4 - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h11 : (4 * x - 5 - y : ℚ) ≠ 0 := by intro h; linarith
  have h12 : (x * 4 - 5 - y : ℚ) ≠ 0 := by intro h; linarith
  have h13 : (4 * x - 6 - y : ℚ) ≠ 0 := by intro h; linarith
  have h14 : (x * 4 - 6 - y : ℚ) ≠ 0 := by intro h; linarith
  have h15 : (4 * x - 7 - y : ℚ) ≠ 0 := by intro h; linarith
  have h16 : (x * 4 - 7 - y : ℚ) ≠ 0 := by intro h; linarith
  have h17 : (4 * x - 8 - y : ℚ) ≠ 0 := by intro h; linarith
  have h18 : (x * 4 - 8 - y : ℚ) ≠ 0 := by intro h; linarith
  have h19 : (4 * x - 9 - y : ℚ) ≠ 0 := by intro h; linarith
  have h20 : (x * 4 - 9 - y : ℚ) ≠ 0 := by intro h; linarith
  have h21 : (4 * x - 10 - y : ℚ) ≠ 0 := by intro h; linarith
  have h22 : (x * 4 - 10 - y : ℚ) ≠ 0 := by intro h; linarith
  have h23 : (4 * x - 11 - y : ℚ) ≠ 0 := by intro h; linarith
  have h24 : (x * 4 - 11 - y : ℚ) ≠ 0 := by intro h; linarith
  have h25 : (4 * x - 12 - y : ℚ) ≠ 0 := by intro h; linarith
  have h26 : (x * 4 - 12 - y : ℚ) ≠ 0 := by intro h; linarith
  have h27 : (4 * x + 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h28 : (x * 4 + 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h29 : (4 * x + 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h30 : (x * 4 + 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h31 : (4 * x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h32 : (x * 4 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h33 : (4 * x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h34 : (x * 4 - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h35 : (4 * x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h36 : (x * 4 - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h37 : (4 * x - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h38 : (x * 4 - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h39 : (4 * x - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h40 : (x * 4 - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h41 : (4 * x - 6 : ℚ) ≠ 0 := by intro h; linarith
  have h42 : (x * 4 - 6 : ℚ) ≠ 0 := by intro h; linarith
  have h43 : (4 * x - 7 : ℚ) ≠ 0 := by intro h; linarith
  have h44 : (x * 4 - 7 : ℚ) ≠ 0 := by intro h; linarith
  have h45 : (4 * x - 8 : ℚ) ≠ 0 := by intro h; linarith
  have h46 : (x * 4 - 8 : ℚ) ≠ 0 := by intro h; linarith
  have h47 : (4 * x - 9 : ℚ) ≠ 0 := by intro h; linarith
  have h48 : (x * 4 - 9 : ℚ) ≠ 0 := by intro h; linarith
  have h49 : (4 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h50 : (x * 4 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h51 : (4 * x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have h52 : (x * 4 + 2 : ℚ) ≠ 0 := by intro h; linarith
  have h53 : (4 * x : ℚ) ≠ 0 := by intro h; linarith
  have h54 : (x * 4 : ℚ) ≠ 0 := by intro h; linarith
  have h55 : (x : ℚ) ≠ 0 := by intro h; linarith
  have h56 : (2 * x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h57 : (x * 2 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h58 : (2 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h59 : (x * 2 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h60 : (3 * x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h61 : (x * 3 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h62 : (3 * x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h63 : (x * 3 - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h64 : (3 * x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h65 : (x * 3 - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h66 : (3 * x - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h67 : (x * 3 - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h68 : (3 * x - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h69 : (x * 3 - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h70 : (3 * x - 6 : ℚ) ≠ 0 := by intro h; linarith
  have h71 : (x * 3 - 6 : ℚ) ≠ 0 := by intro h; linarith
  have h72 : (3 * x - 7 : ℚ) ≠ 0 := by intro h; linarith
  have h73 : (x * 3 - 7 : ℚ) ≠ 0 := by intro h; linarith
  have h74 : (3 * x - 8 : ℚ) ≠ 0 := by intro h; linarith
  have h75 : (x * 3 - 8 : ℚ) ≠ 0 := by intro h; linarith
  have h76 : (3 * x - 9 : ℚ) ≠ 0 := by intro h; linarith
  have h77 : (x * 3 - 9 : ℚ) ≠ 0 := by intro h; linarith
  have h78 : (x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h79 : (x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h80 : (x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h81 : (2 * x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h82 : (x * 2 - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h83 : (2 * x - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h84 : (x * 2 - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h85 : (3 * x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h86 : (x * 3 - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h87 : (x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h88 : (4 * (x - 1) - 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h89 : ((x - 1) * 4 - 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h90 : (4 * (x - 1) - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h91 : ((x - 1) * 4 - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h92 : (4 * (x - 1) - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have h93 : ((x - 1) * 4 - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have h94 : (4 * (x - 1) - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h95 : ((x - 1) * 4 - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h96 : (4 * (x - 1) - 5 - y : ℚ) ≠ 0 := by intro h; linarith
  have h97 : ((x - 1) * 4 - 5 - y : ℚ) ≠ 0 := by intro h; linarith
  have h98 : (4 * (x - 1) - 6 - y : ℚ) ≠ 0 := by intro h; linarith
  have h99 : ((x - 1) * 4 - 6 - y : ℚ) ≠ 0 := by intro h; linarith
  have h100 : (4 * (x - 1) - 7 - y : ℚ) ≠ 0 := by intro h; linarith
  have h101 : ((x - 1) * 4 - 7 - y : ℚ) ≠ 0 := by intro h; linarith
  have h102 : (4 * (x - 1) - 8 - y : ℚ) ≠ 0 := by intro h; linarith
  have h103 : ((x - 1) * 4 - 8 - y : ℚ) ≠ 0 := by intro h; linarith
  have h104 : (4 * (x - 2) - 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h105 : ((x - 2) * 4 - 1 - y : ℚ) ≠ 0 := by intro h; linarith
  have h106 : (4 * (x - 2) - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h107 : ((x - 2) * 4 - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have h108 : (4 * (x - 2) - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have h109 : ((x - 2) * 4 - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have h110 : (4 * (x - 2) - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h111 : ((x - 2) * 4 - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h112 : (4 * (x - 1) - y : ℚ) ≠ 0 := by intro h; linarith
  have h113 : ((x - 1) * 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have h114 : (4 * (x - 2) - y : ℚ) ≠ 0 := by intro h; linarith
  have h115 : ((x - 2) * 4 - y : ℚ) ≠ 0 := by intro h; linarith
  unfold rhA rhB rhC RcB sg Rc Qp Dn q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  field_simp
  ring

theorem rhA_eq (x y : ℚ) : rh x y = rhA x y := rfl

theorem rhB_eq (x y : ℚ) : rh (x - 1) y = rhB x y := by
  unfold rh rhB
  congr 1 <;> ring

theorem rhC_eq (x y : ℚ) : rh (x - 2) y = rhC x y := by
  unfold rh rhC
  congr 1 <;> ring

theorem RcB_eq (x y : ℚ) : Rc x (y + 1) = RcB x y := by
  unfold Rc RcB
  congr 1
  congr 1
  ring

/-- The summand in factorial form. -/
noncomputable def ff (N K : ℕ) : ℚ :=
  ((4 * N + 2).factorial : ℚ) /
    ((K.factorial : ℚ) * ((N - K).factorial : ℚ) * ((3 * N - 1).factorial : ℚ) *
      ((4 * N + 2 - K : ℕ) : ℚ) * ((4 * N + 1 - K : ℕ) : ℚ) * ((4 * N - K : ℕ) : ℚ))

/-- The summand, extended by zero. -/
noncomputable def f (N K : ℕ) : ℚ := if K ≤ N then ff N K else 0

theorem term_eq (N K : ℕ) (hN : 1 ≤ N) (h : K ≤ N) :
    ((4 * N + 2).choose K : ℚ) * ((4 * N - K - 1).choose (N - K) : ℚ) = ff N K := by
  obtain ⟨t, ht⟩ : ∃ t, 4 * N - K - 1 = t := ⟨_, rfl⟩
  have e1 : 4 * N + 2 - K = t + 3 := by omega
  have e2 : 4 * N + 1 - K = t + 2 := by omega
  have e3 : 4 * N - K = t + 1 := by omega
  have e4 : t - (N - K) = 3 * N - 1 := by omega
  unfold ff
  rw [ht, Nat.cast_choose ℚ (show K ≤ 4 * N + 2 by omega),
    Nat.cast_choose ℚ (show N - K ≤ t by omega), e1, e2, e3, e4,
    Nat.factorial_succ (t + 2), Nat.factorial_succ (t + 1), Nat.factorial_succ t]
  push_cast
  field_simp
  ring

theorem f_succ (N K : ℕ) : f N (K + 1) = f N K * sg N K := by
  unfold f
  by_cases h : K + 1 ≤ N
  · rw [if_pos h, if_pos (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, N = K + 1 + j := ⟨N - (K + 1), by omega⟩
    unfold ff sg
    rw [show K + 1 + j - (K + 1) = j by omega, show K + 1 + j - K = j + 1 by omega,
      show 4 * (K + 1 + j) + 2 - (K + 1) = 3 * K + 4 * j + 5 by omega,
      show 4 * (K + 1 + j) + 1 - (K + 1) = 3 * K + 4 * j + 4 by omega,
      show 4 * (K + 1 + j) - (K + 1) = 3 * K + 4 * j + 3 by omega,
      show 4 * (K + 1 + j) + 2 - K = 3 * K + 4 * j + 6 by omega,
      show 4 * (K + 1 + j) + 1 - K = 3 * K + 4 * j + 5 by omega,
      show 4 * (K + 1 + j) - K = 3 * K + 4 * j + 4 by omega,
      Nat.factorial_succ K, Nat.factorial_succ j]
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : (4 * ((K : ℚ) + 1 + j) - 1 - K) ≠ 0 := by intro h; linarith
    have n2 : (3 * (K : ℚ) + 4 * j + 3) ≠ 0 := by intro h; linarith
    have n3 : (3 * (K : ℚ) + 4 * j + 4) ≠ 0 := by intro h; linarith
    have n4 : (3 * (K : ℚ) + 4 * j + 5) ≠ 0 := by intro h; linarith
    have n5 : (3 * (K : ℚ) + 4 * j + 6) ≠ 0 := by intro h; linarith
    have n6 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n7 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · rw [if_neg h]
    by_cases h' : K ≤ N
    · obtain rfl : K = N := by omega
      simp [sg]
    · rw [if_neg h']
      simp

theorem fact3 (M : ℕ) (hM : 1 ≤ M) :
    (3 * (M + 1) - 1).factorial = (3 * M + 2) * (3 * M + 1) * (3 * M) * (3 * M - 1).factorial := by
  obtain ⟨P, rfl⟩ : ∃ P, M = P + 1 := ⟨M - 1, by omega⟩
  rw [show 3 * (P + 1 + 1) - 1 = 3 * P + 2 + 1 + 1 + 1 by omega,
    show 3 * (P + 1) - 1 = 3 * P + 2 by omega, Nat.factorial_succ (3 * P + 2 + 1 + 1),
    Nat.factorial_succ (3 * P + 2 + 1), Nat.factorial_succ (3 * P + 2)]
  ring

theorem f_pred (M K : ℕ) (hM : 1 ≤ M) : f M K = f (M + 1) K * rh ((M : ℚ) + 1) K := by
  unfold f
  by_cases h : K ≤ M
  · rw [if_pos h, if_pos (by omega)]
    unfold ff rh
    rw [fact3 M hM]
    obtain ⟨j, rfl⟩ : ∃ j, M = K + j := ⟨M - K, by omega⟩
    rw [show K + j - K = j by omega, show K + j + 1 - K = j + 1 by omega,
      show 4 * (K + j) + 2 - K = 3 * K + 4 * j + 2 by omega,
      show 4 * (K + j) + 1 - K = 3 * K + 4 * j + 1 by omega,
      show 4 * (K + j) - K = 3 * K + 4 * j by omega,
      show 4 * (K + j + 1) + 2 - K = 3 * K + 4 * j + 6 by omega,
      show 4 * (K + j + 1) + 1 - K = 3 * K + 4 * j + 5 by omega,
      show 4 * (K + j + 1) - K = 3 * K + 4 * j + 4 by omega,
      show 4 * (K + j + 1) + 2 = 4 * (K + j) + 2 + 1 + 1 + 1 + 1 by ring,
      Nat.factorial_succ (4 * (K + j) + 2 + 1 + 1 + 1), Nat.factorial_succ (4 * (K + j) + 2 + 1 + 1),
      Nat.factorial_succ (4 * (K + j) + 2 + 1), Nat.factorial_succ (4 * (K + j) + 2),
      Nat.factorial_succ j]
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hKj : (1 : ℚ) ≤ K + j := by exact_mod_cast hM
    have n1 : (4 * ((K : ℚ) + j + 1) + 2) ≠ 0 := by intro h; linarith
    have n2 : (4 * ((K : ℚ) + j + 1) + 1) ≠ 0 := by intro h; linarith
    have n3 : (4 * ((K : ℚ) + j + 1)) ≠ 0 := by intro h; linarith
    have n4 : (4 * ((K : ℚ) + j + 1) - 1) ≠ 0 := by intro h; linarith
    have n5 : (4 * ((K : ℚ) + j + 1) - 2 - K) ≠ 0 := by intro h; linarith
    have n6 : (4 * ((K : ℚ) + j + 1) - 3 - K) ≠ 0 := by intro h; linarith
    have n7 : (4 * ((K : ℚ) + j + 1) - 4 - K) ≠ 0 := by intro h; linarith
    have n8 : (3 * (K : ℚ) + 4 * j + 2) ≠ 0 := by intro h; linarith
    have n9 : (3 * (K : ℚ) + 4 * j + 1) ≠ 0 := by intro h; linarith
    have n10 : (3 * (K : ℚ) + 4 * j) ≠ 0 := by intro h; linarith
    have n11 : (3 * ((K : ℚ) + j)) ≠ 0 := by intro h; linarith
    have n12 : (3 * ((K : ℚ) + j) + 1) ≠ 0 := by intro h; linarith
    have n13 : (3 * ((K : ℚ) + j) + 2) ≠ 0 := by intro h; linarith
    have n14 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n15 : (4 * ((K : ℚ) + j + 1 - 1) - K) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · rw [if_neg h]
    by_cases h' : K ≤ M + 1
    · obtain rfl : K = M + 1 := by omega
      simp [rh]
    · rw [if_neg h']
      simp

theorem A_eq (N : ℕ) (hN : 1 ≤ N) : ((a N : ℤ) : ℚ) = ∑ k ∈ range (N + 1), f N k := by
  unfold a
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := by
    rw [Finset.mem_range] at hk
    omega
  rw [f, if_pos hk', ← term_eq N k hN hk']

theorem f_out (N K : ℕ) (h : N < K) : f N K = 0 := by
  unfold f
  rw [if_neg (by omega)]

theorem tele (m : ℕ) :
    (586413 * ((m : ℚ) + 5) ^ 4 - 1231200 * ((m : ℚ) + 5) ^ 3 + 775101 * ((m : ℚ) + 5) ^ 2 -
        143286 * ((m : ℚ) + 5)) * ∑ k ∈ range (m + 5 + 1), f (m + 5) k +
      (15946643 * ((m : ℚ) + 5) ^ 4 - 186214804 * ((m : ℚ) + 5) ^ 3 +
        598016755 * ((m : ℚ) + 5) ^ 2 - 732654974 * ((m : ℚ) + 5) + 305230680) *
        ∑ k ∈ range (m + 4 + 1), f (m + 4) k +
      (-486785818 * ((m : ℚ) + 5) ^ 4 + 4173881918 * ((m : ℚ) + 5) ^ 3 -
        13213813986 * ((m : ℚ) + 5) ^ 2 + 17666672178 * ((m : ℚ) + 5) - 8311662708) *
        ∑ k ∈ range (m + 3 + 1), f (m + 3) k +
      (-502146048 * ((m : ℚ) + 5) ^ 4 + 3325025792 * ((m : ℚ) + 5) ^ 3 -
        8087800256 * ((m : ℚ) + 5) ^ 2 + 8562823968 * ((m : ℚ) + 5) - 3326533056) *
        ∑ k ∈ range (m + 2 + 1), f (m + 2) k = 0 := by
  set x : ℚ := (m : ℚ) + 5 with hx
  have e4 : ∑ k ∈ range (m + 4 + 1), f (m + 4) k = ∑ k ∈ range (m + 6), f (m + 4) k := by
    rw [show m + 6 = m + 4 + 1 + 1 by omega, Finset.sum_range_succ _ (m + 4 + 1),
      f_out (m + 4) (m + 4 + 1) (by omega), add_zero]
  have e3 : ∑ k ∈ range (m + 3 + 1), f (m + 3) k = ∑ k ∈ range (m + 6), f (m + 3) k := by
    rw [show m + 6 = m + 3 + 1 + 1 + 1 by omega, Finset.sum_range_succ _ (m + 3 + 1 + 1),
      Finset.sum_range_succ _ (m + 3 + 1), f_out (m + 3) (m + 3 + 1) (by omega),
      f_out (m + 3) (m + 3 + 1 + 1) (by omega), add_zero, add_zero]
  have e2 : ∑ k ∈ range (m + 2 + 1), f (m + 2) k = ∑ k ∈ range (m + 6), f (m + 2) k := by
    rw [show m + 6 = m + 2 + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ _ (m + 2 + 1 + 1 + 1),
      Finset.sum_range_succ _ (m + 2 + 1 + 1), Finset.sum_range_succ _ (m + 2 + 1),
      f_out (m + 2) (m + 2 + 1) (by omega), f_out (m + 2) (m + 2 + 1 + 1) (by omega),
      f_out (m + 2) (m + 2 + 1 + 1 + 1) (by omega), add_zero, add_zero, add_zero]
  rw [e4, e3, e2, show m + 5 + 1 = m + 6 by omega, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hstep : ∀ k ∈ range (m + 6),
      (586413 * x ^ 4 - 1231200 * x ^ 3 + 775101 * x ^ 2 - 143286 * x) * f (m + 5) k +
        (15946643 * x ^ 4 - 186214804 * x ^ 3 + 598016755 * x ^ 2 - 732654974 * x + 305230680) *
          f (m + 4) k +
        (-486785818 * x ^ 4 + 4173881918 * x ^ 3 - 13213813986 * x ^ 2 + 17666672178 * x -
          8311662708) * f (m + 3) k +
        (-502146048 * x ^ 4 + 3325025792 * x ^ 3 - 8087800256 * x ^ 2 + 8562823968 * x -
          3326533056) * f (m + 2) k =
      Rc x ((k + 1 : ℕ) : ℚ) * f (m + 5) (k + 1) - Rc x (k : ℚ) * f (m + 5) k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h4 : f (m + 4) k = f (m + 5) k * rhA x k := by
      rw [f_pred (m + 4) k (by omega), ← rhA_eq]
      congr 2
      rw [hx]
      push_cast
      ring
    have h3 : f (m + 3) k = f (m + 4) k * rhB x k := by
      rw [f_pred (m + 3) k (by omega), ← rhB_eq]
      congr 2
      rw [hx]
      push_cast
      ring
    have h2 : f (m + 2) k = f (m + 3) k * rhC x k := by
      rw [f_pred (m + 2) k (by omega), ← rhC_eq]
      congr 2
      rw [hx]
      push_cast
      ring
    have h6 : f (m + 5) (k + 1) = f (m + 5) k * sg x k := by
      rw [f_succ, hx]
      push_cast
      ring_nf
    have hk5 : (5 : ℚ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hkx : (k : ℚ) ≤ x := by
      rw [hx]
      have : (k : ℚ) ≤ (m : ℚ) + 5 := by exact_mod_cast (show k ≤ m + 5 by omega)
      exact this
    have hkey := key x k hk5 hk0 hkx
    have hR : Rc x ((k + 1 : ℕ) : ℚ) = RcB x k := by
      rw [← RcB_eq]
      push_cast
      rfl
    rw [hR, h6, h2, h3, h4]
    linear_combination (f (m + 5) k) * hkey
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => Rc x (k : ℚ) * f (m + 5) k)]
  simp only [f_out (m + 5) (m + 6) (by omega), mul_zero, Nat.cast_zero]
  simp [Rc]

theorem a_small : a 0 = 1 ∧ a 1 = 9 ∧ a 2 = 126 ∧ a 3 = 1978 ∧ a 4 = 32703 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [a, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem rec_ge (m : ℕ) :
    (586413 * ((m + 5 : ℕ) : ℤ) ^ 4 - 1231200 * ((m + 5 : ℕ) : ℤ) ^ 3 +
        775101 * ((m + 5 : ℕ) : ℤ) ^ 2 - 143286 * ((m + 5 : ℕ) : ℤ)) * a (m + 5)
      + (15946643 * ((m + 5 : ℕ) : ℤ) ^ 4 - 186214804 * ((m + 5 : ℕ) : ℤ) ^ 3 +
        598016755 * ((m + 5 : ℕ) : ℤ) ^ 2 - 732654974 * ((m + 5 : ℕ) : ℤ) + 305230680) * a (m + 4)
      + (-486785818 * ((m + 5 : ℕ) : ℤ) ^ 4 + 4173881918 * ((m + 5 : ℕ) : ℤ) ^ 3 -
        13213813986 * ((m + 5 : ℕ) : ℤ) ^ 2 + 17666672178 * ((m + 5 : ℕ) : ℤ) - 8311662708) *
          a (m + 3)
      + (-502146048 * ((m + 5 : ℕ) : ℤ) ^ 4 + 3325025792 * ((m + 5 : ℕ) : ℤ) ^ 3 -
        8087800256 * ((m + 5 : ℕ) : ℤ) ^ 2 + 8562823968 * ((m + 5 : ℕ) : ℤ) - 3326533056) *
          a (m + 2) = 0 := by
  have h := tele m
  rw [← A_eq (m + 5) (by omega), ← A_eq (m + 4) (by omega), ← A_eq (m + 3) (by omega),
    ← A_eq (m + 2) (by omega)] at h
  have hq : ((((586413 * ((m + 5 : ℕ) : ℤ) ^ 4 - 1231200 * ((m + 5 : ℕ) : ℤ) ^ 3 +
        775101 * ((m + 5 : ℕ) : ℤ) ^ 2 - 143286 * ((m + 5 : ℕ) : ℤ)) * a (m + 5)
      + (15946643 * ((m + 5 : ℕ) : ℤ) ^ 4 - 186214804 * ((m + 5 : ℕ) : ℤ) ^ 3 +
        598016755 * ((m + 5 : ℕ) : ℤ) ^ 2 - 732654974 * ((m + 5 : ℕ) : ℤ) + 305230680) * a (m + 4)
      + (-486785818 * ((m + 5 : ℕ) : ℤ) ^ 4 + 4173881918 * ((m + 5 : ℕ) : ℤ) ^ 3 -
        13213813986 * ((m + 5 : ℕ) : ℤ) ^ 2 + 17666672178 * ((m + 5 : ℕ) : ℤ) - 8311662708) *
          a (m + 3)
      + (-502146048 * ((m + 5 : ℕ) : ℤ) ^ 4 + 3325025792 * ((m + 5 : ℕ) : ℤ) ^ 3 -
        8087800256 * ((m + 5 : ℕ) : ℤ) ^ 2 + 8562823968 * ((m + 5 : ℕ) : ℤ) - 3326533056) *
          a (m + 2) : ℤ) : ℚ)) = 0 := by
    push_cast
    linear_combination h
  exact (Int.cast_eq_zero (α := ℚ)).mp hq

theorem rec (n : ℕ) (hn : 3 ≤ n) :
    (586413 * (n : ℤ) ^ 4 - 1231200 * (n : ℤ) ^ 3 + 775101 * (n : ℤ) ^ 2 - 143286 * (n : ℤ)) * a n
      + (15946643 * (n : ℤ) ^ 4 - 186214804 * (n : ℤ) ^ 3 + 598016755 * (n : ℤ) ^ 2 - 732654974 * (n : ℤ) + 305230680) * a (n - 1)
      + (-486785818 * (n : ℤ) ^ 4 + 4173881918 * (n : ℤ) ^ 3 - 13213813986 * (n : ℤ) ^ 2 + 17666672178 * (n : ℤ) - 8311662708) * a (n - 2)
      + (-502146048 * (n : ℤ) ^ 4 + 3325025792 * (n : ℤ) ^ 3 - 8087800256 * (n : ℤ) ^ 2 + 8562823968 * (n : ℤ) - 3326533056) * a (n - 3) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := a_small
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
  · rw [show 3 - 1 = 2 by rfl, show 3 - 2 = 1 by rfl, show 3 - 3 = 0 by rfl, h0, h1, h2, h3]
    norm_num
  · rw [show 4 - 1 = 3 by rfl, show 4 - 2 = 2 by rfl, show 4 - 3 = 1 by rfl, h1, h2, h3, h4]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    exact rec_ge m

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a386837.main := OMA.Helpers.rec
