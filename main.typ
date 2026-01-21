#set text(lang: "fi")
#set page(numbering: "1")

#let pm = sym.plus.minus
#let b(c) = block(c)
#let ds(c) = math.display(c)
#let ar(c) = math.arrow(c)
#let dotp(c1, c2) = $ chevron.l c1, c2 chevron.r $
#let t1(..c) = table(
  columns: (auto),
  inset: 10pt,
  align: horizon,
  ..c
)
#let t2(..c) = table(
  columns: (auto, auto),
  inset: 10pt,
  align: horizon,
  ..c
)
#let limn = $ lim_(n->infinity) $
#let sumn1 = $ sum_(n=1)^infinity $
#let sumn0 = $ sum_(n=0)^infinity $
#let intab = $ integral_a^b $
#let fx = $ f(x) $
#let gx = $ g(x) $
#let dx = $ dif x $

#outline()

#pagebreak()

= Matematiikka

== Muistikaavat

#t1(
  b($ a^2 - b^2 = (a+b)(a-b) $),
  b($ a x^2 + b x + c = a (x - x_1) (x - x_2) $),
  b($ (a x + b) / ((x-x_1)(x-x_2)) = A / (x-x_1) + B / (x-x_2) $),
)

== Yhtälöt

#t2(
  [2. asteen ratkaisukaava], $ x = (-b pm sqrt(b^2 - 4 a c)) / (2a) $,
)

== Raja-arvo

Jos $ds(limn a_n = a)$, $ds(limn b_n = b)$ ja $c in RR$.

#t1(
  b($ limn (a_n + b_n) = a + b $),
  b($ limn (c a_n) = c a $),
  b($ limn (a_n b_n) = a b $),
  b($ limn (a_n / b_n) = a / b, " jos" b != 0 $),
)

Eräitä raja-arvoja:

#t1(
  b($ limn root(n, a) = 1, " kun" a > 0 $),
  b($ limn root(n, n) = 1 $),
  b($ limn (1 + 1 / n)^n = e $),
)

== Jonot ja sarjat

#t2(
  [Jono], $ (a_n)_(n in NN) = (a_n)^infinity_(n=1) = (a_1,a_2,a_3,...) $,
  [Sarja], $ s_n = a_1 + a_2 + a_3 ... + a_n = sum_(k=1)^n a_k $,
  [Geometrinen sarja], $ sum_(k=0)^n a q^k $,
  [Suppenevan geometrisen sarjan summa], $ a / (1 - q) $,
  [Suppenevan geometrisen sarjan osasumma], $ sum_(k=0)^n a q^k = (a (1 - q^(n+1))) / (1 - q) $,
)

== Sarja

#t2(
  [Sarja], $ sumn1 a_n = limn sum_(k=1)^n a_k $,
  [Summausindeksin siirto], $ sumn1 a_n = sumn0 a_(n+1) $,
  [Suhdetestin raja-arvomuoto], [ $ limn abs(a_(n+1) / a_n) = q " niin, " $ $ cases("suppenee," &0 <= q < 1, "hajaantuu," &q>1, "suppenee tai hajaantuu," &q = 1) $ ],
)

Suppenevien sarjojen ominaisuuksia:

#t1(
  b($ sumn1 (a_n + b_n) = sumn1 a_n + sumn1 b_n $),
  b($ sumn1 c a_n = c sumn1 a_n $),
)

== Funktiot

#t2(
  [Käänteisfunktion derivointikaava], $ (f^(-1))'(x) = 1 / (f'(f^(-1)(x))) $,
)

== Taylor-polynomi

#t2(
  [Taylor-polynomi], $ P_n (x;x_0) = sum_(k=0)^n (f^(k) (x_0))/(k!) (x-x_0)^k $,
  [Virhetermi], $ f(x) = P_n (x;x_0) + E_n (x) $,
  [Virhetermi], $ E_n (x) = (f^(n+1) (c) )/(n+1)! (x-x_0)^(n+1) ", jossakin pisteessä " c in [x_0,x] $,
  [Virheen suuruus], $ |E_n (x)| = (M)/(n+1)! abs(x-x_0)^(n+1) ", kun " M >= abs(f^(n+1) (x)) $,
)

Taylor-sarjoja:

#t1(
  b($ 1/(1-x) = sumn0 x^n, abs(x) < 1 $),
  b($ e^x = sumn0 x^n/n! $),
  b($ sin x = sumn0 (-1)^n/(2n+1)! x^(2n+1) $),
  b($ cos x = sumn0 (-1)^n/(2n)! x^(2n) $),
  b($ (1+x)^r = sumn0 (r(r-1)(r-2)...(r-n+1))/(n!) x^(n) $),
)

== Geometria

#t2(
  [Ellipsi...], $ (x-c)^2 / a^2 + y^2/b^2 = 1 $,
  [...keskipisteen etäisyys origosta], $ c = sqrt(a^2 - b^2) $,
  [...x-suuntainen läpimitta], $ 2 a $,
  [...y-suuntainen läpimitta], $ 2 b $,
  [...eksentrisyys], $ epsilon = c/a $,
  [...etäisyys origosta kulmassa $theta$ x-akseliin], $ r = (a(1-epsilon^2))/(1-epsilon cos theta) $,
)

== Kompleksiluvut

#t2(
  [Kompleksiluku], $ x = x_1 + i x_2 in CC $,
  [Reaaliosa], $ Re(x) = "Re"(x) = x_1 $,
  [Imaginaariosa], $ Im(x) = "Im"(x) = x_2 $,
  [Kompleksikonjugaatti], $ overline(x) = x^* = x_1 - i x_2 $,
  [Napakoordinaatit], $ (r, phi) = (abs(x), arg(x)) $,
  [Polaarihajotelma], $ x = abs(x) e^(i phi) = abs(x) (cos(phi) + i sin(phi)) $,
  [Itseisarvo], $ abs(x) = sqrt(x_1^2 + x_2^2) $,
  [Konjugaatin tulo], $ x^* x = (x_1 - i x_2)(x_1 + i x^2) = x_1^2 + x_2^2 = abs(x)^2 $,
  [Yhteenlasku], $ x + y = (x_1 + y_1) + i(x_2 + y_2) $,
  [Tulo], $ cases(abs(x y) = abs(x) abs(y), arg(x y) = arg(x) + arg(y)) \ x y = (x_1 y_1 - x_2 y_2) + i(x_1 y_2 + x_2 y_1) $,
  [Jakolasku], $ cases(abs(x / y) = abs(x) / abs(y), arg(x y) = arg(x) - arg(y)) \ x / y = (x y^*) / (y y^*) = (x y^*) / abs(y)^2 $,
  [Kolmioepäyhtälö], $ abs(x+y) <= abs(x) + abs(y) $,
  [do Moivren kaava], $ (cos(t) + i sin(t))^n = cos(n t) + i sin(n t) $,
)

== Vektorit

#t2(
  [Vektori], $ ar(a) = a = (a_1, a_2, a_3, ..., a_n) = a_x hat(i) + a_y hat(j) + a_z hat(k) + ... $,
  [Normi (pituus)], $ norm(ar(a)) = sqrt(sum_(k=1)^n abs(a_k)^2) = sqrt(chevron.l ar(a)"," ar(a) chevron.r) = sqrt(a_x^2 + a_y^2 + a_z^2 + ...) $,
  [X-akselin välinen kulma], $ tan theta = a_y / a_x $,
  [Sisätulo / pistetulo], $ chevron.l ar(a), ar(b) chevron.r = ar(a) dot ar(b) = sum_(k=1)^n a_k b_k^* \ = norm(ar(a)) norm(ar(b)) cos(angle(ar(a), ar(b))) = a_x b_x^* + a_y b_y^* + a_z b_z^* + ... $,
  [Konjugaattisymmetria], $ dotp(a,b) = dotp(b,a)^* $,
  [Ensimmäisen argumentin lineaarisuus], $ dotp(a x + b y, z) = a dotp(x,z) + b dotp(y,z) $,
  [Summan/erotuksen sisätulo,\ ensimmäinen $pm$ määrää], $ dotp(a pm b, a pm b) = dotp(a, a) + dotp(b, b) pm dotp(a, b) pm dotp(b, a) $,
  [Polarisaatioyhtälö], $ 4 dotp(a,b) = norm(a+b)^2 - norm(a-b)^2 + i norm(a+i b)^2 - i norm(a - i b)^2 $,
  [Sisätulon reaaliosa], $ 4 dot Re dotp(a,b) = norm(a+b)^2 - norm(a-b)^2 $,
  [Sisätulon imaginaariosa], $ Im dotp(a,b) = Re(a, i b) $,
  [Suunnikasyhtälö], $ norm(a+b)^2 + norm(a-b)^2 = 2 norm(a)^2 + 2 norm(b)^2 $,
  [Kohtisuorat], $ chevron.l ar(a), ar(b) chevron.r = 0 $,
  [Cauchy-Schwarz -epäyhtälö], $ abs(dotp(ar(u), ar(v))) <= norm(ar(u)) norm(ar(v)) $,
  [Kolmioepäyhtälö], $ norm(ar(u) + ar(v)) <= norm(ar(u)) + norm(ar(v)) $,
  [*Ristitulo $RR^3$*], $ ar(a) times ar(b) = vec(a_y b_z - a_z b_y, a_z b_x - a_x b_z, a_x b_y - a_y b_x) = vec(a_2 b_3 - a_3 b_2, a_3 b_1 - a_1 b_3, a_1 b_2 - a_2 b_1) $,
  [..kohtisuoruus], $ dotp(a, a times b) = 0 = dotp(b, a times b) $,
  [..suuruus (suunnikkaan pinta-ala)], $ norm(ar(a) times ar(b)) = norm(ar(a)) norm(ar(b)) sin(angle(ar(a), ar(b))) $,
  [..monitahokkaan tilavuus], $ abs(dotp(a times b, c)) "monitahokas" O,  a + b + c  $,
  [..tason normaalivektori], $ (q-p) times (r-p) $,
)

== Matriisit

#t2(
  [Matriisin lähtö- ja maaliavaruus,\ m riviä, n saraketta], $ A: KK^n -> KK^m => [A]^(m times n) = mat(A_11, dots, A_(1n); dots.v, dots.down, dots.v; A_(m 1), dots, A_(m n);) $,
  [Rivillä j sarakkeessa k vektorille u], $ (A u)_j = sum_(k=1)^n A_(j k) u_k $,
  [Lineaarinen funktio matriisina], $ mat(A_(11), A_(12),dots, A_(1n); A_(21), A_(22), dots, A_(2n); dots.v, dots.v, dots.down, dots.v; A_(m 1), A_(m 2), dots, A_(m n)) vec(x_1,x_2, dots.v, x_n)\ = vec(A_(11) x_1 + A_(12) x_2 + dots + A_(1n) x_n, A_(21) x_1 + A_(22) x_2 + dots + A_(2n) x_n, dots.v, A_(m 1) x_1 + A_(m 2) x_2 + dots + A_(m n) x_n) $,
  ["Heikon muotoilun lause" kun $u in CC^n$], $ dotp(A u, u) = dotp(B u, u) => A = B $,
  [Normi], $ norm(A) = max(norm(A u): norm(u) <= 1) = sigma_1 $,
  [*Matriisitulo*], $ [B]_(m times p)  [A]_(p times n) = [B A]_(m times n) $,
  [...lineaarisina funktioina], $ KK^(n) ->^(A) KK^(p) ->^(B) KK^(m) $,
  [...sarakkeessa i rivillä j], $ (B A)_(i j) = sum_(k=1)^m B_(i k) A_(k j) $,
  [...normien estimaatti], $ norm(B A) <= norm(B) norm(A) $,
  [...potenssimerkintä], $ [A]^2 = [A][A] $
)

$
mat(B_11,B_12, dots, B_(1 p); B_21, B_22, dots, B_(2 p); dots.v, dots.v, dots.down, dots.v; B_(m 1), B_(m 2), dots, B_(m p)) mat(A_11,A_12, dots, A_(1 n); A_21, A_22, dots, A_(2 n); dots.v, dots.v, dots.down, dots.v; A_(p 1), A_(p 2), dots, A_(p n)) \
= mat(
  B_(11) A_(11) + B_(12) A_(21) + dots + B_(1p) A_(p 1) "   ", B_(11) A_(12) + B_(12) A_(22) + dots + B_(1p) A_(p 2) "   ", dots "   ", B_(11) A_(2n) + B_(12) A_(2n) + dots + B_(1p) A_(p n);
  B_(21) A_(11) + B_(22) A_(21) + dots + B_(2p) A_(p 1) "   ", B_(21) A_(12) + B_(22) A_(22) + dots + B_(2p) A_(p 2) "   ", dots "   ", B_(21) A_(2n) + B_(22) A_(2n) + dots + B_(2p) A_(p n);
  dots.v "   ", dots.v "   ", dots.down "   ", dots.v "   ";
  B_(m 1) A_(11) + B_(m 2) A_(21) + dots + B_(m p) A_(p 1) "   ", B_(m 1) A_(12) + B_(m 2) A_(22) + dots + B_(m p) A_(p 2) "   ", dots "   ", B_(m 1) A_(2n) + B_(m 2) A_(2n) + dots + B_(m p) A_(p n);
)
$

#t2(
  [Determinantti $KK^(3 times 3)$], $ det mat(a,b,c;d,e,f;g,h,i;) = mat(delim: "|", a,b,c;d,e,f;g,h,i;) \ = a e i - a f h + b f g - b d i + c d h - c e g $,
  [Determinantti $KK^(2 times 2)$], $ det mat(a,b;c,d;) = a d - b c $,
  [Determinantin tulo], $ det(A B) = det(A) det(B) $,
  [Kääntyvän matriisin determinantti], $ det(A^(-1)) = 1/det(A) $,
  [Matriisin kääntyvyys], $ det(A) != 0 <=> A " on kääntyvä" $,
  [Ominaisarvo $lambda$ ja -vektori $u$], $ A u = lambda u $,
  [Karakteristinen polynomi], $ p_A (z) = det(A - z I) = (-1)^n (z-lambda_1) (z-lambda_2) dots (z-lambda_n) $,
  [Ominaisarvojen tulo], $ lambda_1 dots.c lambda_n = det(A) $,
  [Ominaisarvojen summa], $ sum_(k=1)^n lambda_k = tr(A) $,
  [Matriisin jälki], $ tr(A) = sum_(k=1)^n A_(k k) $,
  [Matriisin diagonalisointi], $ Lambda = S^(-1) A S \ A = S Lambda S^(-1) $,
  [Diagonaalimatriisi ominaisarvojen avulla], $ Lambda = mat(lambda_1, 0, dots, 0; 0, lambda_2, dots, 0; dots.v, dots.v, dots.down, dots.v;0,0,dots,lambda_n;) $,
  [Diagonalisoiva matriisi ominaisvektoreina], $ S = [S_1, S_2, dots, S_n] $,
  [Ominaisarvoa vastaava ominaisvektori], $ A (S_k) = lambda_k S_(k) $,
  [Adjungaatti $A^*$], $ dotp(A u, w) = dotp(u, A^* w) \ mat(a,b;c,d)^* = mat(a^*,c^*;b^*,d^*) $,
  [Normaali matriisi], $ N N^* = N^* N $,
  [Symmetrinen matriisi], $ S^* = S $,
  [Positiivinen matriisi], $ dotp(P x, x) >= 0 $,
  [Unitaarinen matriisi], $ U^* = U^(-1) <=> dotp(U x, U y) = dotp(x,y) $,
  [Gram-Schmidt prosessi matriisille $S$], $ U_1 = S_1 / norm(S_1) \ U_k = V_k / norm(V_k) \ V_k = S_k - sum_(j=1)^(k-1) dotp(S_k, U_j) U_j $,
  [Singulaariarvohajotelma], $ A = U Sigma V^* $,
  [Singulaariarvo], $ sigma_k^2 = lambda_k $,
  [Pseudoinverssi], $ A^+ = V Sigma^+ U^* $,
)

== Pyörähdysmatriisit

#t2(
  [Kulman $theta$ pyörähdys x-akselin suhteen], $ R_x (theta) = mat(1, 0, 0; 0, cos theta, - sin theta; 0, sin theta, cos theta;) $,
  [Kulman $theta$ pyörähdys y-akselin suhteen], $ R_y (theta) = mat(cos theta, 0, sin theta; 0, 1, 0; -sin theta, 0, cos theta;) $,
  [Kulman $theta$ pyörähdys z-akselin suhteen], $ R_z (theta) = mat(cos theta, - sin theta, 0; sin theta, cos theta, 0; 0,0,1;) $,
  [Ensin kulman $theta_1$ ja sitten kulman $theta_2$ pyörähdys], $ R(theta_2) R(theta_1) ar(r) $,
)

== Trigonometriset funktiot

#t1(
  b($ sin^2 x + cos^2 x = 1 $),
  b($ sin (x + y) = sin x cos y + cos x sin y $),
  b($ cos (x + y) = cos x cos y - sin x sin y $),
  b($ sin theta pm sin phi = 2 sin((theta pm phi)/2) cos((theta minus.plus phi)/2) $),
  b($ cos theta + cos phi = 2 cos((theta + phi)/2) cos((theta - phi)/2) $),
  b($ cos theta - cos phi = - 2 sin((theta + phi)/2) sin((theta - phi)/2) $),
)

== Eksponenttifunktio


#t2(
  [Neperin luku], $ e = limn (1 + 1/n)^n = 1 + 1 + 1/(2!) + 1/(3!)... \ approx 2,718281828459... $,
  [Exponenttifunktio], $ exp(x) = sumn0 x^n / (n!) = limn (1 + x / n)^n = e^x $,
  [Logaritmifunktio = exponenttifunktion käänteisfunktio], [$ ln : ]0, infinity[ -> RR $ $ e^x = y <=> ln y $],
  [Eulerin kaava], $ e^(plus.minus i x) = cos x plus.minus i sin x $
)

Laskusääntöjä:

#t1(
  b($ a^x = y <=> log_a y $),
  b($ e^(ln x) = x | x > 0 $),
  b($ ln (e^x) = x | x in RR $),
  b($ ln 1 = 0, " " ln e = 1 $),
  b($ ln (a^b) = b ln a, " kun" a > 0, b in RR $),
  b($ ln (a b) = ln a + ln b, " kun" a,b > 0 $),
)

== Hyperboliset funktiot

#t2(
  [Sinh], $ sinh x = 1/2 (e^x - e^(-x)) $,
  [Cosh], $ cosh x = 1/2 (e^x + e^(-x)) $,
  [Tanh], $ tanh x = (sinh x) / (cosh x) $,
  [Sinin hyperbolinen vaste], $ i sin x = sinh(i x), " jossa" i^2 = -1 $,
  [Kosinin hyperbolinen vaste], $ i cos x = cosh(i x) $,
  [Hyperbolisen sinin käänteisfunktio], $ sinh^(-1) x = "ar" sinh x = ln(x + sqrt(1 + x^2)), " " x in RR $,
  [Hyperbolisen kosinin käänteisfunktio], $ cosh^(-1) x = "ar" cosh x = ln(x + sqrt(x^2 - 1)), " " x >= 1 $,
)

Laskusääntöjä:

#t1(
  b($ cosh^2 x - sinh^2 x = 1 $),
)

== Derivointi

=== Derivoimissäännöt

#t1(
  b($ D(f(x) + g(x)) = D f(x) + D g(x) $),
  b($ D(c f(x)) = c D f(x) $),
  b($ D(f(x) g(x)) = f'(x) g(x) + f(x) g'(x) $),
  b($ D(f(x)/g(x)) = (f'(x) g(x) - f(x) g'(x)) / (g(x)^2) $),
  b($ D(f(g(x))) = f'(g(x)) g'(x) $),
)

=== Derivoimiskaavat

#t1(
  b($ D sin x = cos x $),
  b($ D cos x = -sin x $),
  b($ D tan x = 1 + tan^2 x = 1 / (cos^2 x) $),
  b($ D arcsin x = 1 / sqrt(1 - x^2), " " -1 < x < 1 $),
  b($ D arccos x = -1 / sqrt(1 - x^2), " " -1 < x < 1 $),
  b($ D arctan x = 1 / (1 + x^2), " " x in RR $),
  b($ D sinh x = cosh x $),
  b($ D cosh x = sinh x $),
  b($ D sinh^(-1) x = 1 / sqrt(1 + x^2), " " x in RR $),
  b($ D cosh^(-1) x = 1 / sqrt(x^2 - 1), " " x > 1 $),
  b($ D e^x = e^x $),
  b($ D ln abs(x) = 1 / x | x != 0 $),
  b($ D ln fx = (f'(x)) / fx | fx != 0 $),
)

== Integrointi

=== Laskusäännöt

#t1(
  b($ integral_a^a fx dx = 0 $),
  b($ intab fx dx = -integral_b^a fx dx $),
  b($ intab - fx dx = -intab fx dx $),
  b($ intab fx dx = integral_a^c fx dx + integral_c^b fx dx $),
  b($ intab c_1 fx + c_2 gx dx = c_1 intab fx dx + c_2 intab gx dx $),
  b($ fx <= gx => intab fx dx <= intab gx dx $),
)

=== Integroimiskaavoja


#t1(
  b($ integral x^r dx = 1/(r+1) x^(r+1) + C $),
  b($ integral x^(-1) dx = ln abs(x) + C $),
  b($ integral e^x dx = e^x + C $),
  b($ integral sin x dx = - cos x + C $),
  b($ integral cos x dx = sin x + C $),
  b($ integral dx / (1+x^2) = arctan x + C $),
)

=== Geometrisia sovelluksia

#t2(
  [Kuvaajan $y=fx$ kaarenpituus], $ intab sqrt(1+f'(x)^2) dx $,
  [Kuvaajan $y=fx$ x-akselin pyörähdyspinta-ala], $ 2 pi intab abs(fx) sqrt(1+f'(x)^2) dx $,
  [Kuvaajan $y=fx$ x-akselin pyörähdystilavuus], $ pi intab fx^2 dx $,
  [Kuvaajien $y=fx$, $y=gx$ välinen x-akselin pyörähdystilavuus], $ pi intab fx^2 - gx^2 dx $,
  [Kuvaajan $y=fx$ *y*-akselin pyörähdystilavuus], $ 2 pi intab x fx dx $,
)

=== Työkaluja

#t1(
  b($ intab f'(x) gx dx = slash.big_a^b f(x)g(x) - intab fx g'(x) dx $),
  b($ integral f'(x) gx dx = f(x)g(x) - integral fx g'(x) dx $),
  b($ intab f(gx) g'(x) dx = integral_(g(a))^(g(b)) f(u) dif u $),
  b($ intab f(gx) dx = integral_(g(a))^(g(b)) f(u) 1/(g'(x)) dif u $),
)

== Differentiaaliyhtälöt

#t2(
  [Yhtälö], [Ratkaisu],
  $ y' = k y $,$ y = C e^(k x) $,
  $ y' = fx g(y) $,$ integral (dif y) / g(y) = integral fx dx " ja " g(y) = 0 $,
  $ y'' + p y' + q y = 0 ", kun" p, q in RR  $,$ y = e^(lambda x) " ja " lambda^2 + p lambda + q = 0 " kaksoisjuuri: " y = x e^(lambda x) \ "imaginaarijuuri: " \ lambda = a pm b i => y = e^(a x) sin b x " tai " e^(a x) cos b x $,
  $ y' + p(x) y = r(x) $,$ e^(integral p(x) dx) " integroiva tekijä "  $,
  $ y'' + p(x) y' + q(x) y = r(x) $,$ y = C_1 y_1 + C_2 y_2 + y_0 $,
)

== Todennäköisyyslaskenta


#t2(
  [A ja B],$ A inter B $,
  [A tai B],$ A union B $,
  [ei A],$ A^c $,
  [B mutta ei A],$ B without A $,
  [A kun B],$ PP(A|B) = PP(A inter B)/PP(B) $,
  [Monotonisuus],$ PP(A) <= PP(B), " kun" A subset B $,
  [Komplementtien yhdistelmä],$ A^c union B^c = (A inter B)^c $,
  [Yleinen summaussääntö],$ PP(A union B) = PP(A) + PP(B) - PP(A inter B) $,
  [Yleinen tulosääntö],$ PP(A_0 inter A_1 inter ... inter A_n) \ = PP(A_0) PP(A_1|A_0) PP(A_2|A_0 inter A_1)\ ... PP(A_n|A_0 inter A_1 inter ... inter A_(n-1)) $,
  [Bayesin kaava], $ PP(B|A) = (PP(A|B)PP(B))/PP(A) $,
  [Binomikerroin = järjestämättömiä $k$ alkion osajoukkuja voidaan $n$ alkion joukosta muodostaa], $ binom(n,k) = (n!)/(k!(n-k)!) $,
  [Kertymäfunktio], $ F_X (t) = PP(X <= t) $,
  [Tiheysfunktio], $ sum_(x in A) f_X (x) = PP(X in A) $,
  [Kertymäfunktio tiheysfunktion integraalina], $ F_X (x) = PP(X <= x) = integral_(-infinity)^x f_X (t) dif t $,
  [Bernoullijakauman tiheysfunktio], $ f(x) = p^x (1-p)^(n-x), x in {0,1} $,
  [Binomijakauman tiheysfunktio], $ f(x) = binom(n, x) p^x (1-p)^(n-x), x in {0,1,2,...,n} $,
  [Tasajakauman tiheysfunktio], $ f(x) = 1 / (b-a), x in [a,b] $,
  [Exponenttijakauman tiheysfunktio], $ f(x) = cases(lambda e^(-lambda x) " "& x > 0, 0 &x<= 0) $,
  [Normaalijakauman tiheysfunktio], $ f(x) = 1/(sigma sqrt(2 pi)) e^( -(x - mu)^2/(2 sigma^2) ) $,
  [Normaalijakauman kertymäfunktio], $ Phi(x) = 1 / (sigma sqrt(2 pi)) integral_(-infinity)^(x) e^(-((t - mu)^2) / (2 sigma^2)) dif t $,
  [Normitettu normaalijakauman], $ f(x) =  1/sqrt(2 pi) e^( -x^2/2 ) $,
  [Exponenttijakauman kertymäfunktio], $ F(x) = cases(1 - e^(-lambda x) " "& x > 0, 0 &x<= 0) $,
  [Ehdollinen tiheysfunktio], $ f_(Y|X) (y|x) = (f_(X,Y) (x,y)) / (f_X (x)) $,
  [Stokastisesti riippumattomat], $ PP(Y in B | X in A) = PP(Y in B)\ PP(X in A | Y in B) = PP(X in A)\ f_(X,Y) (x,y) = f_X (x) f_Y (y) \ f_(Y|X) (y|x) = f_Y (y) $,
  [Odotusarvo], $ mu = EE(X) = sum_(x in S) x PP(X = x) = sum_(x in S) x f(x) $,
  [Jatkuvan satunnaismuuttujan odotusarvo], $ EE(x) = integral_(-infinity)^infinity x f(x) dif x $,
  [Satunnaisluvun todennäköisyys], $ PP(X in A) = cases(sum_(x in A) f(x), integral_A f(x) dif x) $,
  [Suurten lukujen laki], $ 1/n sum_(i=1)^n X_i = EE(X) pm epsilon $,
  [Suhteellinen esiintyvyys], $ (\# {s in {1,2,...,n} : X_s in B})/n = PP(X in B) pm epsilon $,
  [Odotusarvon muunnoskaava], $ EE(g(X)) = cases(sum_x g(x) f(x), integral_(-infinity)^infinity g(x) f(x) dif x) $,
  [Odotusarvon lineaarisuus], $ EE(X_1 + X_2 + ... + X_n) = EE(X_1) + ... + EE(X_n) $,
  [Odotusarvon skaalautuvuus], $ EE(b X) = b EE(X) $,
  [Kahden satunnaismuuttujan odotusarvo], $ EE(g(X,Y)) = cases(sum_x sum_y g(x,y) f(x,y), integral_(-infinity)^infinity integral_(-infinity)^infinity g(x,y) f(x,y) dif x dif y) $,
  [Itseispoikkeaman odotusarvo eli keskipoikkeama], $ EE(abs(X - mu)) $,
  [Varianssi], $ "Var"(X) = EE((X-mu)^2) = cases(sum_x (x-mu)^2 f(x), integral (x-mu)^2 f(x) dif x) $,
  [Varianssin yhteenlaskukaava], $ "Var"(X+Y) \ = "Var"(X) + 2 "Cov"(X,Y) + "Var"(Y) $,
  [Varianssin skaalautuvuus], $ "Var"(b X) = b^2 "Var"(X) $,
  [Keskihajonta], $ sigma = "SD"(X) = sqrt("Var"(X)) = sqrt(EE(X^2) - mu^2) $,
  [Keskihajonnan skaalautuvuus], $ "SD"(b X) = abs(b) "SD"(X) $,
  [Keskihajonnan liikkuminen], $ "SD"(X + b) = "SD"(X) $,
  [Tsebysovin epäyhtälö], $ PP(X = mu pm r sigma) >= 1 - 1/r^2 "kaikilla" r>=1 $,
  [Kovarianssi], $ "Cov"(X, Y) = EE((X-mu_X)(Y-mu_Y)) \ = sum_x sum_y (x-mu_X)(y-mu_Y) f(x,y) \ = integral_(-infinity)^infinity integral_(-infinity)^infinity (x-mu_X)(y-mu_Y) f(x,y) dif x dif y $,
  [Kovarianssi vahtoehtoinen kaava], $ "Cov"(X,Y) = EE(X Y) - EE(X) EE(Y)  $,
  [Kovarianssin bilinearisuus], $ "Cov"(X,Y) = "Cov"(Y,X) \ "Cov"(X_1 + X_2, Y) = "Cov"(X_1,Y) + "Cov"(X_2,Y) \ "Cov"(b X,Y) = b "Cov"(X,Y) $,
  [Korrelaatio], $ "Cor"(X, Y) = ("Cov"(X,Y))/("SD"(X) "SD"(Y)) $,
  [Satunnaismuuttujien summan keskihajonta], $ "SD"(sum_i X_i) \ = sqrt(sum_i "SD"(X_i)^2 + sum_i sum_(j: j != i) "SD"(X_i) "SD"(X_j) "Cor"(X_i, X_j) ) $,
  [$n$:n riippumattoman summan odotusarvo], $ EE(sum_i^n X_i) = n EE(X_i) $,
  [$n$:n riippumattoman summan keskihajonta], $ "SD"(sum_i^n X_i) = sqrt(n) "SD"(X_i) $,
  [Satunnaismuuttujan $X$ normitus], $ Z = (X - mu)/(sigma) $,
  [Bessel-korjattu otoskeskihajonta], $ "sd"_s (ar(x)) = sqrt(1/(n-1) sum_(i=1)^n (x_i - m(ar(x)))^2 ) $,
  [Bessel-korjattu otosvarianssi], $ "var"_s (ar(x)) = 1/(n-1) sum_(i=1)^n (x_i - m(ar(x)))^2 $,
  [Bessel-korjattu otoskovarianssi], $ "cov"_s (ar(x), ar(y)) = 1/(n-1) sum_(i=1)^n (x_i - m(ar(x)))(y_i - m(ar(y))) $,
  [Uskottavuusfunktio], $ L(theta) = f_theta (x_1) dots f_theta (x_n) $,
  [Luottamusväli odotusarvoparametrille $mu$], $ mu approx m(ar(x)) pm z "sd"(ar(x)) / sqrt(n) $,
  [Luottamusväli $gamma$], $ PP(mu = m(ar(x)) pm z "sd"(ar(x)) / sqrt(n)) \ = PP(-z <= (m(ar(X))-mu)/("sd"(ar(x))/sqrt(n)) <= z) \ = PP(-z <= Z <= z) = gamma $,
  [Luottamusvälin kerroin $z$], $ Phi(z) - Phi(-z) = gamma \ z = Phi^(-1) (1+gamma/2) $,
  [Luottamusväli binaarimallile $p=f(1)$], $ hat(p) pm z sqrt(hat(p)(1 - hat(p)))/sqrt(n) $,
  [Posteriorijakauma], $ f_(Theta|X) (theta|x) = (f_Theta (theta) f_(X|Theta)(x|theta))/(sum_(theta ') f_Theta (theta ') f_(X|Theta)(x|theta)) $,
  [Ennustejakauma], $ f_(Y|X)(y|ar(x)) = integral f_(Y|Theta) (y|theta) f_(Theta|ar(X)) (theta|ar(x)) dif theta $,
  [Betajakauma ($a = \# 1 - 1$, $b = \# 0 - 1$)], $ f(theta) = cases(c^(-1) theta^(a-1) (1-theta)^(b-1)"," &"kun" theta in [0\,1], 0", " &"muuten") \ c = ((a-1)! (b-1)!)/(a+b-1)! $,
  [Bayeslaisen normaalimallin posteriorijakauman parametrin $mu$ jakauma, $sigma$ tunnettu], $ mu_1 = ( 1/sigma_0^2 mu_0 + n/sigma^2 m(ar(x)) )/(1/sigma_0^2 + n/sigma^2) \ sigma_1 = 1/sqrt(1/sigma_0^2 + n/sigma^2) $,
)

= Fysiikka

== Merkintöjä

#t2(
 [Paikka], $ x $,
 [Paikka], $ ar(r) $,
 [Nopeus], $ v $,
 [Kulma], $ theta $,
 [Kulmanopeus /-taajuus], $ omega $,
 [Kulmakiihtyvyys], $ alpha $,
 [Liikemäärä], $ p $,
 [Liikemäärämomentti], $ L $,
 [Kiihtyvyys], $ a $,
 [Säde], $ R $,
 [Massa], $ m $,
 [Hitausmomentti], $ I $,
 [Tiheys], $ rho $,
 [Voima], $ F $,
 [Momentti], $ tau $,
 [Pinnan tukivoima], $ N $,
 [Painovoima], $ G $,
 [Työ], $ W $,
 [Liike-energia], $ K $,
 [Potentiaalienergia], $ U $,
 [Impulssi], $ J $,
 [Amplitudi], $ A $,
 [Taajuus], $ f $,
 [Aallonpituus], $ lambda $,
 [Jaksonaika], $ T $,
 [Lämpömäärä], $ Q $,
 [Lämpötila], $ T $,
 [Ominaislämpökapasiteetti], $ c $,
 [Pituuden lämpölaajenemiskerroin], $ alpha $,
 [Tilavuuden lämpölaajenemiskerroin], $ beta $,
 [Moolimassa], $ M $,
 [Ainemäärä], $ n = m / M $,
 [Pinnan normaalivektori], $ ar(n) $,
)

== Liike

#t2(
  [Keskinopeus], $ v = (Delta x)/(Delta t) $,
  [Hetkellinen nopeus], $ v(t) = (dif x(t)) / (dif t) $,
  [Keskikiihtyvyys], $ a = (Delta v)/(Delta t) $,
  [Hetkellinen kiihtyvyys], $ a(t) = (dif v(t)) / (dif t) = (dif^2 x(t)) / (dif^2 t) $,
  [Paikka: tasainen liike], $ x = x_0 + v t $,
  [Nopeus: tasaisesti kiihtyvä liike], $ v(t) = v_0 + a t $,
  [Paikka: tasaisesti kiihtyvä liike], $ x(t) = x_0 + v_0 t + 1/2 a t^2 $,

)

== Ympyräliike

#t2(
  [Ympyräliikkeen kulmanopeus], $ omega(t) = (dif theta (t))/(dif t) $,
  [Ympyräliikkeen kulmakiihtyvyys], $ ar(alpha)(t) = (dif ar(omega) (t))/(dif t) = (dif omega (t) ar(n))/(dif t) $,
  [Ympyräliikkeen nopeus], $ v = R omega $,
  [Radiaalinen kiihtyvyys], $ a_"rad" = R omega ^ 2 = v^2 / R $,
  [Tangentiaalinen kiihtyvyys], $ a_"tan" = (dif v)/(dif t) = R (dif omega)/(dif t) = R alpha $,
  [Nopeuden kanssa yhdensuuntainen kiihtyvyys], $ ar(a)_"||" = (ar(a) dot ar(v)) / norm(ar(v))^2 ar(v) = norm(ar(a)) cos(angle(ar(a), ar(v))) ar(v) / norm(ar(v)) $,
  [Nopeuden kanssa kohtisuora kiihtyvyys], $ ar(a)_perp = ar(a) - ar(a)_"||" $,
)

== Voima

#t2(
  [Dynamiikan peruslaki], $ ar(F) = m ar(a) $,
  [Paikan muutos tasaisesti kiihtyvässä liikkeessä], $ x_t - x_0 = (v_t^2 - v_0^2) / (2a) $,
  [Kulman muutos tasaisesti kiihtyvässä ympyräliikkeessä], $ theta_t - theta_0 = (omega_t^2 - omega_0^2) / (2 alpha) $,
  [Kitkavoima], $ F_mu = mu N $,
  [*Väliaineen vastus...*], [],
  [...laminaarisesti], $ F_d = k v $,
  [...turbulentisti], $ F_d = D v^2 $,
  [...pallomaiseen kappaleeseen (laminaarinen)], $ F_d = 6 pi mu R v $,
  [...kappaleeseen (turbulentti)], $ F_d = 1/2 rho C_d A v^2 $,
  [Jousen harmoninen voima], $ F = -k x $,
  [Konservatiivinen voima potentiaalienergian avulla], $ F(x) = - (dif U(x))/(dif x) $,
  [Konservatiivinen voima], $ ar(F)(ar(r)) = - (partial U(ar(r))) / (partial x) hat(i) - (partial U(ar(r))) / (partial y) hat(j) - (partial U(ar(r))) / (partial z) hat(k) \ = - nabla U(ar(r)) $,
  [Painovoima], $ F_g = G (m_1 m_2) / (r^2) \ ar(F)_g = G (m_1 m_2)/(norm(ar(r))^2) ar(r)/norm(ar(r)) $,
  [Paine], $ P = F_perp / A $,
  [Paine nesteessä syvyydellä $h$ \ (hydrostaattinen paine)], $ p = p_0 + rho g h $,
  [Nostevoima], $ B = rho_"neste" V g $,
)

== Lämpöoppi

#t2(
  [Lämpömäärä lämpötilanmuutoksissa], $ Q = m c Delta T $,
  [Lämpömäärä olomuodonmuutoksissa], $ Q = m s $,
  [Pituuden lämpölaajeneminen pienissä lämpötilamuutoksissa], $ L = L_0 (1 + alpha Delta T) $,
  [Pituuden lämpölaajeneminen], $ (dif L) / (dif T) = alpha L <=> L(T) = L_0 e^(alpha(T-T_0)) $,
  [Tilavuuden lämpölaajeneminen pienissä lämpötilamuutoksissa], $ V = V_0 (1+ beta Delta T) $,
  [Lämpölaajenemiskertoimien suhde], $ beta approx 3 alpha $,
  [Lämpösäteily \ ($e$ on kappaleen emissiivisyys, $sigma$ luonnonvakio)], $ H = A e sigma T^4 $,
  [Lämpövirta kappaleiden välillä \ ($k$ on lämmönjohtavuus, $L$ etäisyys)], $ H = (dif Q)/(dif T) = k A (T_H - T_C) / L $,
  [Lämpöyhtälö], $ (partial T) / (partial t) = k / (c rho) (partial^2 T) / (partial x^2) $,
  [Lämpöyhtälön perusratkaisu (normaalijakauma), $alpha = k / (c rho)$], $ Phi (x,t) = 1/sqrt(4 alpha t) e^(-(x^2)/(4 alpha t)) $,
  [Diffuusioyhtälö], $ (partial Phi) / (partial t) = D (partial^2 Phi) / (partial x^2) $,
  [Ideaalikaasun tilanyhtälö], $ p V = n R T $,
  [Van Der Waalsin yhtälö \ $a$ ja $b$ kokeelliset vakiot], $ (p + a (n/V)^2)(V - n b) = n R T $,
  [Paineen tekemä työ], $ W = integral_(x_1)^(x_2) p A dif x = integral_(V_1)^(V_2) p dif V $,
  [Sisäenergian muutos], $ Delta U = Q - W $,
  [Adiabaattinen prosessi \ (ei lämmönvaihtoa ympäristön kanssa) \ $gamma = (f+2)/f$, $f$ on kaasun vapausaste] ,$ P_1 V_1^gamma = P_2 V_2^gamma $ ,
  [Lämpövoimakoneen hyötysuhde], $ e = W / Q_H = 1 - abs(Q_C / Q_H) $,
  [Hiukkasten nopeusjakauma kaasussa, $k$ on Boltzmannin vakio], $ f(v) = 4 pi (m/(2 pi k T))^(3/2) v^2 e^(-(m v^2)/(2 k T)) $,
  [$N$ hiukkasen systeemi, $n$ vapausastetta], $ Q = N n/2 k Delta T $,
  [Systeemin ominaislämpökapasiteetti], $ c = Q / (m Delta T) = n / 2 N / m k = n / 2 R / M $,
  [Entropia \ $k$ on Boltzmannin vakio, $w$ on tilojen lkm], $ S = k ln(w) $,
  [Tilavuuden muutoksen tuoma epäjärestyksen muutos], $ Delta S = integral_(V_1)^V_2 k N (dif V) / V $,
  [Entropian muutos lämpömäärän muutoksen avulla \ tilasta 1 tilaan 2], $ Delta S = integral_(1)^2 (dif Q) / T = m c integral_(T_1)^T_2 (dif T) / T = m c ln(T_2/T_1) $,
)

== Sähkö ja magnetismi

#t2(
  [Coulombin laki], $ ar(F)_1 = 1/(4 pi epsilon_0) (q_1 q) / norm(ar(r))^2 ar(r) / norm(r) $,
  [Sähkökenttä], $ ar(E) = ar(F) / q $,
  [Dipolimomentti], $ p = q r  $,
  [Dipolin kokonäisvääntömomentti], $ ar(tau) = ar(x) times ar(E) $,
  [Sähködipolin potentiaalienergia], $ U = - ar(p) dot ar(E) $,
  [Sähkövuo], $ Phi_E = ar(E) dot ar(A) = ar(E) dot A ar(n) = E_perp A $,
  [Sähkövuo (epätasainen)], $ Phi_E = integral ar(E) dot dif ar(A) = integral E_perp dif A $,
  [Pistevarauksen vuo pallopinnan läpi], $ Phi_E = integral ar(E) dot dif ar(A) = E A = q/(4 pi epsilon_0 r^2) (4 pi r^2) = q / epsilon_0 $,
  [Gaussin laki], $ Phi_E = integral.cont ar(E) dot dif ar(A) = Q_"encl" / epsilon_0 $,
  [Pistevarauksen sähkökenttä], $ ar(E) = 1/(4 pi epsilon_0) q/r^2 hat(r) $,
  [Äärettömän viivavarauksen sähkökenttä, \ $lambda$ on varaus / pituus], $ ar(E) = 1/(2 pi epsilon_0) lambda/r hat(r) $,
  [Äärettömän tasovarauksen sähkökenttä, \ $sigma$ on varaus / pinta-ala], $ ar(E) = sigma / ( 2 epsilon_0) ar(n) = 1/(2 epsilon_0) sigma / (r_0) hat(r) $,
  [$R$-säteisen varauspallon (ei johdepallo) sähkökenttä], $ cases(ar(E) = 1/(4 pi epsilon_0) Q/r^2 hat(r)&", " r>R, ar(E) = 1/(4 pi epsilon_0) (Q r)/R^3 hat(r)&", " r<R) $,
  [Johdepinnan paikallinen sähkökenttä], $ E_perp = sigma / epsilon_0 $,
  [Pistevarauksen $q_0$ potentiaalienergia], $ U = 1/(4 pi epsilon_0) (q q_0) / r $,
  [Potentiaali], $ V = U / q_0 $,
  [Potentiaalin superpositio], $ V = 1 / (4 pi epsilon_0) sum_i q_i / r_i ( = 1 / (4 pi epsilon_0) integral (dif q) / r ) $,
  [Jatkuvan varausjakauman potentiaali], $ V = 1/(4 pi epsilon_0) integral (dif q) / r $,
  [Sähkökentän tekemä työ], $ W_(a -> b) = integral_a^b ar(F) dot dif ar(l) = q_0 integral_a^b ar(E) dif ar(l) = q_1 V_(a b) $,
  [Jännite], $ V_(a b) = integral_a^b ar(E) dot dif ar(l) ( = integral_(r_a)^(r_b) E_r dif r ) $,
  [Potentiaaligradientti], $ ar(E) = - nabla V = -( (partial V) / (partial x) hat(i) + (partial V) / (partial y) hat(j) + (partial V) / (partial z) hat(k)  ) $,
  [Etäisyys pallon keskipisteestä tai sylinterin akselista], $ ar(E) (r) = - nabla V(r) = - (partial V) / (partial r) hat(r) $,
)

== Momentti

#t2(
  [Voiman momentti], $ tau = F_perp l $,
  [Voiman momentti], $ ar(tau) = ar(F) times ar(r) $,
  [Voiman momentti ja kulmakiihtyvyys], $ sum tau_y = I alpha_y $,
  [Massakeskipiste], $ ar(r)_"cm" = (sum_i m_i ar(r)_i)/(sum_i m_i) $,
  [Massakeskipiste jatkuvalle aineelle], $ ar(r)_"cm" = (integral integral integral rho(x,y,z) x dif x dif y dif z) / (integral integral integral rho(x,y,z) dif x dif y dif z) $,
  [Kappaleiden yhteinen massakeskipiste], $ ar(r)_"cm,AB" = (M_"A" ar(r)_"cm,A" + M_"B" ar(r)_"cm,B") / (M_"A" + M_"B") $,
)

== Energia, työ ja teho

#t2(
  [Jousen potentiaalienergia], $ W = 1/2 k X^2 $,
  [Keskimääräinen teho], $ P_"av" = (Delta W) / (Delta t) $,
  [Hetkellinen teho], $ P = (dif W(t))/(dif t) = ar(F) dot ar(v) $,
  [Työ suoraviivaisessa liikkeessä (vakiovoima)], $ W = ar(F) dot ar(s)  $,
  [Työ suoraviivaisessa liikkeessä], $ W = integral_(x_1)^x_2 F(x) dif x = integral_(t_1)^t_2 F(t) v(t) dif t $,
  [Työ kaarevassa liikkeessä], $ W = integral_(ar(r)_1)^(ar(r)_2) ar(F)(ar(r)) dot dif ar(r) = integral_(s_1)^s_2 F(ar(r)(s)) dot (dif ar(r)(s)) / (dif s) dif s $,
  [Liike-energia], $ K = 1/2 m v^2 $,
  [Pyörimisliikkeen energia], $ K = 1/2 I omega^2 $,
  [Jäykän kappaleen liike-energia], $ K = 1/2 M v_"cm"^2 + 1/2 I_"cm" omega^2 $,
  [Vakiomomentin tekemä työ], $ W = tau Delta theta $,
  [Muuttuvan momentin tekemä työ], $ W = integral_(theta_1)^(theta_2) tau (theta) dif theta = integral_(omega_1)^omega_2 I omega dif omega $,
  [Teho ympyräliikkeessä], $ P = (dif W)/(dif t) = I alpha omega = tau omega $,
  [Painovoiman potentiaalienergia lähellä maanpintaa], $ U_"grav" = m g h $,
  [Painovoiman potentiaalienergia], $ U_"grav" = -G (M m)/r $,
  [Jousen tekemä työ matkan $X$ aikana], $ W = -1/2 k X^2 $,
  [Työperiaate], $ W = K_2 - K_1 = Delta K $,
  [Mekaaninen kokonaisenergia], $ E = K + U $,
  [Energian säilymislaki], $ Delta K + Delta U + Delta U_"int" = 0 $,
)

== Hitausmomentteja

#t2(
  [Hitausmomentti yhdensuuntaisen akselin suhteen], $ I = I_"cm" + m r^2 $,
  [Pistemäisille massoille], $ I = sum_i m_i R_1^2 $,
  [Jatkuvan aineen hitausmomentti], $ I = integral integral integral rho(x,y,z) norm(ar(r))^2 dif x dif y dif z $,
  [Ohut tanko (pituus L, keskipisteen ympäri)], $ I = 1/12 m L^2 $,
  [Ohut tanko (pituus L, pään ympäri)], $ I = 1/3 m L^2 $,
  [Ohutseinäinen ontto sylinteri (säde R, keskiakselin ympäri)], $ I = m R^2 $,
  [Osittain ontto sylinteri ("ontto" säde $R_1$, "koko" säde $R_2$, keskiakselin ympäri)], $ I = 1/2 m (R_1^2 + R_2^2) $,
  [Kiinteä sylinteri (säde R, keskiakselin ympäri)], $ I = 1/2 m R^2 $,
  [Ohutseinäinen ontto pallo (säde R)], $ I = 2/3 m R^2 $,
  [Kiinteä pallo (säde R)], $ I = 2/5 m R^2 $,
  [Suorakulmainen taso (sivut a,b, keskiakselin ympäri)], $ I = 1/12 m (a^2 + b^2) $,
  [Suorakulmainen taso (sivut a,b, b-sivun ympäri)], $ I = 1/3 m a^2 $,
)

== Liikemäärä ja impulssi

#t2(
  [Liikemäärä], $ ar(p) = m ar(v) $,
  [Newton II liikemäärällä], $ sum ar(F) = (dif ar(p)) / (dif t) $,
  [Vakiovoiman impulssi], $ ar(J) = ar(F) Delta t = Delta ar(p) $,
  [Impulssi], $ ar(J) = integral_(t_1)^t_2 ar(F)(t) dif t = Delta ar(p) $,
  [Liikemäärän säilymislaki], $ ar(p)_A_1 + ar(p)_B_1 = ar(p)_A_2 + ar(p)_B_2 $,
)

== Liikemäärämomentti


#t2(
  [Pistehiukkasen liikemäärämomentti], $ ar(L) = ar(r) times ar(p) $,
  [Pistehiukkasen liikemäärämomentin suuruus], $ L = m v r sin(angle(ar(r), ar(p))) = m v l $,
  [Jäykän kappaleen liikemäärämomentti], $ ar(L) = I ar(omega) $,
  [Kokonaismomentin vaikutus liikemäärämomenttiin], $ sum tau = (dif L_"tot")/(dif t) $,
  [Liikemäärämomentin säilymislaki], $ ar(L)_A_1 + ar(L)_B_1 = ar(L)_A_2 + ar(L)_B_2 ", kun " sum tau = 0 $,
  [Prekession kulmanopeus], $ Omega = lim_(Delta t -> 0) (Delta theta) / (Delta t) = (dif theta) / (dif t) = tau / L = (F r) / (I omega) $,
)

== Harmoninen liike

#t2(
  [Jousen harmoninen voima], $ F = -k x $,
  [Yksinkertaisen harmonisen liikkeen liikeyhtälö], $ (dif^2 x)/(dif t^2) = - k/m x = -omega^2 x $,
  [Kulmataajuus], $ omega = sqrt(k / m) $,
  [Yksinkertaisen liikeyhtälön ratkaisu], $ x(t) = A cos(omega t + theta_0) $,
  [Mekaaninen kokonaisenergia], $ E = 1/2 k A^2 = 1/2 m v^2 + 1/2 k x^2 $,
  [Ideaaliheilurin liikeyhtälö], $ (dif^2 x)/(dif t^2) = F_theta / m = -g sin(theta) = -g sin(x/r) approx -g/r x $,
  [Heilurin liikeyhtälö], $ (dif^2 theta)/(dif t^2) = alpha = tau / I = - (m g r) / I sin theta approx - (m g r) / I theta $,
  [Suurten heilahtelukulmien liikeyhtälö\ (potetentiaalienergia ympyrän kaaren mukaisesti)], $ K = - Delta U = m g r (cos theta_0 - cos theta) = 1/2 m (r omega)^2 $,
  [Vaimennetun värähtelijän kiihtyvyys], $ a = - b/m v - k/m x $,
  [Vaimennetun värähtelijän liikeyhtälö], $ (dif^2 x)/(dif t^2) + b/m (dif x)/(dif t) + k/m x = 0 $,
  [Vaimennetun värähtelijän liikeyhtälön ratkaisu], $ x(t) = A cos(omega t) e^(-lambda t) \ lambda = b/(2m) \ omega = sqrt(k/m - b^2/(4m^2)) $,
  [Vaimennetun värähtelijan mekaanisen kokonaisenergian muutos], $ (dif E)/(dif t) = -b v^2 $,
  [Pakotettu harmoninen värähtely], $ F(t) = F_"max" cos(omega_d t) $,
  [Pakotetun värähtelijän amplitudi], $ A = F_"max" / sqrt((k-m omega_d^2)^2 + b^2 omega_d^2) $,
)

== Aaltoliike

#t2(
  [*Siniaallon*...], $ y(x, t) = A cos(k x - omega t) $,
  [...taajuus], $ f = 1/T $,
  [...kulmataajuus], $ omega = 2 pi f $,
  [...aaltoluku], $ 1 / lambda $,
  [...kulmaaaltoluku], $ k = (2 pi) / lambda $,
  [...vaihenopeus], $ v = lambda / T = lambda f = omega / k $,
  [Aaltoyhtälö], $ (partial^2 y)/(partial x^2) (x, t) = 1/v^2 (partial^2 y)/(partial t^2) (x,t) $,
  [Poikittaiset aallot narussa. ($[mu] = "kg/m"$)], $ v = sqrt(F / mu) $,
  [Narun aaltoliikkeen hetkellinen teho], $ P(x,t) = -F (partial y)/(partial x) (x,t) (partial y)/(partial t) (x,t) \ = sqrt(mu F) omega^2 A^2 sin^2(k x - omega t) $,
  [Maksimiteho], $ P_"max" = sqrt(mu F) omega^2 A^2 $,
  [Keskimääräinen teho], $ P_"av" = 1/2 P_"max" = lim_(T->infinity) integral_0^T P(x, t) dif t $,
  [Reunaehto rajapinnassa AB], $ y_A(a,t) = y_B(a,t) " ja " (partial y_A)/(partial x)(a,t) = (partial y_B)/(partial x)(a,t) $,
  ["Narun pää kiinnitetty", vaihe-ero $pi$], $ y(a,t) = 0 $,
  ["Narun pää kokonaan irti", ei vaihe-eroa], $ (partial y)/(partial x)(a,t) = 0 $,
  [Aaltojen superpositio], $ y(x,t) = y_1 (x,t) + y_2 (x,t) $,
  [Seisova aalto], $ y(x,t) = A sin(k x - omega t) + A sin(k x + omega t) \ = 2 A cos(omega t) sin(k x) $,
)

== Planeettojen liikeyhtälö

#t2(
  [Planeetan liikeyhtälö], $ m (dif^2 ar(r))/(dif t^2) = -G (M m)/(norm(ar(r))^2) ar(r)/norm(ar(r)) $,
  [Liikemäärämomentti], $ L = m r v_perp = m r^2 (dif theta) / (dif t) $,
  [Planeetan nopeusvektori], $ ar(v) = (dif r) / (dif t) = dif / (dif t) (r cos(theta) hat(i) + r sin(theta) hat(j)) $,
  [Elliptinen rata \ ($a$ on ellipsin isoakselin säde)], $ a(1 - epsilon^2) = L^2 / (G M m^2) $,
)
