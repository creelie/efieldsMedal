#!/usr/bin/env bash
# check_examples.sh -- Examples 1.5 and 1.6 of "Regular Morley tetrahedra from p-secting
# planes" with bc at 60 digits.  For each edge of the face F_A, the parameter p given in
# closed form must satisfy R_p(theta) = sin((p-1)theta/p)/sin(theta/p) = rho, where rho is
# the ratio d_Y/d_A at the stated vertex A' (eq. (3.2)) and cos(theta) comes from (3.1).
# (bc gives unary minus precedence over ^, so -x^2 is written 0 - x^2 or reordered.)
# Prints ALL OK on success.   bash check_examples.sh
set -euo pipefail

# each check: a name and a bc expression that must vanish to 50 digits
checks=(
  "Example 1.5: cos theta_CD = -23/49|abs(ccd + 23/49)"
  "Example 1.5: cos theta_BD = 31/49|abs(cbd - 31/49)"
  "Example 1.5: cos theta_BC = 41/49|abs(cbc - 41/49)"
  "Example 1.5: lambda = 3/5|abs(lam - 3/5)"
  "Example 1.5: R_e(theta_CD) = 1 + 2(beta+gamma)lambda = 2|abs(rp(e, acos(ccd)) - (1 + 2 * (be + ga) * lam))"
  "Example 1.5: R_g(theta_BD) = 1 + 2(alpha+gamma)lambda = 13/5|abs(rp(g, acos(cbd)) - (1 + 2 * (al + ga) * lam))"
  "Example 1.5: R_f(theta_BC) = 1 + 2(alpha+beta)lambda = 14/5|abs(rp(f, acos(cbc)) - (1 + 2 * (al + be) * lam))"
  "SWITCH"
  "Example 1.6: cos theta_CD = 19/21|abs(ccd - 19/21)"
  "Example 1.6: cos theta_BD = 13/21|abs(cbd - 13/21)"
  "Example 1.6: cos theta_BC = -11/21|abs(cbc + 11/21)"
  "Example 1.6: t = lambda/(1 + 7 lambda/4)|abs(t - lam / (1 + 7/4 * lam))"
  "Example 1.6: R_4(theta_CD) = 1 + 2(beta+gamma)lambda|abs(rp(4, acos(ccd)) - (1 + 2 * (be + ga) * lam))"
  "Example 1.6: R_4(theta_BC) = 1 + 2(alpha+beta)lambda|abs(rp(4, acos(cbc)) - (1 + 2 * (al + be) * lam))"
  "Example 1.6: R_g(theta_BD) = 1 + 2(alpha+gamma)lambda|abs(rp(g, acos(cbd)) - (1 + 2 * (al + ga) * lam))"
)

prog='scale = 60
define acos(x) { return 2 * a(sqrt((1 - x) / (1 + x))); }
define rp(p, t) { return s((p - 1) * t / p) / s(t / p); }
define abs(x) { if (x < 0) return -x; return x; }
/* Example 1.5: (alpha, beta, gamma) = (1, 1/2, 1/3), X = -(2/7)(1,1,1) */
al = 1; be = 1/2; ga = 1/3
n2 = al^2 + be^2 + ga^2
ccd = (be^2 + ga^2 - al^2) / n2; cbd = (al^2 - be^2 + ga^2) / n2; cbc = (al^2 + be^2 - ga^2) / n2
t = 2/7; lam = t / (1 - t * (al + be + ga))
e = acos(-23/49) / a(4 * sqrt(13) / 25)
f = acos(41/49) / a(20 * sqrt(5) / 297)
g = acos(31/49) / a(5 * sqrt(10) / 66)
'
switch='/* Example 1.6: (alpha, beta, gamma) = (1/4, 1/2, 1), e = f = 4 */
al = 1/4; be = 1/2; ga = 1
n2 = al^2 + be^2 + ga^2
ccd = (be^2 + ga^2 - al^2) / n2; cbd = (al^2 - be^2 + ga^2) / n2; cbc = (al^2 + be^2 - ga^2) / n2
r = sqrt(5/21); lam = 4/3 * r; t = 5/2 - 9/2 * r
g = acos(13/21) / a(2 * sqrt(17) / (17 + 35 * r))
'
for c in "${checks[@]}"; do
  if [ "$c" = SWITCH ]; then prog+="$switch"; continue; fi
  prog+="if (${c#*|} < 10^-50) print \"ok\n\" else print \"FAIL\n\"
"
done
prog+='print "e15 ", e, "\n"; print "g16 ", g, "\n"; print "s16 ", t, "\n"
'

out=$(bc -l <<< "$prog" 2>&1)
if grep -q "error" <<< "$out"; then echo "bc error:"; echo "$out"; exit 1; fi
mapfile -t res < <(grep -E "^(ok|FAIL)$" <<< "$out")
fails=0; i=0
for c in "${checks[@]}"; do
  [ "$c" = SWITCH ] && continue
  printf '%-6s%s\n' "${res[$i]}" "${c%%|*}"
  [ "${res[$i]}" = ok ] || fails=$((fails + 1))
  i=$((i + 1))
done
grep -E "^(e15|g16|s16) " <<< "$out" | sed 's/^e15/      Example 1.5: e =/; s/^g16/      Example 1.6: g =/; s/^s16/      Example 1.6: s =/' | cut -c1-60
if [ "$fails" -eq 0 ] && [ "$i" -eq 14 ]; then echo "ALL OK"; else echo "$fails FAILED"; exit 1; fi
