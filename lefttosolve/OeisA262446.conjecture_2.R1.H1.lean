import OMAReductions.R_OeisA262446_conjecture_2_R1

/-!
# Step H1 of the reduction OeisA262446.conjecture_2.R1

At the seven indices 4, 6, 11, 21, 54, 253 and 325 the count `a n` equals one.

Proof: a trial-division primality test `a262446Pr` is proved equivalent to `Nat.Prime` below
`252 ^ 2`, which gives a certified way to count primes in an interval. A table `a262446Tbl`
(a binary decision tree on k) lists the values `b k` for `k ≤ 325`; the kernel checks, in
chunks of 25, that consecutive entries differ by the number of primes in the interval between
consecutive triangular numbers, which identifies the table with `b` by induction. Finally `a n`
is rewritten with the table and evaluated by the kernel.
-/

namespace OMA.Helpers

/-- Trial division by `d, d + 1, ...` while `d * d ≤ n`, with fuel `f`. -/
def a262446Chk (n : ℕ) : ℕ → ℕ → Bool
  | 0, d => Nat.blt n (d * d)
  | f + 1, d => bif Nat.blt n (d * d) then true
      else bif Nat.beq (n % d) 0 then false else a262446Chk n f (d + 1)

theorem a262446Chk_sound (n : ℕ) : ∀ f d, a262446Chk n f d = true →
    ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro f
  induction f with
  | zero =>
    intro d h m hdm hmn _
    have h' : n < d * d := by simpa [a262446Chk] using h
    have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
    omega
  | succ f ih =>
    intro d h m hdm hmn hdvd
    by_cases h1 : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · have hb1 : Nat.blt n (d * d) = false := by
        cases hb : Nat.blt n (d * d)
        · rfl
        · exact absurd (by simpa using hb) h1
      by_cases h2 : n % d = 0
      · have hb2 : Nat.beq (n % d) 0 = true := by simpa using h2
        simp [a262446Chk, hb1, hb2] at h
      · have hb2 : Nat.beq (n % d) 0 = false := by
          cases hb : Nat.beq (n % d) 0
          · rfl
          · exact absurd (by simpa using hb) h2
        have h' : a262446Chk n f (d + 1) = true := by simpa [a262446Chk, hb1, hb2] using h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 1) h' m hlt hmn hdvd

theorem a262446Chk_complete (n : ℕ) : ∀ f d, n < (d + f) * (d + f) →
    (∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n) → a262446Chk n f d = true := by
  intro f
  induction f with
  | zero =>
    intro d hn _
    simpa [a262446Chk] using hn
  | succ f ih =>
    intro d hn hm
    by_cases h1 : n < d * d
    · have hb1 : Nat.blt n (d * d) = true := by simpa using h1
      simp [a262446Chk, hb1]
    · have hb1 : Nat.blt n (d * d) = false := by
        cases hb : Nat.blt n (d * d)
        · rfl
        · exact absurd (by simpa using hb) h1
      have h2 : ¬ n % d = 0 := by
        intro h0
        exact hm d le_rfl (by omega) (Nat.dvd_of_mod_eq_zero h0)
      have hb2 : Nat.beq (n % d) 0 = false := by
        cases hb : Nat.beq (n % d) 0
        · rfl
        · exact absurd (by simpa using hb) h2
      simp only [a262446Chk, hb1, hb2, cond_false]
      apply ih (d + 1) (by rw [show d + 1 + f = d + (f + 1) by omega]; exact hn)
      intro m hdm hmn
      exact hm m (by omega) hmn

/-- Trial-division primality test, correct below `252 ^ 2`. -/
def a262446Pr (n : ℕ) : Bool := Nat.ble 2 n && a262446Chk n 250 2

theorem a262446Pr_iff (n : ℕ) (hn : n < 252 * 252) : a262446Pr n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [a262446Pr, Bool.and_eq_true, Nat.ble_eq, Nat.le_sqrt]
  constructor
  · rintro ⟨h2, hc⟩
    exact ⟨h2, fun m hm hmn => a262446Chk_sound n 250 2 hc m hm hmn⟩
  · rintro ⟨h2, hc⟩
    exact ⟨h2, a262446Chk_complete n 250 2 hn hc⟩

/-- Number of primes in `[s, s + l)`. -/
def a262446Cnt (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | l + 1 => a262446Cnt s l + (bif a262446Pr (s + l) then 1 else 0)

theorem a262446_count_add (s l : ℕ) (hsl : s + l ≤ 252 * 252) :
    Nat.count Nat.Prime (s + l) = Nat.count Nat.Prime s + a262446Cnt s l := by
  induction l with
  | zero => simp [a262446Cnt]
  | succ l ih =>
    rw [← Nat.add_assoc, Nat.count_succ, ih (by omega), a262446Cnt, Nat.add_assoc]
    congr 2
    by_cases h : (s + l).Prime
    · simp [h, (a262446Pr_iff (s + l) (by omega)).mpr h]
    · have h' : a262446Pr (s + l) = false := by
        cases hp : a262446Pr (s + l)
        · rfl
        · exact absurd ((a262446Pr_iff _ (by omega)).mp hp) h
      simp [h, h']

/-- The values `b k` for `k ≤ 325`, as a binary decision tree. -/
def a262446Tbl (k : ℕ) : ℕ :=
    if k < 163 then
      if k < 81 then
        if k < 40 then
          if k < 20 then
            if k < 10 then
              if k < 5 then
                if k < 2 then
                  if k < 1 then
                    0
                  else
                    1
                else
                  if k < 3 then
                    2
                  else
                    if k < 4 then
                      4
                    else
                      5
              else
                if k < 7 then
                  if k < 6 then
                    6
                  else
                    8
                else
                  if k < 8 then
                    10
                  else
                    if k < 9 then
                      12
                    else
                      14
            else
              if k < 15 then
                if k < 12 then
                  if k < 11 then
                    16
                  else
                    19
                else
                  if k < 13 then
                    22
                  else
                    if k < 14 then
                      24
                    else
                      27
              else
                if k < 17 then
                  if k < 16 then
                    30
                  else
                    33
                else
                  if k < 18 then
                    36
                  else
                    if k < 19 then
                      39
                    else
                      43
          else
            if k < 30 then
              if k < 25 then
                if k < 22 then
                  if k < 21 then
                    47
                  else
                    50
                else
                  if k < 23 then
                    54
                  else
                    if k < 24 then
                      59
                    else
                      62
              else
                if k < 27 then
                  if k < 26 then
                    66
                  else
                    70
                else
                  if k < 28 then
                    75
                  else
                    if k < 29 then
                      79
                    else
                      84
            else
              if k < 35 then
                if k < 32 then
                  if k < 31 then
                    90
                  else
                    94
                else
                  if k < 33 then
                    99
                  else
                    if k < 34 then
                      102
                    else
                      108
              else
                if k < 37 then
                  if k < 36 then
                    115
                  else
                    121
                else
                  if k < 38 then
                    126
                  else
                    if k < 39 then
                      131
                    else
                      137
        else
          if k < 60 then
            if k < 50 then
              if k < 45 then
                if k < 42 then
                  if k < 41 then
                    142
                  else
                    149
                else
                  if k < 43 then
                    154
                  else
                    if k < 44 then
                      161
                    else
                      167
              else
                if k < 47 then
                  if k < 46 then
                    174
                  else
                    180
                else
                  if k < 48 then
                    189
                  else
                    if k < 49 then
                      193
                    else
                      200
            else
              if k < 55 then
                if k < 52 then
                  if k < 51 then
                    205
                  else
                    217
                else
                  if k < 53 then
                    220
                  else
                    if k < 54 then
                      226
                    else
                      235
              else
                if k < 57 then
                  if k < 56 then
                    242
                  else
                    251
                else
                  if k < 58 then
                    259
                  else
                    if k < 59 then
                      267
                    else
                      274
          else
            if k < 70 then
              if k < 65 then
                if k < 62 then
                  if k < 61 then
                    282
                  else
                    290
                else
                  if k < 63 then
                    297
                  else
                    if k < 64 then
                      306
                    else
                      313
              else
                if k < 67 then
                  if k < 66 then
                    324
                  else
                    329
                else
                  if k < 68 then
                    338
                  else
                    if k < 69 then
                      348
                    else
                      358
            else
              if k < 75 then
                if k < 72 then
                  if k < 71 then
                    367
                  else
                    375
                else
                  if k < 73 then
                    381
                  else
                    if k < 74 then
                      393
                    else
                      403
              else
                if k < 78 then
                  if k < 76 then
                    414
                  else
                    if k < 77 then
                      423
                    else
                      431
                else
                  if k < 79 then
                    440
                  else
                    if k < 80 then
                      446
                    else
                      457
      else
        if k < 122 then
          if k < 101 then
            if k < 91 then
              if k < 86 then
                if k < 83 then
                  if k < 82 then
                    467
                  else
                    478
                else
                  if k < 84 then
                    487
                  else
                    if k < 85 then
                      500
                    else
                      510
              else
                if k < 88 then
                  if k < 87 then
                    522
                  else
                    531
                else
                  if k < 89 then
                    542
                  else
                    if k < 90 then
                      552
                    else
                      564
            else
              if k < 96 then
                if k < 93 then
                  if k < 92 then
                    574
                  else
                    587
                else
                  if k < 94 then
                    596
                  else
                    if k < 95 then
                      607
                    else
                      618
              else
                if k < 98 then
                  if k < 97 then
                    630
                  else
                    640
                else
                  if k < 99 then
                    650
                  else
                    if k < 100 then
                      662
                    else
                      676
          else
            if k < 111 then
              if k < 106 then
                if k < 103 then
                  if k < 102 then
                    686
                  else
                    697
                else
                  if k < 104 then
                    708
                  else
                    if k < 105 then
                      721
                    else
                      734
              else
                if k < 108 then
                  if k < 107 then
                    747
                  else
                    758
                else
                  if k < 109 then
                    775
                  else
                    if k < 110 then
                      783
                    else
                      796
            else
              if k < 116 then
                if k < 113 then
                  if k < 112 then
                    809
                  else
                    824
                else
                  if k < 114 then
                    836
                  else
                    if k < 115 then
                      847
                    else
                      859
              else
                if k < 119 then
                  if k < 117 then
                    873
                  else
                    if k < 118 then
                      887
                    else
                      903
                else
                  if k < 120 then
                    914
                  else
                    if k < 121 then
                      928
                    else
                      938
        else
          if k < 142 then
            if k < 132 then
              if k < 127 then
                if k < 124 then
                  if k < 123 then
                    950
                  else
                    968
                else
                  if k < 125 then
                    982
                  else
                    if k < 126 then
                      994
                    else
                      1007
              else
                if k < 129 then
                  if k < 128 then
                    1022
                  else
                    1035
                else
                  if k < 130 then
                    1049
                  else
                    if k < 131 then
                      1061
                    else
                      1077
            else
              if k < 137 then
                if k < 134 then
                  if k < 133 then
                    1094
                  else
                    1108
                else
                  if k < 135 then
                    1124
                  else
                    if k < 136 then
                      1138
                    else
                      1152
              else
                if k < 139 then
                  if k < 138 then
                    1170
                  else
                    1184
                else
                  if k < 140 then
                    1199
                  else
                    if k < 141 then
                      1218
                    else
                      1231
          else
            if k < 152 then
              if k < 147 then
                if k < 144 then
                  if k < 143 then
                    1246
                  else
                    1262
                else
                  if k < 145 then
                    1277
                  else
                    if k < 146 then
                      1290
                    else
                      1308
              else
                if k < 149 then
                  if k < 148 then
                    1322
                  else
                    1337
                else
                  if k < 150 then
                    1354
                  else
                    if k < 151 then
                      1369
                    else
                      1383
            else
              if k < 157 then
                if k < 154 then
                  if k < 153 then
                    1398
                  else
                    1411
                else
                  if k < 155 then
                    1430
                  else
                    if k < 156 then
                      1446
                    else
                      1463
              else
                if k < 160 then
                  if k < 158 then
                    1480
                  else
                    if k < 159 then
                      1500
                    else
                      1519
                else
                  if k < 161 then
                    1532
                  else
                    if k < 162 then
                      1553
                    else
                      1570
    else
      if k < 244 then
        if k < 203 then
          if k < 183 then
            if k < 173 then
              if k < 168 then
                if k < 165 then
                  if k < 164 then
                    1586
                  else
                    1602
                else
                  if k < 166 then
                    1619
                  else
                    if k < 167 then
                      1637
                    else
                      1655
              else
                if k < 170 then
                  if k < 169 then
                    1670
                  else
                    1683
                else
                  if k < 171 then
                    1701
                  else
                    if k < 172 then
                      1720
                    else
                      1743
            else
              if k < 178 then
                if k < 175 then
                  if k < 174 then
                    1757
                  else
                    1776
                else
                  if k < 176 then
                    1800
                  else
                    if k < 177 then
                      1816
                    else
                      1837
              else
                if k < 180 then
                  if k < 179 then
                    1857
                  else
                    1876
                else
                  if k < 181 then
                    1891
                  else
                    if k < 182 then
                      1908
                    else
                      1926
          else
            if k < 193 then
              if k < 188 then
                if k < 185 then
                  if k < 184 then
                    1943
                  else
                    1962
                else
                  if k < 186 then
                    1981
                  else
                    if k < 187 then
                      2000
                    else
                      2021
              else
                if k < 190 then
                  if k < 189 then
                    2039
                  else
                    2057
                else
                  if k < 191 then
                    2080
                  else
                    if k < 192 then
                      2101
                    else
                      2122
            else
              if k < 198 then
                if k < 195 then
                  if k < 194 then
                    2137
                  else
                    2152
                else
                  if k < 196 then
                    2169
                  else
                    if k < 197 then
                      2188
                    else
                      2213
              else
                if k < 200 then
                  if k < 199 then
                    2230
                  else
                    2250
                else
                  if k < 201 then
                    2272
                  else
                    if k < 202 then
                      2293
                    else
                      2313
        else
          if k < 223 then
            if k < 213 then
              if k < 208 then
                if k < 205 then
                  if k < 204 then
                    2331
                  else
                    2352
                else
                  if k < 206 then
                    2373
                  else
                    if k < 207 then
                      2394
                    else
                      2417
              else
                if k < 210 then
                  if k < 209 then
                    2438
                  else
                    2460
                else
                  if k < 211 then
                    2484
                  else
                    if k < 212 then
                      2503
                    else
                      2524
            else
              if k < 218 then
                if k < 215 then
                  if k < 214 then
                    2547
                  else
                    2565
                else
                  if k < 216 then
                    2591
                  else
                    if k < 217 then
                      2609
                    else
                      2631
              else
                if k < 220 then
                  if k < 219 then
                    2654
                  else
                    2680
                else
                  if k < 221 then
                    2700
                  else
                    if k < 222 then
                      2721
                    else
                      2738
          else
            if k < 233 then
              if k < 228 then
                if k < 225 then
                  if k < 224 then
                    2760
                  else
                    2781
                else
                  if k < 226 then
                    2803
                  else
                    if k < 227 then
                      2825
                    else
                      2847
              else
                if k < 230 then
                  if k < 229 then
                    2869
                  else
                    2893
                else
                  if k < 231 then
                    2915
                  else
                    if k < 232 then
                      2939
                    else
                      2963
            else
              if k < 238 then
                if k < 235 then
                  if k < 234 then
                    2984
                  else
                    3004
                else
                  if k < 236 then
                    3022
                  else
                    if k < 237 then
                      3053
                    else
                      3074
              else
                if k < 241 then
                  if k < 239 then
                    3095
                  else
                    if k < 240 then
                      3124
                    else
                      3148
                else
                  if k < 242 then
                    3169
                  else
                    if k < 243 then
                      3195
                    else
                      3217
      else
        if k < 285 then
          if k < 264 then
            if k < 254 then
              if k < 249 then
                if k < 246 then
                  if k < 245 then
                    3238
                  else
                    3259
                else
                  if k < 247 then
                    3282
                  else
                    if k < 248 then
                      3302
                    else
                      3330
              else
                if k < 251 then
                  if k < 250 then
                    3352
                  else
                    3380
                else
                  if k < 252 then
                    3402
                  else
                    if k < 253 then
                      3424
                    else
                      3447
            else
              if k < 259 then
                if k < 256 then
                  if k < 255 then
                    3476
                  else
                    3503
                else
                  if k < 257 then
                    3525
                  else
                    if k < 258 then
                      3553
                    else
                      3578
              else
                if k < 261 then
                  if k < 260 then
                    3607
                  else
                    3633
                else
                  if k < 262 then
                    3653
                  else
                    if k < 263 then
                      3679
                    else
                      3707
          else
            if k < 274 then
              if k < 269 then
                if k < 266 then
                  if k < 265 then
                    3732
                  else
                    3754
                else
                  if k < 267 then
                    3780
                  else
                    if k < 268 then
                      3801
                    else
                      3829
              else
                if k < 271 then
                  if k < 270 then
                    3854
                  else
                    3879
                else
                  if k < 272 then
                    3908
                  else
                    if k < 273 then
                      3935
                    else
                      3960
            else
              if k < 279 then
                if k < 276 then
                  if k < 275 then
                    3990
                  else
                    4010
                else
                  if k < 277 then
                    4034
                  else
                    if k < 278 then
                      4059
                    else
                      4086
              else
                if k < 282 then
                  if k < 280 then
                    4112
                  else
                    if k < 281 then
                      4141
                    else
                      4166
                else
                  if k < 283 then
                    4196
                  else
                    if k < 284 then
                      4221
                    else
                      4242
        else
          if k < 305 then
            if k < 295 then
              if k < 290 then
                if k < 287 then
                  if k < 286 then
                    4266
                  else
                    4295
                else
                  if k < 288 then
                    4324
                  else
                    if k < 289 then
                      4353
                    else
                      4381
              else
                if k < 292 then
                  if k < 291 then
                    4411
                  else
                    4445
                else
                  if k < 293 then
                    4473
                  else
                    if k < 294 then
                      4502
                    else
                      4522
            else
              if k < 300 then
                if k < 297 then
                  if k < 296 then
                    4550
                  else
                    4572
                else
                  if k < 298 then
                    4604
                  else
                    if k < 299 then
                      4632
                    else
                      4661
              else
                if k < 302 then
                  if k < 301 then
                    4687
                  else
                    4714
                else
                  if k < 303 then
                    4739
                  else
                    if k < 304 then
                      4765
                    else
                      4794
          else
            if k < 315 then
              if k < 310 then
                if k < 307 then
                  if k < 306 then
                    4822
                  else
                    4849
                else
                  if k < 308 then
                    4874
                  else
                    if k < 309 then
                      4905
                    else
                      4935
              else
                if k < 312 then
                  if k < 311 then
                    4963
                  else
                    4990
                else
                  if k < 313 then
                    5022
                  else
                    if k < 314 then
                      5051
                    else
                      5081
            else
              if k < 320 then
                if k < 317 then
                  if k < 316 then
                    5110
                  else
                    5142
                else
                  if k < 318 then
                    5172
                  else
                    if k < 319 then
                      5197
                    else
                      5224
              else
                if k < 323 then
                  if k < 321 then
                    5255
                  else
                    if k < 322 then
                      5289
                    else
                      5319
                else
                  if k < 324 then
                    5349
                  else
                    if k < 325 then
                      5375
                    else
                      5406

/-- Kernel-checkable: the table increases by the prime count between triangular numbers. -/
def a262446Steps (a : ℕ) : ℕ → Bool
  | 0 => true
  | l + 1 => a262446Steps a l && Nat.beq (a262446Tbl (a + l + 1))
      (a262446Tbl (a + l) + a262446Cnt ((a + l) * (a + l + 1) / 2 + 2) (a + l + 1))

theorem a262446Steps_sound (a l : ℕ) (h : a262446Steps a l = true) : ∀ k, a ≤ k → k < a + l →
    a262446Tbl (k + 1) = a262446Tbl k + a262446Cnt (k * (k + 1) / 2 + 2) (k + 1) := by
  induction l with
  | zero => intro k h1 h2; omega
  | succ l ih =>
    simp only [a262446Steps, Bool.and_eq_true, Nat.beq_eq] at h
    intro k h1 h2
    rcases Nat.lt_or_ge k (a + l) with hk | hk
    · exact ih h.1 k h1 hk
    · have hk' : k = a + l := by omega
      subst hk'
      exact h.2

theorem a262446_chunk0 : a262446Steps 0 25 = true := by decide +kernel

theorem a262446_chunk1 : a262446Steps 25 25 = true := by decide +kernel

theorem a262446_chunk2 : a262446Steps 50 25 = true := by decide +kernel

theorem a262446_chunk3 : a262446Steps 75 25 = true := by decide +kernel

theorem a262446_chunk4 : a262446Steps 100 25 = true := by decide +kernel

theorem a262446_chunk5 : a262446Steps 125 25 = true := by decide +kernel

theorem a262446_chunk6 : a262446Steps 150 25 = true := by decide +kernel

theorem a262446_chunk7 : a262446Steps 175 25 = true := by decide +kernel

theorem a262446_chunk8 : a262446Steps 200 25 = true := by decide +kernel

theorem a262446_chunk9 : a262446Steps 225 25 = true := by decide +kernel

theorem a262446_chunk10 : a262446Steps 250 25 = true := by decide +kernel

theorem a262446_chunk11 : a262446Steps 275 25 = true := by decide +kernel

theorem a262446_chunk12 : a262446Steps 300 25 = true := by decide +kernel

theorem a262446_step (k : ℕ) (hk : k < 325) :
    a262446Tbl (k + 1) = a262446Tbl k + a262446Cnt (k * (k + 1) / 2 + 2) (k + 1) := by
  by_cases h0 : k < 25
  · exact a262446Steps_sound 0 25 a262446_chunk0 k (by omega) (by omega)
  by_cases h1 : k < 50
  · exact a262446Steps_sound 25 25 a262446_chunk1 k (by omega) (by omega)
  by_cases h2 : k < 75
  · exact a262446Steps_sound 50 25 a262446_chunk2 k (by omega) (by omega)
  by_cases h3 : k < 100
  · exact a262446Steps_sound 75 25 a262446_chunk3 k (by omega) (by omega)
  by_cases h4 : k < 125
  · exact a262446Steps_sound 100 25 a262446_chunk4 k (by omega) (by omega)
  by_cases h5 : k < 150
  · exact a262446Steps_sound 125 25 a262446_chunk5 k (by omega) (by omega)
  by_cases h6 : k < 175
  · exact a262446Steps_sound 150 25 a262446_chunk6 k (by omega) (by omega)
  by_cases h7 : k < 200
  · exact a262446Steps_sound 175 25 a262446_chunk7 k (by omega) (by omega)
  by_cases h8 : k < 225
  · exact a262446Steps_sound 200 25 a262446_chunk8 k (by omega) (by omega)
  by_cases h9 : k < 250
  · exact a262446Steps_sound 225 25 a262446_chunk9 k (by omega) (by omega)
  by_cases h10 : k < 275
  · exact a262446Steps_sound 250 25 a262446_chunk10 k (by omega) (by omega)
  by_cases h11 : k < 300
  · exact a262446Steps_sound 275 25 a262446_chunk11 k (by omega) (by omega)
  by_cases h12 : k < 325
  · exact a262446Steps_sound 300 25 a262446_chunk12 k (by omega) (by omega)
  omega

theorem a262446_tri (k : ℕ) :
    (k + 1) * (k + 1 + 1) / 2 + 2 = (k * (k + 1) / 2 + 2) + (k + 1) := by
  have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + (k + 1) * 2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num)]
  omega

theorem a262446_b_eq : ∀ k, k ≤ 325 → OeisA262446.b k = a262446Tbl k := by
  intro k
  induction k with
  | zero => intro _; decide +kernel
  | succ k ih =>
    intro hk
    have hb : ∀ j, OeisA262446.b j = Nat.count Nat.Prime (j * (j + 1) / 2 + 2) := fun j => rfl
    have hle : k * (k + 1) / 2 ≤ 325 * 326 / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    rw [hb, a262446_tri, a262446_count_add _ _ (by omega), ← hb, ih (by omega),
      a262446_step k (by omega)]

theorem a262446_a_eq (n : ℕ) (hn : n ≤ 325) : OeisA262446.a n =
    ∑ k ∈ Finset.Ico 1 n,
      ((Finset.Ico (k + 1) n).filter
        (fun m => a262446Tbl n = a262446Tbl k + a262446Tbl m)).card := by
  show (∑ k ∈ Finset.Ico 1 n, ((Finset.Ico (k + 1) n).filter
      (fun m => OeisA262446.b n = OeisA262446.b k + OeisA262446.b m)).card) = _
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  congr 1
  apply Finset.filter_congr
  intro m hm
  rw [Finset.mem_Ico] at hm
  rw [a262446_b_eq n hn, a262446_b_eq k (by omega), a262446_b_eq m (by omega)]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_OeisA262446_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [a262446_a_eq _ (by norm_num)]
    decide +kernel
