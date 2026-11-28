import OMAStatements.S_oeis_a289004
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a289004

/-- One step of the left-to-right reading: emitted letters and the pending letter. -/
def step : Option Bool → Bool → List Bool × Option Bool
  | none, c => ([], some c)
  | some false, false => ([false, false, true, false], none)
  | some false, true => ([false, false, true], none)
  | some true, false => ([false, true, false], none)
  | some true, true => ([true], some true)

/-- The pending letter is copied at the end. -/
def flush : Option Bool → List Bool
  | none => []
  | some b => [b]

/-- Emitted letters (without the final copy) and the final pending letter. -/
def run : Option Bool → List Bool → List Bool × Option Bool
  | p, [] => ([], p)
  | p, c :: w => ((step p c).1 ++ (run (step p c).2 w).1, (run (step p c).2 w).2)

def go (p : Option Bool) (w : List Bool) : List Bool := (run p w).1 ++ flush (run p w).2

theorem run_append (p : Option Bool) (u v : List Bool) :
    run p (u ++ v) = ((run p u).1 ++ (run (run p u).2 v).1, (run (run p u).2 v).2) := by
  induction u generalizing p with
  | nil => simp [run]
  | cons c u ih => simp [run, ih]

theorem go_append (p : Option Bool) (u v : List Bool) :
    go p (u ++ v) = (run p u).1 ++ go (run p u).2 v := by
  simp [go, run_append]

theorem go_cons (p : Option Bool) (c : Bool) (w : List Bool) :
    go p (c :: w) = (step p c).1 ++ go (step p c).2 w := by
  simp [go, run]

theorem rewrite_eq (w : List Bool) : rewrite w = go none w := by
  induction w using rewrite.induct with
  | case1 => rfl
  | case2 b => cases b <;> rfl
  | case3 w ih => rw [rewrite, ih, go_cons, go_cons]; rfl
  | case4 w ih => rw [rewrite, ih, go_cons, go_cons]; rfl
  | case5 w ih => rw [rewrite, ih, go_cons, go_cons]; rfl
  | case6 w ih => rw [rewrite, ih, go_cons, go_cons, go_cons]; rfl

/-- Applying the stages of a cascade in order. -/
def sem : List (Option Bool) → List Bool → List Bool
  | [], w => w
  | p :: S, w => sem S (go p w)

/-- Feeding a chunk through a cascade: new stage states and the number of letters emitted
by the last stage (without final copies). -/
def casc : List (Option Bool) → List Bool → List (Option Bool) × ℕ
  | [], w => ([], w.length)
  | p :: S, w => ((run p w).2 :: (casc S (run p w).1).1, (casc S (run p w).1).2)

theorem casc_spec (S : List (Option Bool)) (u v : List Bool) :
    (sem S (u ++ v)).length = (casc S u).2 + (sem (casc S u).1 v).length := by
  induction S generalizing u v with
  | nil => simp [sem, casc]
  | cons p S ih =>
    simp only [sem, casc]
    rw [go_append, ih]

theorem word_add (n j : ℕ) : word (n + j) = sem (List.replicate j none) (word n) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, sem, ← rewrite_eq, show n + (j + 1) = (n + 1) + j by omega, ih]
    rfl

theorem chunk_step (S S' : List (Option Bool)) (w : List Bool) (a m b c : ℕ) (hab : a + m = b)
    (h : casc S ((w.drop a).take m) = (S', c)) :
    (sem S (w.drop a)).length = c + (sem S' (w.drop b)).length := by
  have e := casc_spec S ((w.drop a).take m) ((w.drop a).drop m)
  rw [List.take_append_drop, h, List.drop_drop] at e
  rw [e, ← hab]

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a289004

theorem len_top : (word 12).length = 1277 := by decide +kernel

theorem chunk0 : casc (List.replicate 10 none) (((word 12).drop 0).take 16) =
    ([none, none, none, none, none, some false, none, some true, none, none], 3445) := by
  decide +kernel

theorem chunk1 : casc [none, none, none, none, none, some false, none, some true, none, none] (((word 12).drop 16).take 16) =
    ([none, some false, none, some true, some false, none, some true, none, some false, some true], 3128) := by
  decide +kernel

theorem chunk2 : casc [none, some false, none, some true, some false, none, some true, none, some false, some true] (((word 12).drop 32).take 16) =
    ([none, none, none, some false, none, some true, none, none, some false, some true], 3462) := by
  decide +kernel

theorem chunk3 : casc [none, none, none, some false, none, some true, none, none, some false, some true] (((word 12).drop 48).take 16) =
    ([none, some true, some false, none, none, some true, some false, some true, some false, some true], 3206) := by
  decide +kernel

theorem chunk4 : casc [none, some true, some false, none, none, some true, some false, some true, some false, some true] (((word 12).drop 64).take 16) =
    ([none, some false, none, none, none, none, none, some true, none, some false], 3485) := by
  decide +kernel

theorem chunk5 : casc [none, some false, none, none, none, none, none, some true, none, some false] (((word 12).drop 80).take 16) =
    ([none, none, none, none, none, some false, none, none, none, none], 3452) := by
  decide +kernel

theorem chunk6 : casc [none, none, none, none, none, some false, none, none, none, none] (((word 12).drop 96).take 16) =
    ([none, some true, some false, some true, some false, none, some true, some false, none, none], 3124) := by
  decide +kernel

theorem chunk7 : casc [none, some true, some false, some true, some false, none, some true, some false, none, none] (((word 12).drop 112).take 16) =
    ([none, some false, none, some true, some false, some true, none, some false, none, none], 3462) := by
  decide +kernel

theorem chunk8 : casc [none, some false, none, some true, some false, some true, none, some false, none, none] (((word 12).drop 128).take 16) =
    ([none, none, none, some false, none, none, some true, none, none, some false], 3472) := by
  decide +kernel

theorem chunk9 : casc [none, none, none, some false, none, none, some true, none, none, some false] (((word 12).drop 144).take 16) =
    ([none, some true, some false, none, none, none, none, none, none, some true], 3224) := by
  decide +kernel

theorem chunk10 : casc [none, some true, some false, none, none, none, none, none, none, some true] (((word 12).drop 160).take 16) =
    ([none, some false, none, none, none, some true, some false, some true, none, some false], 3444) := by
  decide +kernel

theorem chunk11 : casc [none, some false, none, none, none, some true, some false, some true, none, some false] (((word 12).drop 176).take 16) =
    ([none, none, none, none, none, none, none, some false, none, some true], 3480) := by
  decide +kernel

theorem chunk12 : casc [none, none, none, none, none, none, none, some false, none, some true] (((word 12).drop 192).take 16) =
    ([none, some true, some false, some true, some false, some true, none, none, some false, none], 3113) := by
  decide +kernel

theorem chunk13 : casc [none, some true, some false, some true, some false, some true, none, none, some false, none] (((word 12).drop 208).take 16) =
    ([none, some false, none, some true, some false, none, some true, some false, some true, some false], 3462) := by
  decide +kernel

theorem chunk14 : casc [none, some false, none, some true, some false, none, some true, some false, some true, some false] (((word 12).drop 224).take 16) =
    ([none, none, none, some false, none, some true, none, some false, some true, some false], 3462) := by
  decide +kernel

theorem chunk15 : casc [none, none, none, some false, none, some true, none, some false, some true, some false] (((word 12).drop 240).take 16) =
    ([none, some true, some false, none, none, some true, some false, none, none, some true], 3217) := by
  decide +kernel

theorem chunk16 : casc [none, some true, some false, none, none, some true, some false, none, none, some true] (((word 12).drop 256).take 16) =
    ([none, some false, none, none, none, none, none, none, some true, none], 3482) := by
  decide +kernel

theorem chunk17 : casc [none, some false, none, none, none, none, none, none, some true, none] (((word 12).drop 272).take 16) =
    ([none, none, none, none, none, some false, none, some true, some false, some true], 3442) := by
  decide +kernel

theorem chunk18 : casc [none, none, none, none, none, some false, none, some true, some false, some true] (((word 12).drop 288).take 16) =
    ([none, some false, none, some true, some false, none, some true, none, none, none], 3137) := by
  decide +kernel

theorem chunk19 : casc [none, some false, none, some true, some false, none, some true, none, none, none] (((word 12).drop 304).take 16) =
    ([none, none, none, some true, some false, some true, none, none, none, none], 3462) := by
  decide +kernel

theorem chunk20 : casc [none, none, none, some true, some false, some true, none, none, none, none] (((word 12).drop 320).take 16) =
    ([none, none, none, some false, none, none, some true, some false, none, none], 3462) := by
  decide +kernel

theorem chunk21 : casc [none, none, none, some false, none, none, some true, some false, none, none] (((word 12).drop 336).take 16) =
    ([none, some false, none, none, none, none, none, some true, some false, none], 3223) := by
  decide +kernel

theorem chunk22 : casc [none, some false, none, none, none, none, none, some true, some false, none] (((word 12).drop 352).take 16) =
    ([none, none, none, none, none, some true, some false, none, some true, none], 3452) := by
  decide +kernel

theorem chunk23 : casc [none, none, none, none, none, some true, some false, none, some true, none] (((word 12).drop 368).take 16) =
    ([none, none, none, none, none, none, none, none, none, some false], 3482) := by
  decide +kernel

theorem chunk24 : casc [none, none, none, none, none, none, none, none, none, some false] (((word 12).drop 384).take 16) =
    ([none, some false, none, some true, some false, some true, none, some false, some true, none], 3104) := by
  decide +kernel

theorem chunk25 : casc [none, some false, none, some true, some false, some true, none, some false, some true, none] (((word 12).drop 400).take 16) =
    ([none, none, none, some true, some false, none, some true, none, some false, none], 3472) := by
  decide +kernel

theorem chunk26 : casc [none, none, none, some true, some false, none, some true, none, some false, none] (((word 12).drop 416).take 16) =
    ([none, none, none, some false, none, some true, none, none, some false, none], 3462) := by
  decide +kernel

theorem chunk27 : casc [none, none, none, some false, none, some true, none, none, some false, none] (((word 12).drop 432).take 16) =
    ([none, some false, none, none, none, some true, some false, some true, some false, none], 3206) := by
  decide +kernel

theorem chunk28 : casc [none, some false, none, none, none, some true, some false, some true, some false, none] (((word 12).drop 448).take 16) =
    ([none, none, none, none, none, none, none, some true, none, none], 3486) := by
  decide +kernel

theorem chunk29 : casc [none, none, none, none, none, none, none, some true, none, none] (((word 12).drop 464).take 16) =
    ([none, none, none, none, none, some false, none, none, none, some true], 3449) := by
  decide +kernel

theorem chunk30 : casc [none, none, none, none, none, some false, none, none, none, some true] (((word 12).drop 480).take 16) =
    ([none, some false, none, some true, some false, none, some true, some false, none, some true], 3124) := by
  decide +kernel

theorem chunk31 : casc [none, some false, none, some true, some false, none, some true, some false, none, some true] (((word 12).drop 496).take 16) =
    ([none, none, none, some true, some false, some true, none, some false, none, some true], 3462) := by
  decide +kernel

theorem chunk32 : casc [none, none, none, some true, some false, some true, none, some false, none, some true] (((word 12).drop 512).take 16) =
    ([none, none, none, some false, none, none, some true, none, none, none], 3475) := by
  decide +kernel

theorem chunk33 : casc [none, none, none, some false, none, none, some true, none, none, none] (((word 12).drop 528).take 16) =
    ([none, some false, none, none, none, none, none, none, none, none], 3223) := by
  decide +kernel

theorem chunk34 : casc [none, some false, none, none, none, none, none, none, none, none] (((word 12).drop 544).take 16) =
    ([none, none, none, none, none, some false, none, some true, none, none], 3445) := by
  decide +kernel

theorem chunk35 : casc [none, none, none, none, none, some false, none, some true, none, none] (((word 12).drop 560).take 16) =
    ([none, none, none, none, none, none, none, some false, none, none], 3479) := by
  decide +kernel

theorem chunk36 : casc [none, none, none, none, none, none, none, some false, none, none] (((word 12).drop 576).take 16) =
    ([none, some false, none, some true, some false, some true, none, none, some false, some true], 3111) := by
  decide +kernel

theorem chunk37 : casc [none, some false, none, some true, some false, some true, none, none, some false, some true] (((word 12).drop 592).take 16) =
    ([none, none, none, some false, none, none, some true, some false, some true, none], 3465) := by
  decide +kernel

theorem chunk38 : casc [none, none, none, some false, none, none, some true, some false, some true, none] (((word 12).drop 608).take 16) =
    ([none, some true, some false, none, none, none, none, some true, none, some false], 3226) := by
  decide +kernel

theorem chunk39 : casc [none, some true, some false, none, none, none, none, some true, none, some false] (((word 12).drop 624).take 16) =
    ([none, some false, none, none, none, some true, some false, none, none, none], 3452) := by
  decide +kernel

theorem chunk40 : casc [none, some false, none, none, none, some true, some false, none, none, none] (((word 12).drop 640).take 16) =
    ([none, none, none, none, none, none, none, none, some false, none], 3479) := by
  decide +kernel

theorem chunk41 : casc [none, none, none, none, none, none, none, none, some false, none] (((word 12).drop 656).take 16) =
    ([none, some true, some false, some true, some false, some true, none, some false, none, none], 3107) := by
  decide +kernel

theorem chunk42 : casc [none, some true, some false, some true, some false, some true, none, some false, none, none] (((word 12).drop 672).take 16) =
    ([none, some false, none, some true, some false, none, some true, none, none, some false], 3472) := by
  decide +kernel

theorem chunk43 : casc [none, some false, none, some true, some false, none, some true, none, none, some false] (((word 12).drop 688).take 16) =
    ([none, none, none, some false, none, some true, none, none, none, some false], 3462) := by
  decide +kernel

theorem chunk44 : casc [none, none, none, some false, none, some true, none, none, none, some false] (((word 12).drop 704).take 16) =
    ([none, some true, some false, none, none, some true, some false, some true, none, some false], 3206) := by
  decide +kernel

theorem chunk45 : casc [none, some true, some false, none, none, some true, some false, some true, none, some false] (((word 12).drop 720).take 16) =
    ([none, some false, none, none, none, none, none, some true, some false, some true], 3480) := by
  decide +kernel

theorem chunk46 : casc [none, some false, none, none, none, none, none, some true, some false, some true] (((word 12).drop 736).take 16) =
    ([none, none, none, none, none, some false, none, none, some true, some false], 3451) := by
  decide +kernel

theorem chunk47 : casc [none, none, none, none, none, some false, none, none, some true, some false] (((word 12).drop 752).take 16) =
    ([none, some true, some false, some true, some false, none, some true, some false, some true, some false], 3124) := by
  decide +kernel

theorem chunk48 : casc [none, some true, some false, some true, some false, none, some true, some false, some true, some false] (((word 12).drop 768).take 16) =
    ([none, some false, none, some true, some false, some true, none, some false, some true, some false], 3462) := by
  decide +kernel

theorem chunk49 : casc [none, some false, none, some true, some false, some true, none, some false, some true, some false] (((word 12).drop 784).take 16) =
    ([none, none, none, some false, none, none, some true, none, some false, some true], 3473) := by
  decide +kernel

theorem chunk50 : casc [none, none, none, some false, none, none, some true, none, some false, some true] (((word 12).drop 800).take 16) =
    ([none, some false, none, none, none, none, none, none, some true, none], 3226) := by
  decide +kernel

theorem chunk51 : casc [none, some false, none, none, none, none, none, none, some true, none] (((word 12).drop 816).take 16) =
    ([none, some false, none, none, none, some true, some false, some true, some false, some true], 3442) := by
  decide +kernel

theorem chunk52 : casc [none, some false, none, none, none, some true, some false, some true, some false, some true] (((word 12).drop 832).take 16) =
    ([none, none, none, none, none, none, none, some false, some true, none], 3482) := by
  decide +kernel

theorem chunk53 : casc [none, none, none, none, none, none, none, some false, some true, none] (((word 12).drop 848).take 16) =
    ([none, some false, none, some true, some false, some true, none, none, none, none], 3117) := by
  decide +kernel

theorem chunk54 : casc [none, some false, none, some true, some false, some true, none, none, none, none] (((word 12).drop 864).take 16) =
    ([none, none, none, some true, some false, none, some true, some false, none, none], 3462) := by
  decide +kernel

theorem chunk55 : casc [none, none, none, some true, some false, none, some true, some false, none, none] (((word 12).drop 880).take 16) =
    ([none, none, none, some false, none, some true, none, some false, none, none], 3462) := by
  decide +kernel

theorem chunk56 : casc [none, none, none, some false, none, some true, none, some false, none, none] (((word 12).drop 896).take 16) =
    ([none, some false, none, none, none, some true, some false, none, some true, none], 3213) := by
  decide +kernel

theorem chunk57 : casc [none, some false, none, none, none, some true, some false, none, some true, none] (((word 12).drop 912).take 16) =
    ([none, none, none, none, none, none, none, none, none, some true], 3483) := by
  decide +kernel

theorem chunk58 : casc [none, none, none, none, none, none, none, none, none, some true] (((word 12).drop 928).take 16) =
    ([none, none, none, none, none, some false, none, some true, none, some false], 3444) := by
  decide +kernel

theorem chunk59 : casc [none, none, none, none, none, some false, none, some true, none, some false] (((word 12).drop 944).take 16) =
    ([none, some false, none, some true, some false, none, some true, none, some false, none], 3131) := by
  decide +kernel

theorem chunk60 : casc [none, some false, none, some true, some false, none, some true, none, some false, none] (((word 12).drop 960).take 16) =
    ([none, none, none, some true, some false, some true, none, none, some false, none], 3462) := by
  decide +kernel

theorem chunk61 : casc [none, none, none, some true, some false, some true, none, none, some false, none] (((word 12).drop 976).take 16) =
    ([none, none, none, some false, none, none, some true, some false, some true, some false], 3462) := by
  decide +kernel

theorem chunk62 : casc [none, none, none, some false, none, none, some true, some false, some true, some false] (((word 12).drop 992).take 16) =
    ([none, some false, none, none, none, none, none, some true, none, none], 3230) := by
  decide +kernel

theorem chunk63 : casc [none, some false, none, none, none, none, none, some true, none, none] (((word 12).drop 1008).take 16) =
    ([none, none, none, none, none, some true, some false, none, none, some true], 3449) := by
  decide +kernel

theorem chunk64 : casc [none, none, none, none, none, some true, some false, none, none, some true] (((word 12).drop 1024).take 16) =
    ([none, none, none, none, none, none, none, none, some false, some true], 3479) := by
  decide +kernel

theorem chunk65 : casc [none, none, none, none, none, none, none, none, some false, some true] (((word 12).drop 1040).take 16) =
    ([none, some false, none, some true, some false, some true, none, some false, none, some true], 3107) := by
  decide +kernel

theorem chunk66 : casc [none, some false, none, some true, some false, some true, none, some false, none, some true] (((word 12).drop 1056).take 16) =
    ([none, none, none, some true, some false, none, some true, none, none, none], 3475) := by
  decide +kernel

theorem chunk67 : casc [none, none, none, some true, some false, none, some true, none, none, none] (((word 12).drop 1072).take 16) =
    ([none, none, none, some false, none, some true, none, none, none, none], 3462) := by
  decide +kernel

theorem chunk68 : casc [none, none, none, some false, none, some true, none, none, none, none] (((word 12).drop 1088).take 16) =
    ([none, some false, none, none, none, some true, some false, some true, none, none], 3206) := by
  decide +kernel

theorem chunk69 : casc [none, some false, none, none, none, some true, some false, some true, none, none] (((word 12).drop 1104).take 16) =
    ([none, none, none, none, none, none, none, some false, none, none], 3479) := by
  decide +kernel

theorem chunk70 : casc [none, none, none, none, none, none, none, some false, none, none] (((word 12).drop 1120).take 16) =
    ([none, some true, some false, some true, some false, some true, none, none, some false, some true], 3111) := by
  decide +kernel

theorem chunk71 : casc [none, some true, some false, some true, some false, some true, none, none, some false, some true] (((word 12).drop 1136).take 16) =
    ([none, some false, none, some true, some false, none, some true, some false, some true, none], 3465) := by
  decide +kernel

theorem chunk72 : casc [none, some false, none, some true, some false, none, some true, some false, some true, none] (((word 12).drop 1152).take 16) =
    ([none, none, none, some false, none, some true, none, some false, some true, none], 3462) := by
  decide +kernel

theorem chunk73 : casc [none, none, none, some false, none, some true, none, some false, some true, none] (((word 12).drop 1168).take 16) =
    ([none, some true, some false, none, none, some true, some false, none, none, none], 3216) := by
  decide +kernel

theorem chunk74 : casc [none, some true, some false, none, none, some true, some false, none, none, none] (((word 12).drop 1184).take 16) =
    ([none, some false, none, none, none, none, none, none, some true, some false], 3479) := by
  decide +kernel

theorem chunk75 : casc [none, some false, none, none, none, none, none, none, some true, some false] (((word 12).drop 1200).take 16) =
    ([none, none, none, none, none, some false, none, some true, some false, none], 3445) := by
  decide +kernel

theorem chunk76 : casc [none, none, none, none, none, some false, none, some true, some false, none] (((word 12).drop 1216).take 16) =
    ([none, some true, some false, some true, some false, none, some true, none, none, some false], 3134) := by
  decide +kernel

theorem chunk77 : casc [none, some true, some false, some true, some false, none, some true, none, none, some false] (((word 12).drop 1232).take 16) =
    ([none, some false, none, some true, some false, some true, none, none, none, some false], 3462) := by
  decide +kernel

theorem chunk78 : casc [none, some false, none, some true, some false, some true, none, none, none, some false] (((word 12).drop 1248).take 16) =
    ([none, none, none, some false, none, none, some true, some false, none, some true], 3463) := by
  decide +kernel

theorem chunk79 : casc [none, none, none, some false, none, none, some true, some false, none, some true] (((word 12).drop 1264).take 16) =
    ([some false, none, none, some true, none, some false, some true, none, some false, some true], 2465) := by
  decide +kernel

theorem chunk_fin : (sem [some false, none, none, some true, none, some false, some true, none, some false, some true] []).length = 72 := by decide +kernel

theorem len22 : (word 22).length = 268184 := by
  have e : word 22 = sem (List.replicate 10 none) (word 12) := word_add 12 10
  have e0 : (word 12).drop 0 = word 12 := List.drop_zero
  have h0 := chunk_step _ _ _ 0 16 16 3445 rfl chunk0
  have h1 := chunk_step _ _ _ 16 16 32 3128 rfl chunk1
  have h2 := chunk_step _ _ _ 32 16 48 3462 rfl chunk2
  have h3 := chunk_step _ _ _ 48 16 64 3206 rfl chunk3
  have h4 := chunk_step _ _ _ 64 16 80 3485 rfl chunk4
  have h5 := chunk_step _ _ _ 80 16 96 3452 rfl chunk5
  have h6 := chunk_step _ _ _ 96 16 112 3124 rfl chunk6
  have h7 := chunk_step _ _ _ 112 16 128 3462 rfl chunk7
  have h8 := chunk_step _ _ _ 128 16 144 3472 rfl chunk8
  have h9 := chunk_step _ _ _ 144 16 160 3224 rfl chunk9
  have h10 := chunk_step _ _ _ 160 16 176 3444 rfl chunk10
  have h11 := chunk_step _ _ _ 176 16 192 3480 rfl chunk11
  have h12 := chunk_step _ _ _ 192 16 208 3113 rfl chunk12
  have h13 := chunk_step _ _ _ 208 16 224 3462 rfl chunk13
  have h14 := chunk_step _ _ _ 224 16 240 3462 rfl chunk14
  have h15 := chunk_step _ _ _ 240 16 256 3217 rfl chunk15
  have h16 := chunk_step _ _ _ 256 16 272 3482 rfl chunk16
  have h17 := chunk_step _ _ _ 272 16 288 3442 rfl chunk17
  have h18 := chunk_step _ _ _ 288 16 304 3137 rfl chunk18
  have h19 := chunk_step _ _ _ 304 16 320 3462 rfl chunk19
  have h20 := chunk_step _ _ _ 320 16 336 3462 rfl chunk20
  have h21 := chunk_step _ _ _ 336 16 352 3223 rfl chunk21
  have h22 := chunk_step _ _ _ 352 16 368 3452 rfl chunk22
  have h23 := chunk_step _ _ _ 368 16 384 3482 rfl chunk23
  have h24 := chunk_step _ _ _ 384 16 400 3104 rfl chunk24
  have h25 := chunk_step _ _ _ 400 16 416 3472 rfl chunk25
  have h26 := chunk_step _ _ _ 416 16 432 3462 rfl chunk26
  have h27 := chunk_step _ _ _ 432 16 448 3206 rfl chunk27
  have h28 := chunk_step _ _ _ 448 16 464 3486 rfl chunk28
  have h29 := chunk_step _ _ _ 464 16 480 3449 rfl chunk29
  have h30 := chunk_step _ _ _ 480 16 496 3124 rfl chunk30
  have h31 := chunk_step _ _ _ 496 16 512 3462 rfl chunk31
  have h32 := chunk_step _ _ _ 512 16 528 3475 rfl chunk32
  have h33 := chunk_step _ _ _ 528 16 544 3223 rfl chunk33
  have h34 := chunk_step _ _ _ 544 16 560 3445 rfl chunk34
  have h35 := chunk_step _ _ _ 560 16 576 3479 rfl chunk35
  have h36 := chunk_step _ _ _ 576 16 592 3111 rfl chunk36
  have h37 := chunk_step _ _ _ 592 16 608 3465 rfl chunk37
  have h38 := chunk_step _ _ _ 608 16 624 3226 rfl chunk38
  have h39 := chunk_step _ _ _ 624 16 640 3452 rfl chunk39
  have h40 := chunk_step _ _ _ 640 16 656 3479 rfl chunk40
  have h41 := chunk_step _ _ _ 656 16 672 3107 rfl chunk41
  have h42 := chunk_step _ _ _ 672 16 688 3472 rfl chunk42
  have h43 := chunk_step _ _ _ 688 16 704 3462 rfl chunk43
  have h44 := chunk_step _ _ _ 704 16 720 3206 rfl chunk44
  have h45 := chunk_step _ _ _ 720 16 736 3480 rfl chunk45
  have h46 := chunk_step _ _ _ 736 16 752 3451 rfl chunk46
  have h47 := chunk_step _ _ _ 752 16 768 3124 rfl chunk47
  have h48 := chunk_step _ _ _ 768 16 784 3462 rfl chunk48
  have h49 := chunk_step _ _ _ 784 16 800 3473 rfl chunk49
  have h50 := chunk_step _ _ _ 800 16 816 3226 rfl chunk50
  have h51 := chunk_step _ _ _ 816 16 832 3442 rfl chunk51
  have h52 := chunk_step _ _ _ 832 16 848 3482 rfl chunk52
  have h53 := chunk_step _ _ _ 848 16 864 3117 rfl chunk53
  have h54 := chunk_step _ _ _ 864 16 880 3462 rfl chunk54
  have h55 := chunk_step _ _ _ 880 16 896 3462 rfl chunk55
  have h56 := chunk_step _ _ _ 896 16 912 3213 rfl chunk56
  have h57 := chunk_step _ _ _ 912 16 928 3483 rfl chunk57
  have h58 := chunk_step _ _ _ 928 16 944 3444 rfl chunk58
  have h59 := chunk_step _ _ _ 944 16 960 3131 rfl chunk59
  have h60 := chunk_step _ _ _ 960 16 976 3462 rfl chunk60
  have h61 := chunk_step _ _ _ 976 16 992 3462 rfl chunk61
  have h62 := chunk_step _ _ _ 992 16 1008 3230 rfl chunk62
  have h63 := chunk_step _ _ _ 1008 16 1024 3449 rfl chunk63
  have h64 := chunk_step _ _ _ 1024 16 1040 3479 rfl chunk64
  have h65 := chunk_step _ _ _ 1040 16 1056 3107 rfl chunk65
  have h66 := chunk_step _ _ _ 1056 16 1072 3475 rfl chunk66
  have h67 := chunk_step _ _ _ 1072 16 1088 3462 rfl chunk67
  have h68 := chunk_step _ _ _ 1088 16 1104 3206 rfl chunk68
  have h69 := chunk_step _ _ _ 1104 16 1120 3479 rfl chunk69
  have h70 := chunk_step _ _ _ 1120 16 1136 3111 rfl chunk70
  have h71 := chunk_step _ _ _ 1136 16 1152 3465 rfl chunk71
  have h72 := chunk_step _ _ _ 1152 16 1168 3462 rfl chunk72
  have h73 := chunk_step _ _ _ 1168 16 1184 3216 rfl chunk73
  have h74 := chunk_step _ _ _ 1184 16 1200 3479 rfl chunk74
  have h75 := chunk_step _ _ _ 1200 16 1216 3445 rfl chunk75
  have h76 := chunk_step _ _ _ 1216 16 1232 3134 rfl chunk76
  have h77 := chunk_step _ _ _ 1232 16 1248 3462 rfl chunk77
  have h78 := chunk_step _ _ _ 1248 16 1264 3463 rfl chunk78
  have h79 := chunk_step _ _ _ 1264 16 1280 2465 rfl chunk79
  have hf : (sem [some false, none, none, some true, none, some false, some true, none, some false, some true] ((word 12).drop 1280)).length = 72 := by
    rw [List.drop_eq_nil_of_le (by rw [len_top]; norm_num)]
    exact chunk_fin
  rw [e0] at h0
  rw [e]
  omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a289004.main) := by
  intro h
  have h22 := h 22
  have r : OMA.S_oeis_a289004.reference 22 = 268182 := by decide +kernel
  rw [len22, r] at h22
  norm_num at h22

