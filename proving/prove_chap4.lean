open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
fun h1 : ∃ _ : α, r => Exists.elim h1
  (fun _ : α => fun hr : r => hr)

example : (∃ _ : α, r) → r :=
fun h1 : ∃ _ : α, r => Exists.elim h1
  (fun _ : α => fun hr : r => hr)

example (a : α) : r → (∃ _ : α, r) :=
fun hr : r => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
(fun h1: ∃ x, p x ∧ r => And.intro
  (Exists.elim h1 (fun x : α =>
    fun h2 : p x ∧ r => Exists.intro x h2.left))
  (Exists.elim h1 (fun x : α =>
    fun h2 : p x ∧ r => h2.right)))
(fun h1: (∃ x, p x) ∧ r => Exists.elim h1.left
  (fun x : α =>
    fun hp : p x =>
      have h2 : p x ∧ r := And.intro hp h1.right
      Exists.intro x h2))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
(fun h1 : ∃ x, p x ∨ q x => Exists.elim h1
  fun y : α =>
    fun h2 : p y ∨ q y => Or.elim h2
      (fun hp : p y =>
        have h3 : ∃ x, p x := Exists.intro y hp
        Or.intro_left (∃ x, q x) h3)
      (fun hq : q y =>
        have h3 : ∃ x, q x := Exists.intro y hq
        Or.intro_right (∃ x, p x) h3))
(fun h1 : (∃ x, p x) ∨ (∃ x, q x) => Or.elim h1
  (fun h2 : ∃ x, p x => Exists.elim h2
    fun y : α =>
      fun hp : p y =>
        have h3 : p y ∨ q y := Or.intro_left (q y) hp
        Exists.intro y h3)
  (fun h2 : ∃ x, q x => Exists.elim h2
    fun y : α =>
      fun hq : q y =>
        have h3 : p y ∨ q y := Or.intro_right (p y) hq
        Exists.intro y h3))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
(fun h1 : ∀ x, p x =>
  fun h2 : ∃ x, ¬ p x => Exists.elim h2
    fun y : α =>
      fun hpf : ¬ p y => show False from hpf (h1 y))
(fun h1 : ¬ ∃ x, ¬ p x =>
  fun y : α => show p y from byContradiction
    fun hpf : ¬ p y =>
      have h3 : ∃ x, ¬ p x := Exists.intro y hpf
      show False from h1 h3)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
(fun h1 : ∀ x, p x =>
  fun h2 : ∃ x, ¬ p x => Exists.elim h2
    fun y : α =>
      fun hpf : ¬ p y =>
        have hp : p y := h1 y
        show False from hpf hp)
(fun h1 : ¬ (∃ x, ¬ p x) =>
  fun y : α => show p y from byContradiction
    fun hpf : ¬ p y =>
      have h2 : ∃ x, ¬ p x := Exists.intro y hpf
      show False from h1 h2)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
(fun h1 : ∃ x, p x =>
  fun h2 : ∀ x, ¬ p x => Exists.elim h1
    fun y : α =>
      fun hp : p y =>
        have hpf : ¬ p y := h2 y
        show False from hpf hp)
(fun h1 : ¬ (∀ x, ¬ p x) => show ∃ x, p x from byContradiction
  fun h2 : ¬ ∃ x, p x => h1
    fun y : α =>
      fun hp : p y => h2 (Exists.intro y hp))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro
(fun h1 : ¬ ∃ x, p x =>
  fun y : α =>
    fun hp : p y => h1 (Exists.intro y hp))
(fun h1 : ∀ x, ¬ p x =>
  fun h2 : ∃ x, p x => Exists.elim h2
  (fun y : α =>
    fun hp : p y => (h1 y) hp))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro
(fun h1 : ¬ ∀ x, p x => show ∃ x, ¬ p x from byContradiction
  fun h2 : ¬ ∃ x, ¬ p x => h1
    fun y : α => show p y from byContradiction
      fun hpf : ¬ p y => h2 (Exists.intro y hpf))
(fun h1 : ∃ x, ¬ p x =>
  fun h2 : ∀ x, p x => Exists.elim h1
    fun y : α =>
      fun hpf : ¬ p y => hpf (h2 y))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
(fun h1 : ∀ x, p x → r =>
  fun h2 : ∃ x, p x => Exists.elim h2
    fun y : α =>
      fun hp : p y => (h1 y) hp)
(fun h1 : (∃ x, p x) → r =>
  fun y : α =>
    fun hp : p y => h1 (Exists.intro y hp))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
(fun h1 : ∃ x, p x → r =>
  fun h2 : ∀ x, p x => Exists.elim h1
    fun y : α =>
      fun h3 : p y → r => h3 (h2 y))
(fun h1 : (∀ x, p x) → r => Or.elim (em r)
  (fun hr : r =>
    have h2 : p a → r := fun _ : p a => hr
    show ∃ x, p x → r from (Exists.intro a h2))
  (fun h2 : ¬ r => show ∃ x, p x → r from byContradiction
    fun h3 : ¬ ∃ x, p x → r => h2
      (show r from h1 (fun y : α => show p y from byContradiction
          fun hpf : ¬ p y => h3
            (have h4 : p y → r := fun hp : p y => False.elim (hpf hp)
            show (∃ x, p x → r) from (Exists.intro y h4))))))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
(fun h1 : ∃ x, r → p x =>
  fun hr : r => Exists.elim h1
    (fun y : α =>
      fun h2 : r → p y =>
        have hp : p y := h2 hr
        Exists.intro y hp))
(fun h1 : r → ∃ x, p x => Or.elim (em r)
  (fun hr : r =>
    have h2 : ∃ x, p x := h1 hr
    Exists.elim h2 (fun y : α =>
      fun hp : p y =>
        have h3 : r → p y := fun _ : r => hp
        Exists.intro y h3))
  (fun hrf : r → False =>
    have h2 : r → p a := fun hr : r => False.elim (hrf hr)
    Exists.intro a h2))

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := Iff.intro
(fun h1 : ∀ x, p x ∧ q x => And.intro
  (fun y : α => (h1 y).left)
  (fun y : α => (h1 y).right))
(fun h1 : (∀ x, p x) ∧ (∀ x, q x) =>
  fun y : α => And.intro (h1.left y) (h1.right y))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
fun h1 : ∀ x, p x → q x =>
  fun h2 : ∀ x, p x =>
    fun y : α => (h1 y) (h2 y)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
fun h1 : (∀ x, p x) ∨ (∀ x, q x) =>
  fun y : α => Or.elim h1
    (fun h2 : ∀ x, p x => Or.intro_left (q y) (h2 y))
    (fun h2 : ∀ x, q x => Or.intro_right (p y) (h2 y))

example : α → ((∀ _ : α, r) ↔ r) :=
fun a : α => Iff.intro
  (fun h1 : (∀ _ : α, r) => h1 a)
  (fun h1 : r =>
    fun _ : α => h1)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
(fun h1 : ∀ x, p x ∨ r => Or.elim (em r)
  (fun hr : r => Or.intro_right (∀ x, p x) hr)
  (fun hrf : ¬ r => suffices h2 : ∀ x, p x from Or.intro_left r h2
    fun y : α =>
      have h3 : p y ∨ r := h1 y
      Or.elim h3
      (fun hp : p y => hp)
      (fun hr : r => show p y from False.elim (hrf hr))))
(fun h1 : (∀ x, p x) ∨ r =>
  fun y : α => Or.elim h1
    (fun h2 : ∀ x, p x => Or.intro_left r (h2 y))
    (fun hr : r => Or.intro_right (p y) hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
(fun h1 : ∀ x, r → p x =>
  fun hr : r =>
    fun y : α => (h1 y) hr)
(fun h1 : r → ∀ x, p x =>
  fun y : α =>
    fun hr : r => (h1 hr) y)

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
have hb : shaves barber barber ↔ ¬ shaves barber barber := h barber
have hf : ¬ shaves barber barber := fun ht : shaves barber barber => (hb.mp ht) ht
show False from hf (hb.mpr hf)