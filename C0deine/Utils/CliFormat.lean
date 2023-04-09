import C0deine.AuxDefs

namespace C0deine.Utils.CliFormat

structure Rect where
  (width height : Nat)
  lines : List String
  h_height : lines.length = height
  h_width : ∀ l, l ∈ lines → l.length = width

def Rect.ofLines (lines : List String) : Rect :=
  let width := lines.foldr (max ·.length) 0
  have : ∀ l, l ∈ lines → l.length ≤ width := by
    intro l hl
    induction lines
    . simp at hl
    . simp at hl ⊢
      cases hl
      . simp [*, Nat.le_max_left]
      . apply Nat.le_trans _ (Nat.le_max_right ..)
        simp [*] at *
  { width, height := lines.length
  , lines := lines.map (fun l => l.pushn ' ' (width - l.length))
  , h_height := by simp, h_width := by
      intro l h
      rw [List.mem_map] at h
      rcases h with ⟨l',hl',rfl⟩
      simp; rw [Nat.add_comm]
      apply Nat.sub_add_cancel
      apply this _ hl'
  }

def Rect.ofString (s : String) : Rect :=
  have lines := s.splitOn "\n"
  Rect.ofLines lines

instance : Coe Char Rect where
  coe c := .ofString c.toString

instance : Coe String Rect where
  coe s := .ofString s

instance : Coe (List String) Rect where
  coe l := .ofLines l

instance : Coe Rect String where
  coe r := String.intercalate "\n" r.lines

inductive HAlign | left | center | right
inductive VAlign | top | center | bottom

def Rect.padHeight (r : Rect) (height : Nat) (h_height : r.height ≤ height)
                  (align : VAlign) : Rect :=
  { height, width := r.width
  , lines :=
    match align with
    | .top    => r.lines ++ List.replicate (height - r.height) ("".pushn ' ' r.width)
    | .bottom => List.replicate (height - r.height) ("".pushn ' ' r.width) ++ r.lines
    | .center => let top := (height - r.height)/2
                 List.replicate top ("".pushn ' ' r.width) ++ r.lines ++
                 List.replicate (height - r.height - top) ("".pushn ' ' r.width)
  , h_height := by
      split <;> simp [r.h_height]
      . apply Nat.add_sub_cancel' h_height
      . apply Nat.sub_add_cancel h_height
      . rw [← Nat.add_assoc, Nat.sub_sub, Nat.add_comm r.height]
        apply Nat.add_sub_cancel'
        apply Nat.add_le_of_le_sub h_height
        apply Nat.div_le_self
  , h_width := by
      intro l h
      cases align <;> (
        simp at h
        cases h <;> (try rename _ ∨ _ => h; cases h) <;>
          first
          | (apply r.h_width; assumption)
          | (have := List.mem_replicate.mp (by assumption) |>.2
             cases this; simp; simp [String.length])
        )
  }

def Rect.padWidth (r : Rect) (width : Nat) (h_width : r.width ≤ width)
                  (align : HAlign) : Rect :=
  { width, height := r.height
  , lines := r.lines.map (fun l => 
    match align with
    | .left   => l.pushn ' ' (width - l.length)
    | .right  => "".pushn ' ' (width - l.length) ++ l
    | .center => let left := (width - l.length)/2
                 "".pushn ' ' left ++ l |>.pushn ' ' (width-l.length-left)
    )
  , h_height := by simp [r.h_height], h_width := by
      intros; have := List.mem_map.mp (by assumption)
      rcases this with ⟨line,hmem,rfl⟩
      have := r.h_width _ hmem
      cases align <;> simp at * <;> simp [*]
      . apply Nat.add_sub_cancel' h_width
      . simp [String.length]; rw [Nat.sub_sub, Nat.add_comm r.width]
        apply Nat.add_sub_cancel'
        apply Nat.add_le_of_le_sub h_width
        apply Nat.div_le_self
      . simp [String.length]; apply Nat.sub_add_cancel h_width
  }

def Rect.joinVert (top bottom : Rect) (h : top.width = bottom.width) : Rect :=
  { width := top.width, height := top.height + bottom.height
  , lines := top.lines ++ bottom.lines
  , h_height := by simp [top.h_height, bottom.h_height]
  , h_width := by simp (config := {contextual := true}) [or_imp, h, top.h_width, bottom.h_width]}

def Rect.joinHorz (left right : Rect) (h : left.height = right.height) : Rect :=
  { height := left.height, width := left.width + right.width
  , lines := List.zipWith (· ++ ·) left.lines right.lines
  , h_height := by simp [left.h_height, right.h_height, h]; apply Nat.min_eq_left (Nat.le_refl _)
  , h_width := by intro l hl; have := List.mem_zipWith hl
                  rcases this with ⟨y,z, rfl, hy, hz⟩
                  simp [left.h_width _ hy, right.h_width _ hz]}

def empty : Rect := { width := 0, height := 0, lines := [], h_width := by simp, h_height := by simp }

def fill (c : Char) (width height : Nat) : Rect :=
  { width, height, lines := List.replicate height ("".pushn c width)
  , h_width := by intro l hl; have := List.mem_replicate.mp hl; simp [this]; simp [String.length]
  , h_height := by simp }

def space (width height : Nat) : Rect :=
  fill ' ' width height

@[simp] theorem space.width_eq : (space w h).width = w := by
  simp [space, fill]

@[simp] theorem space.height_eq : (space w h).height = h := by
  simp [space, fill]

def Rect.trimHeight (height : Nat) (r : Rect) : Rect :=
  { width := r.width, height := min r.height height
  , lines := r.lines.take height
  , h_width := by intro l hl; have := List.mem_take hl; apply r.h_width _ this
  , h_height := by simp [r.h_height, Nat.min_comm] }

def Rect.trimWidth (width : Nat) (r : Rect) : Rect :=
  { width := min r.width width, height := r.height
  , lines := r.lines.map (·.take width)
  , h_width := by intro l hl; have := List.mem_map.mp hl
                  rcases this with ⟨a, ha, rfl⟩
                  simp [r.h_width _ ha]
  , h_height := by simp [r.h_height, Nat.min_comm] }

def Rect.dropLeft (n : Nat)  (r : Rect): Rect :=
  { width := r.width - n, height := r.height
  , lines := r.lines.map (·.drop n)
  , h_width := by intro l hl; have := List.mem_map.mp hl
                  rcases this with ⟨a,ha,rfl⟩
                  simp [r.h_width _ ha]
  , h_height := by simp [r.h_height]}

def Rect.tileVert (height : Nat) (r : Rect) (hr : r.height > 0) : Rect :=
  { width := r.width, height
  , lines := List.replicate (height / r.height + 1) r.lines |>.join.take height
  , h_width   := by intro l hl
                    have := List.mem_join.mp <| List.mem_take hl
                    rcases this with ⟨l',hl',h⟩
                    rw [List.mem_replicate] at hl'
                    simp at hl'; cases hl'
                    simp [r.h_width _ h]
  , h_height  := by simp [-List.replicate, -List.join]
                    apply Nat.min_eq_left
                    simp [r.h_height]
                    conv => lhs; rw [← Nat.div_add_mod (m := height) (n := r.height)]
                    conv => rhs; rw [Nat.mul_comm _ r.height, Nat.mul_add, Nat.mul_one]
                    apply Nat.add_le_add_left
                    apply Nat.le_of_lt; apply Nat.mod_lt _ hr }

def Rect.tileHorz (width : Nat) (r : Rect) (hr : r.width > 0) : Rect :=
  { width, height := r.height
  , lines := r.lines.map (List.replicate (width / r.width + 1) · |> String.join |>.take width)
  , h_width   := by intro l hl
                    have := List.mem_map.mp hl
                    rcases this with ⟨l',hl',rfl⟩
                    simp
                    apply Nat.min_eq_right
                    sorry
  , h_height  := by simp [r.h_height] }

def vbox (children : List Rect) (align : HAlign := .left)
          (sep : Rect := space 1 0) (hsep : sep.width > 0 := by simp) : Rect :=
  let width := children.foldr (max ·.width) 0
  have : ∀ c, c ∈ children → c.width ≤ width := by
    intro l hl
    induction children
    . simp at hl
    . simp at hl ⊢
      cases hl
      . simp [*, Nat.le_max_left]
      . apply Nat.le_trans _ (Nat.le_max_right ..)
        simp [*] at *
  match children with
  | [] => space width 0
  | c::cs => 
    aux width cs (fun c hc => this c (List.Mem.tail _ hc))
      (c.padWidth width (this c (List.Mem.head _)) align)
      (by simp [Rect.padWidth])
      (sep.tileHorz width hsep)
      (by simp [Rect.tileHorz])
where aux width children (h : ∀ c, c ∈ children → c.width ≤ width)
          acc (hacc : acc.width = width)
          sep (hsep : sep.width = width) :=
  match children with
  | [] => acc
  | c::cs =>
    have := h c (List.Mem.head _)
    aux width cs (fun c hc => h c (List.Mem.tail _ hc))
      (acc.joinVert sep (by simp [hacc, hsep])
        |>.joinVert
          (c.padWidth width this align)
          (by simp [Rect.joinVert, Rect.padWidth, hacc]))
      (by simp [Rect.joinVert, hacc])
      sep hsep

def hbox (children : List Rect) (align : VAlign := .top)
          (sep : Rect := space 0 1) (hsep : sep.height > 0 := by simp) : Rect :=
  let height := children.foldr (max ·.height) 0
  have : ∀ c, c ∈ children → c.height ≤ height := by
    intro l hl
    induction children
    . simp at hl
    . simp at hl ⊢
      cases hl
      . simp [*, Nat.le_max_left]
      . apply Nat.le_trans _ (Nat.le_max_right ..)
        simp [*] at *
  match children with
  | [] => space 0 height
  | c::cs =>
    aux height cs (fun c hc => this c (List.Mem.tail _ hc))
      (c.padHeight height (this c (List.Mem.head _)) align)
      (by simp [Rect.padHeight])
      (sep.tileVert height hsep)
      (by simp [Rect.tileVert])
where aux height children (h : ∀ c, c ∈ children → c.height ≤ height)
          acc (hacc : acc.height = height) sep (hsep : sep.height = height) :=
  match children with
  | [] => acc
  | c::cs =>
    have := h c (List.Mem.head _)
    aux height cs (fun c hc => h c (List.Mem.tail _ hc))
      (acc.joinHorz sep (by simp [hacc, hsep])
        |>.joinHorz
          (c.padHeight height this align)
          (by simp [Rect.joinHorz, Rect.padHeight, hacc]))
      (by simp [Rect.joinHorz, hacc])
      sep hsep
