module
public import Aeneas.Std.Primitives
public import Aeneas.Std.WP
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Aeneas.Std.Scalar.CloneCopy
public import Aeneas.Std.Scalar.EqOrd
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Hash
public import Aeneas.Tactic.Step.Init
public section

/-!
# `core::num::NonZero`

`NonZero<T>` stores `T::NonZeroInner`, one of the niche types in
`core::num::niche_types`, and `NonZero::new` relies on intrinsics to tell
zero apart. So the `ZeroablePrimitive` model carries, besides its parent
clauses, two fields with no counterpart in Rust: `toInner`, which is `none`
exactly at zero, and `ofInner`. `ZeroablePrimitive` is sealed, so every
instance is one of the per-scalar instances below.
-/

namespace Aeneas.Std

open Result ScalarElab

/-! ## The niche types -/

scalar @[expose] def core.num.niche_types.NonZero'SInner : Type := { x : «%S» // x.val ≠ 0 }

scalar instance core.num.niche_types.NonZero'SInner.instDecidableEq :
  DecidableEq core.num.niche_types.NonZero'SInner :=
  inferInstanceAs (DecidableEq { x : «%S» // x.val ≠ 0 })

scalar @[expose, reducible]
def core.num.niche_types.NonZero'SInner.Insts.CoreCloneClone.clone
  (x : core.num.niche_types.NonZero'SInner) : Result core.num.niche_types.NonZero'SInner :=
  ok x

scalar @[expose, reducible]
def core.num.niche_types.NonZero'SInner.Insts.CoreCloneClone :
  core.clone.Clone core.num.niche_types.NonZero'SInner := {
  clone := core.num.niche_types.NonZero'SInner.Insts.CoreCloneClone.clone }

scalar @[expose, reducible]
def core.num.niche_types.NonZero'SInner.Insts.CoreMarkerCopy :
  core.marker.Copy core.num.niche_types.NonZero'SInner := {
  cloneInst := core.num.niche_types.NonZero'SInner.Insts.CoreCloneClone }

/-! ## `ZeroablePrimitive` -/

@[rust_trait "core::num::nonzero::ZeroablePrimitive"
  (parentClauses := ["copyInst", "copyInnerInst"])]
structure core.num.nonzero.ZeroablePrimitive (Self : Type) (NonZeroInner : Type) where
  copyInst : core.marker.Copy Self
  copyInnerInst : core.marker.Copy NonZeroInner
  /-- Not in Rust: `none` exactly at zero. -/
  toInner : Self → Option NonZeroInner
  /-- Not in Rust: the value a niche holds. -/
  ofInner : NonZeroInner → Self

scalar @[expose, reducible]
def core.num.nonzero.ZeroablePrimitive'S :
  core.num.nonzero.ZeroablePrimitive «%S» core.num.niche_types.NonZero'SInner := {
  copyInst := core.marker.Copy'S
  copyInnerInst := core.num.niche_types.NonZero'SInner.Insts.CoreMarkerCopy
  toInner := fun x => if h : x.val = 0 then none else some ⟨ x, h ⟩
  ofInner := fun x => x.val }

/-! ## `NonZero` -/

@[rust_type "core::num::nonzero::NonZero" (body := .opaque)]
structure core.num.nonzero.NonZero (T : Type) (NonZeroInner : Type) where
  inner : NonZeroInner
deriving DecidableEq

namespace core.num.nonzero.NonZero

@[expose, rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::new"]
def new {T NonZeroInner : Type} (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (x : T) : Result (Option (NonZero T NonZeroInner)) :=
  ok ((ZeroablePrimitiveInst.toInner x).map NonZero.mk)

@[expose, rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::get"]
def get {T NonZeroInner : Type} (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (self : NonZero T NonZeroInner) : Result T :=
  ok (ZeroablePrimitiveInst.ofInner self.inner)

@[expose, rust_fun
  "core::num::nonzero::{core::clone::Clone<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>}::clone"]
def Insts.CoreCloneClone.clone {T NonZeroInner : Type}
  (_ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (self : NonZero T NonZeroInner) : Result (NonZero T NonZeroInner) :=
  ok self

@[expose, reducible, rust_trait_impl
  "core::clone::Clone<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>"]
def Insts.CoreCloneClone {T NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner) :
  core.clone.Clone (NonZero T NonZeroInner) := {
  clone := Insts.CoreCloneClone.clone ZeroablePrimitiveInst }

@[expose, reducible, rust_trait_impl
  "core::marker::Copy<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>"]
def Insts.CoreMarkerCopy {T NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner) :
  core.marker.Copy (NonZero T NonZeroInner) := {
  cloneInst := Insts.CoreCloneClone ZeroablePrimitiveInst }

@[expose, rust_fun
  "core::num::nonzero::{core::cmp::PartialEq<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>, core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>}::eq"]
def Insts.CoreCmpPartialEqNonZero.eq {T NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (cmpPartialEqInst : core.cmp.PartialEq T T)
  (self other : NonZero T NonZeroInner) : Result Bool :=
  cmpPartialEqInst.eq (ZeroablePrimitiveInst.ofInner self.inner)
    (ZeroablePrimitiveInst.ofInner other.inner)

@[expose, rust_fun
  "core::num::nonzero::{core::cmp::PartialEq<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>, core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>}::ne"]
def Insts.CoreCmpPartialEqNonZero.ne {T NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (cmpPartialEqInst : core.cmp.PartialEq T T)
  (self other : NonZero T NonZeroInner) : Result Bool :=
  cmpPartialEqInst.ne (ZeroablePrimitiveInst.ofInner self.inner)
    (ZeroablePrimitiveInst.ofInner other.inner)

@[expose, reducible, rust_trait_impl
  "core::cmp::PartialEq<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>, core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>"]
def Insts.CoreCmpPartialEqNonZero {T NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (cmpPartialEqInst : core.cmp.PartialEq T T) :
  core.cmp.PartialEq (NonZero T NonZeroInner) (NonZero T NonZeroInner) := {
  eq := Insts.CoreCmpPartialEqNonZero.eq ZeroablePrimitiveInst cmpPartialEqInst
  ne := Insts.CoreCmpPartialEqNonZero.ne ZeroablePrimitiveInst cmpPartialEqInst }

@[expose, rust_fun
  "core::num::nonzero::{core::hash::Hash<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>}::hash"]
def Insts.CoreHashHash.hash {T H NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (hashHashInst : core.hash.Hash T) (hashHasherInst : core.hash.Hasher H)
  (self : NonZero T NonZeroInner) (state : H) : Result H :=
  hashHashInst.hash hashHasherInst (ZeroablePrimitiveInst.ofInner self.inner) state

@[expose, reducible, rust_trait_impl
  "core::hash::Hash<core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>>"]
def Insts.CoreHashHash {T NonZeroInner : Type}
  (ZeroablePrimitiveInst : ZeroablePrimitive T NonZeroInner)
  (hashHashInst : core.hash.Hash T) :
  core.hash.Hash (NonZero T NonZeroInner) := {
  hash := fun hasherInst => Insts.CoreHashHash.hash ZeroablePrimitiveInst hashHashInst hasherInst }

end core.num.nonzero.NonZero

/-! ## Registration

The Rust names are spelled out per scalar: `scalar` substitutes identifiers, not strings.
-/

attribute [rust_type "core::num::niche_types::NonZeroU8Inner"]
  core.num.niche_types.NonZeroU8Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU8Inner>}::clone"]
  core.num.niche_types.NonZeroU8Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroU8Inner>"]
  core.num.niche_types.NonZeroU8Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroU8Inner>"]
  core.num.niche_types.NonZeroU8Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<u8, core::num::niche_types::NonZeroU8Inner>"]
  core.num.nonzero.ZeroablePrimitiveU8

attribute [rust_type "core::num::niche_types::NonZeroU16Inner"]
  core.num.niche_types.NonZeroU16Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU16Inner>}::clone"]
  core.num.niche_types.NonZeroU16Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroU16Inner>"]
  core.num.niche_types.NonZeroU16Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroU16Inner>"]
  core.num.niche_types.NonZeroU16Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<u16, core::num::niche_types::NonZeroU16Inner>"]
  core.num.nonzero.ZeroablePrimitiveU16

attribute [rust_type "core::num::niche_types::NonZeroU32Inner"]
  core.num.niche_types.NonZeroU32Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU32Inner>}::clone"]
  core.num.niche_types.NonZeroU32Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroU32Inner>"]
  core.num.niche_types.NonZeroU32Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroU32Inner>"]
  core.num.niche_types.NonZeroU32Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<u32, core::num::niche_types::NonZeroU32Inner>"]
  core.num.nonzero.ZeroablePrimitiveU32

attribute [rust_type "core::num::niche_types::NonZeroU64Inner"]
  core.num.niche_types.NonZeroU64Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU64Inner>}::clone"]
  core.num.niche_types.NonZeroU64Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroU64Inner>"]
  core.num.niche_types.NonZeroU64Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroU64Inner>"]
  core.num.niche_types.NonZeroU64Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<u64, core::num::niche_types::NonZeroU64Inner>"]
  core.num.nonzero.ZeroablePrimitiveU64

attribute [rust_type "core::num::niche_types::NonZeroU128Inner"]
  core.num.niche_types.NonZeroU128Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU128Inner>}::clone"]
  core.num.niche_types.NonZeroU128Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroU128Inner>"]
  core.num.niche_types.NonZeroU128Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroU128Inner>"]
  core.num.niche_types.NonZeroU128Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<u128, core::num::niche_types::NonZeroU128Inner>"]
  core.num.nonzero.ZeroablePrimitiveU128

attribute [rust_type "core::num::niche_types::NonZeroUsizeInner"]
  core.num.niche_types.NonZeroUsizeInner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroUsizeInner>}::clone"]
  core.num.niche_types.NonZeroUsizeInner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroUsizeInner>"]
  core.num.niche_types.NonZeroUsizeInner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroUsizeInner>"]
  core.num.niche_types.NonZeroUsizeInner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<usize, core::num::niche_types::NonZeroUsizeInner>"]
  core.num.nonzero.ZeroablePrimitiveUsize

attribute [rust_type "core::num::niche_types::NonZeroI8Inner"]
  core.num.niche_types.NonZeroI8Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroI8Inner>}::clone"]
  core.num.niche_types.NonZeroI8Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroI8Inner>"]
  core.num.niche_types.NonZeroI8Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroI8Inner>"]
  core.num.niche_types.NonZeroI8Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<i8, core::num::niche_types::NonZeroI8Inner>"]
  core.num.nonzero.ZeroablePrimitiveI8

attribute [rust_type "core::num::niche_types::NonZeroI16Inner"]
  core.num.niche_types.NonZeroI16Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroI16Inner>}::clone"]
  core.num.niche_types.NonZeroI16Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroI16Inner>"]
  core.num.niche_types.NonZeroI16Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroI16Inner>"]
  core.num.niche_types.NonZeroI16Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<i16, core::num::niche_types::NonZeroI16Inner>"]
  core.num.nonzero.ZeroablePrimitiveI16

attribute [rust_type "core::num::niche_types::NonZeroI32Inner"]
  core.num.niche_types.NonZeroI32Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroI32Inner>}::clone"]
  core.num.niche_types.NonZeroI32Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroI32Inner>"]
  core.num.niche_types.NonZeroI32Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroI32Inner>"]
  core.num.niche_types.NonZeroI32Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<i32, core::num::niche_types::NonZeroI32Inner>"]
  core.num.nonzero.ZeroablePrimitiveI32

attribute [rust_type "core::num::niche_types::NonZeroI64Inner"]
  core.num.niche_types.NonZeroI64Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroI64Inner>}::clone"]
  core.num.niche_types.NonZeroI64Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroI64Inner>"]
  core.num.niche_types.NonZeroI64Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroI64Inner>"]
  core.num.niche_types.NonZeroI64Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<i64, core::num::niche_types::NonZeroI64Inner>"]
  core.num.nonzero.ZeroablePrimitiveI64

attribute [rust_type "core::num::niche_types::NonZeroI128Inner"]
  core.num.niche_types.NonZeroI128Inner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroI128Inner>}::clone"]
  core.num.niche_types.NonZeroI128Inner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroI128Inner>"]
  core.num.niche_types.NonZeroI128Inner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroI128Inner>"]
  core.num.niche_types.NonZeroI128Inner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<i128, core::num::niche_types::NonZeroI128Inner>"]
  core.num.nonzero.ZeroablePrimitiveI128

attribute [rust_type "core::num::niche_types::NonZeroIsizeInner"]
  core.num.niche_types.NonZeroIsizeInner
attribute [rust_fun "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroIsizeInner>}::clone"]
  core.num.niche_types.NonZeroIsizeInner.Insts.CoreCloneClone.clone
attribute [rust_trait_impl "core::clone::Clone<core::num::niche_types::NonZeroIsizeInner>"]
  core.num.niche_types.NonZeroIsizeInner.Insts.CoreCloneClone
attribute [rust_trait_impl "core::marker::Copy<core::num::niche_types::NonZeroIsizeInner>"]
  core.num.niche_types.NonZeroIsizeInner.Insts.CoreMarkerCopy
attribute [rust_trait_impl "core::num::nonzero::ZeroablePrimitive<isize, core::num::niche_types::NonZeroIsizeInner>"]
  core.num.nonzero.ZeroablePrimitiveIsize

/-! ## Specifications -/

open core.num.nonzero in
scalar @[step]
theorem core.num.nonzero.NonZero.new'S.spec (x : «%S») :
    NonZero.new ZeroablePrimitive'S x ⦃ (r : Option (NonZero «%S» core.num.niche_types.NonZero'SInner)) =>
      match r with
      | none => x.val = 0
      | some n => n.inner.val = x ⦄ := by
  by_cases h : x.val = 0 <;> simp [NonZero.new, h]

open core.num.nonzero in
scalar @[step]
theorem core.num.nonzero.NonZero.get'S.spec (n : NonZero «%S» core.num.niche_types.NonZero'SInner) :
    NonZero.get ZeroablePrimitive'S n ⦃ (v : «%S») =>
      v = n.inner.val ∧ v.val ≠ 0 ⦄ := by
  simp [NonZero.get, n.inner.property]

open core.num.nonzero in
scalar @[step]
theorem core.num.nonzero.NonZero.eq'S.spec (a b : NonZero «%S» core.num.niche_types.NonZero'SInner) :
    NonZero.Insts.CoreCmpPartialEqNonZero.eq ZeroablePrimitive'S core.cmp.PartialEq'S a b
    ⦃ (r : Bool) => r = decide (a = b) ⦄ := by
  obtain ⟨⟨a, ha⟩⟩ := a
  obtain ⟨⟨b, hb⟩⟩ := b
  simp [NonZero.Insts.CoreCmpPartialEqNonZero.eq]
  exact ⟨fun h => by subst h; rfl, fun h => congrArg Subtype.val h⟩

end Aeneas.Std
