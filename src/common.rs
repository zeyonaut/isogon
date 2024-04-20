use std::{
	ops::{AddAssign, Mul, MulAssign},
	rc::Rc,
};

use lasso::Spur;

// de Bruijn index: zero is the newest bound parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Index(pub(super) usize);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Level(pub(super) usize);

impl Level {
	pub fn index(self, index: usize) -> Self { Self(self.0 - (index + 1)) }
}

impl std::ops::Add<usize> for Level {
	type Output = Self;
	fn add(self, rhs: usize) -> Self::Output {
		let Self(level) = self;
		Self(level + rhs)
	}
}

impl std::ops::AddAssign<usize> for Level {
	fn add_assign(&mut self, rhs: usize) { self.0 += rhs; }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Field {
	Base,
	Fiber,
}

pub type Name = Spur;
pub type Label = Option<Name>;

#[derive(Clone, Debug)]
pub struct Binder<P, T, const N: usize = 1> {
	pub parameters: [P; N],
	pub body: T,
}

impl<P, T, const N: usize> Binder<P, T, N> {
	pub fn new(parameters: [P; N], body: T) -> Self { Self { parameters, body } }
}

pub fn bind<P, T, const N: usize>(parameters: [P; N], body: impl Into<T>) -> Binder<P, T, N> {
	Binder::new(parameters, body.into())
}

impl<P: Copy, T> Binder<P, T, 1> {
	pub fn parameter(&self) -> P {
		let [parameter] = self.parameters;
		parameter
	}
}

impl<P, A, const N: usize> Binder<P, A, N> {
	pub fn map_ref<B, C: From<B>>(&self, f: impl FnOnce(&A) -> B) -> Binder<P, C, N>
	where
		P: Copy,
	{
		Binder { parameters: self.parameters, body: f(&self.body).into() }
	}

	pub fn mapv<B, C: From<B>>(self, f: impl FnOnce([P; N], A) -> B) -> Binder<P, C, N>
	where
		P: Copy,
	{
		Binder { parameters: self.parameters, body: f(self.parameters, self.body).into() }
	}

	pub fn map_into<B: From<A>>(self) -> Binder<P, B, N> {
		Binder { parameters: self.parameters, body: self.body.into() }
	}
}

impl<P, A, B, const N: usize> Binder<P, (A, B), N> {
	pub fn retract(self) -> (Binder<P, A, N>, B) {
		(Binder { parameters: self.parameters, body: self.body.0 }, self.body.1)
	}
}

impl<P, A, B, C, const N: usize> Binder<P, (A, B, C), N> {
	pub fn retract2(self) -> (Binder<P, A, N>, B, C) {
		(Binder { parameters: self.parameters, body: self.body.0 }, self.body.1, self.body.2)
	}
}

#[derive(Clone, Debug)]
pub struct AnyBinder<P, T> {
	pub parameters: Box<[P]>,
	pub body: T,
}

impl<P, T> AnyBinder<P, T> {
	pub fn new(parameters: Box<[P]>, body: T) -> Self { Self { parameters, body } }

	pub fn try_resolve<const N: usize>(self) -> Result<Binder<P, T, N>, Box<[P]>> {
		Ok(Binder { parameters: *(<Box<_>>::try_from(self.parameters)?), body: self.body })
	}
}

impl<P, T, const N: usize> From<Binder<P, T, N>> for AnyBinder<P, T> {
	fn from(value: Binder<P, T, N>) -> Self { Self { parameters: value.parameters.into(), body: value.body } }
}

pub fn any_bind<P, T>(parameters: impl Into<Box<[P]>>, body: impl Into<T>) -> AnyBinder<P, T> {
	AnyBinder::new(parameters.into(), body.into())
}

#[derive(Clone, Debug)]
pub struct Closure<E, T, const N: usize = 1> {
	pub environment: E,
	pub parameters: [Option<Name>; N],
	pub body: T,
}

impl<E, T, const N: usize> Closure<E, T, N> {
	pub fn new(environment: E, parameters: [Option<Name>; N], body: T) -> Self {
		Self { environment, parameters, body }
	}
}

impl<E, T> Closure<E, T, 1> {
	pub fn parameter(&self) -> Option<Name> {
		let [parameter] = self.parameters;
		parameter
	}
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum Cpy {
	Tr = 0,
	Nt = 1,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum ReprAtom {
	Byte,
	Nat,
	Ptr,
	Fun,
}

// A number greater than one.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct ArraySize(pub usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Repr {
	Atom(ReprAtom),
	Pair(Rc<Repr>, Rc<Repr>),
	Array(ArraySize, Rc<Repr>),
}

#[derive(Clone, Debug)]
pub struct UniverseKind {
	pub copy: Cpy,
	pub repr: Option<Repr>,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Cost {
	Fin(usize),
	Inf,
}

impl Mul for Cost {
	type Output = Cost;
	fn mul(self, rhs: Self) -> Self::Output {
		match (self, rhs) {
			(Self::Fin(a), Self::Fin(b)) => Self::Fin(a * b),
			(Self::Fin(0), _) => Self::Fin(0),
			(_, Self::Fin(0)) => Self::Fin(0),
			(Self::Inf, _) => Self::Inf,
			(_, Self::Inf) => Self::Inf,
		}
	}
}

impl MulAssign for Cost {
	fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<T: Into<Cost>> AddAssign<T> for Cost {
	fn add_assign(&mut self, rhs: T) {
		match (self, rhs.into()) {
			(Self::Fin(a), Self::Fin(b)) => *a += b,
			(Self::Inf, _) => (),
			(a, Self::Inf) => *a = Self::Inf,
		}
	}
}

impl From<usize> for Cost {
	fn from(value: usize) -> Self { Self::Fin(value) }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Fragment {
	Logical = 0,
	Material = 1,
}

impl Fragment {
	pub fn is_logical(self) -> bool { self == Self::Logical }
}

impl From<Fragment> for Cost {
	fn from(value: Fragment) -> Self { Self::Fin(value as u8 as _) }
}
