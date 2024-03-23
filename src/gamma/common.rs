use std::rc::Rc;

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

#[derive(Clone, Debug)]
pub struct Binder<T, const N: usize = 1> {
	pub parameters: [Option<Name>; N],
	pub body: T,
}

impl<T, const N: usize> Binder<T, N> {
	pub fn new(parameters: [Option<Name>; N], body: T) -> Self { Self { parameters, body } }
}

pub fn bind<T, const N: usize>(parameters: [Option<Name>; N], body: impl Into<T>) -> Binder<T, N> {
	Binder::new(parameters, body.into())
}

impl<T> Binder<T, 1> {
	pub fn parameter(&self) -> Option<Name> {
		let [parameter] = self.parameters;
		parameter
	}
}

impl<A, const N: usize> Binder<A, N> {
	pub fn map_ref<B, C: From<B>>(&self, f: impl FnOnce(&A) -> B) -> Binder<C, N> {
		Binder { parameters: self.parameters, body: f(&self.body).into() }
	}

	pub fn mapv<B, C: From<B>>(self, f: impl FnOnce([Option<Name>; N], A) -> B) -> Binder<C, N> {
		Binder { parameters: self.parameters, body: f(self.parameters, self.body).into() }
	}
}

#[derive(Clone, Debug)]
pub struct AnyBinder<T> {
	pub parameters: Box<[Option<Name>]>,
	pub body: T,
}

pub fn any_bind<T>(parameters: impl Into<Box<[Option<Name>]>>, body: impl Into<T>) -> AnyBinder<T> {
	AnyBinder { parameters: parameters.into(), body: body.into() }
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
pub enum Copyability {
	Trivial = 0,
	Nontrivial = 1,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum ReprAtom {
	Class,
	Pointer,
	Byte,
	Nat,
	Fun,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Repr {
	Atom(ReprAtom),
	Pair(Rc<Repr>, Rc<Repr>),
	Max(Rc<Repr>, Rc<Repr>),
}

impl Repr {
	pub fn pair(a: Option<Self>, b: Option<Self>) -> Option<Self> {
		match (a, b) {
			(None, b) => b,
			(a, None) => a,
			(Some(a), Some(b)) => Some(Self::Pair(a.into(), b.into())),
		}
	}

	pub fn max(a: Option<Self>, b: Option<Self>) -> Option<Self> {
		match (a, b) {
			(None, b) => b,
			(a, None) => a,
			(Some(a), Some(b)) => Some(Self::Max(a.into(), b.into())),
		}
	}
}

#[derive(Clone, Debug)]
pub struct UniverseKind(pub Copyability, pub Option<Repr>);
