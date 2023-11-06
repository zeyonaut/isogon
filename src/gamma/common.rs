// de Bruijn index: zero is the newest bound parameter.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Index(pub(super) usize);
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Level(pub(super) usize);

impl Level {
	pub fn suc(self) -> Self {
		let Self(level) = self;
		Self(level + 1)
	}
}
