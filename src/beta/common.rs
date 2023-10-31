pub type Name = String;

// de Bruijn index: zero is the newest bound parameter.
#[derive(Clone, PartialEq, Debug)]
pub struct Index(pub(super) usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Metavariable(pub(super) usize);
