macro_rules! bx {
	($x:expr) => {
		::std::boxed::Box::new($x)
	};
}

pub(crate) use bx;

macro_rules! rc {
	($x:expr) => {
		::std::rc::Rc::new($x)
	};
}

pub(crate) use rc;
