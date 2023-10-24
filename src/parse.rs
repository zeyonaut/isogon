use nom::IResult;

// This is adapted directly from Nom, with only two changes made: we change the return type to FnOnce, and the type of the initializer to FnOnce.
pub fn fold_many0_once<I, O, E, F, G, H, R>(mut f: F, init: H, mut g: G) -> impl FnOnce(I) -> IResult<I, R, E>
where
	I: Clone + nom::InputLength,
	F: nom::Parser<I, O, E>,
	G: FnMut(R, O) -> R,
	H: FnOnce() -> R,
	E: nom::error::ParseError<I>,
{
	move |i: I| {
		let mut res = init();
		let mut input = i;

		loop {
			let i_ = input.clone();
			let len = input.input_len();
			match f.parse(i_) {
				Ok((i, o)) => {
					// infinite loop check: the parser must always consume
					if i.input_len() == len {
						return Err(nom::Err::Error(E::from_error_kind(input, nom::error::ErrorKind::Many0)));
					}

					res = g(res, o);
					input = i;
				}
				Err(nom::Err::Error(_)) => {
					return Ok((input, res));
				}
				Err(e) => {
					return Err(e);
				}
			}
		}
	}
}
