package de.uni_freiburg.informatik.ultimate.servercontroller.util;

import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;

import org.apache.commons.cli.ParseException;

final public class Either<L, R> {
	public static <L, R> Either<L, R> left(final L value) {
		return new Either<>(Optional.of(value), Optional.empty());
	}

	public static <L, R> Either<L, R> right(final R value) {
		return new Either<>(Optional.empty(), Optional.of(value));
	}

	public static <In, L, R> Either<L, R> parse(final In input, final Parser<In, L> lparser,
			final Parser<In, R> rparser) throws ParseException {
		try {
			final L lout = lparser.parse(input);
			return left(lout);
		} catch (ParseException | java.text.ParseException le) {
			try {
				final R rout = rparser.parse(input);
				return right(rout);
			} catch (ParseException | java.text.ParseException e) {
				throw new ParseException(le.getMessage() + " ### " + e.getMessage());
			}
		}

	}

	private final Optional<L> left;
	private final Optional<R> right;

	private Either(final Optional<L> l, final Optional<R> r) {
		left = l;
		right = r;
	}

	public <T> T map(final Function<? super L, ? extends T> lFunc, final Function<? super R, ? extends T> rFunc) {
		return left.<T> map(lFunc).orElseGet(() -> right.map(rFunc).get());
	}

	public <T> Either<T, R> mapLeft(final Function<? super L, ? extends T> lFunc) {
		return new Either<>(left.map(lFunc), right);
	}

	public <T> Either<L, T> mapRight(final Function<? super R, ? extends T> rFunc) {
		return new Either<>(left, right.map(rFunc));
	}

	public void apply(final Consumer<? super L> lFunc, final Consumer<? super R> rFunc) {
		left.ifPresent(lFunc);
		right.ifPresent(rFunc);
	}
}