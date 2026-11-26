package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.Duration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExactDurationValue;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.IntervalDurationValue;

/** Integer millisecond clock. Months and years are explicitly fixed approximations. */
public final class EcaBoogieTimeEncoding {
	private EcaBoogieTimeEncoding() {
	}

	public record Bounds(BigInteger lower, BigInteger upper, BigInteger unitMillis) {
		public BigInteger lowerMillis() {
			return lower.multiply(unitMillis);
		}

		public BigInteger upperMillis() {
			return upper.multiply(unitMillis);
		}
	}

	public static BigInteger unitMillis(final Duration.TimeUnit unit) {
		return BigInteger.valueOf(switch (unit) {
		case MS -> 1L;
		case S -> 1_000L;
		case MIN -> 60_000L;
		case H -> 3_600_000L;
		case MONTH -> 2_592_000_000L;
		case YEAR -> 31_536_000_000L;
		});
	}

	public static Bounds bounds(final Duration duration, final boolean positive) {
		final BigInteger lower;
		final BigInteger upper;
		if (duration.getValue() instanceof final ExactDurationValue exact) {
			lower = exact.getAmount();
			upper = lower;
		} else {
			final IntervalDurationValue interval = (IntervalDurationValue) duration.getValue();
			lower = interval.getLower();
			upper = interval.getUpper();
		}
		if (lower.signum() < 0 || lower.compareTo(upper) > 0 || positive && lower.signum() == 0) {
			throw new IllegalArgumentException("Invalid " + (positive ? "positive period" : "duration") + " interval ["
					+ lower + ":" + upper + "]");
		}
		return new Bounds(lower, upper, unitMillis(duration.getUnit()));
	}
}
