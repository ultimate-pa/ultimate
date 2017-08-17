package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;

import de.uni_freiburg.informatik.ultimate.servercontroller.util.Either;
import de.uni_freiburg.informatik.ultimate.servercontroller.util.Parser;

public class EitherOption<L, R> extends Option2<Either<L, R>, EitherOption<L, R>> {
//	public static <L, R> EitherOption<L, R> from(final Option.Builder option) {
//		
//	}

	private final Parser<String, L> lparser;
	private final Parser<String, R> rparser;

	public EitherOption(final Option.Builder option, final Parser<String, L> lparser, final Parser<String, R> rparser) {
		super(option);
		this.lparser = lparser;
		this.rparser = rparser;
	}

	@Override
	protected Either<L, R> getParsed(final CommandLine commandLine) throws ParseException {
		return Either.parse(getStringValue(commandLine), lparser, rparser);
	}

	@Override
	public Class<Either<L, R>> getType() {
		return null;
	}
}