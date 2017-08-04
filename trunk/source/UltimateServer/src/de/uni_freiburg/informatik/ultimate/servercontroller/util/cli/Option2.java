package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import java.util.List;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;

import de.uni_freiburg.informatik.ultimate.servercontroller.util.cli.CommandLineArgs.IOption;

public abstract class Option2<T, ME extends Option2<T, ME>> implements IOption<T> {
	private final static String PARSE_EXCEPTION_MESSAGE = "Invalid value: %s cannot be parsed as %s";
	final Option mOption;
	private T Default;
	private T value;

	@Override
	public T getValue() {
		return value;
	}

	public abstract Class<T> getType();

	public Option2(final Option.Builder option) {
		mOption = option.type(getType()).build();
	}

	ME defaultValue(final T value) {
		Default = value;
		return (ME) this;
	}

	ME addTo(final List<? super ME> options) {
		// Options options = new Options();
		// options.addOption(mOption);
		final ME me = (ME) this;
		options.add(me);
		return me;
	}

	public final void parse(final CommandLine commandLine) throws ParseException {
		value = getOptionValue(commandLine);
	}

	protected T getParsed(final CommandLine commandLine) throws ParseException {
		return (T) commandLine.getParsedOptionValue(mOption.getOpt());
	}

	protected final String getStringValue(final CommandLine commandLine) {
		return commandLine.getOptionValue(mOption.getOpt());
	}

	private T getOptionValue(final CommandLine commandLine) throws ParseException {
		if (commandLine.hasOption(mOption.getOpt())) {
			try {
				final T result = getParsed(commandLine);
				return result;
			} catch (final ParseException e) {
				throw new ParseException(
						String.format(PARSE_EXCEPTION_MESSAGE, getStringValue(commandLine), mOption.getArgName()));
			}
		}
		return Default;
	}
}