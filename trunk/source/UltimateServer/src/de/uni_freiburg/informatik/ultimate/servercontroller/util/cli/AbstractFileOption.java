package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import java.io.File;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;

public abstract class AbstractFileOption extends Option2<File, ExistingDirOption> {
	public AbstractFileOption(final Option.Builder option) {
		super(option);
	}

	@Override
	protected File getParsed(final CommandLine commandLine) throws ParseException {
		final File f = super.getParsed(commandLine);
		check(f);
		return f;
	}

	protected abstract void check(final File f) throws ParseException;

	@Override
	public Class<File> getType() {
		return File.class;
	}
}