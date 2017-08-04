package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import java.io.File;

import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.Option.Builder;

public class ExistingFileOption extends AbstractFileOption {
	public ExistingFileOption(final Builder option) {
		super(option);
	}

	@Override
	protected void check(final File f) throws ParseException {
		if (!f.isFile()) {
			throw new ParseException(String.format("%1$s is not a valid File.", f.getName()));
		}
	}
}