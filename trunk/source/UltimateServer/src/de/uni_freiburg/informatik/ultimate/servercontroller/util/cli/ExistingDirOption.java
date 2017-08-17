package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import java.io.File;

import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.Option.Builder;

public class ExistingDirOption extends AbstractFileOption {
	public ExistingDirOption(final Builder option) {
		super(option);
	}

	@Override
	protected void check(final File f) throws ParseException {
		if (!f.isDirectory()) {
			throw new ParseException(String.format("%1$s is not a valid Directory.", f.getName()));
		}
	}
}