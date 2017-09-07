package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import org.apache.commons.cli.Option;

public class StringOption extends Option2<String, StringOption> {

	public StringOption(final Option.Builder option) {
		super(option);
	}

	@Override
	public Class<String> getType() {
		return String.class;
	}
}