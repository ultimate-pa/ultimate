package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import org.apache.commons.cli.Option;

public class BoolOption extends Option2<Boolean, BoolOption> {

	public BoolOption(final Option.Builder option) {
		super(option);
	}

	@Override
	public Class<Boolean> getType() {
		return Boolean.class;
	}
}