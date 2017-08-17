package de.uni_freiburg.informatik.ultimate.servercontroller.util.cli;

import org.apache.commons.cli.Option;

public class IntOption extends Option2<Integer, IntOption> {

	public IntOption(final Option.Builder option) {
		super(option);
	}

	@Override
	public Class<Integer> getType() {
		return Integer.class;
	}
}