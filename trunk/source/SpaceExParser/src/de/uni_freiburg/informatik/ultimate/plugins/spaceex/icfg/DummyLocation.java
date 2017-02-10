package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;

public class DummyLocation extends DefaultLocation {

	private static final long serialVersionUID = 4063704608726743410L;

	public DummyLocation(final String filename) {
		super(filename, -1, -1, -1, -1);
	}
}
