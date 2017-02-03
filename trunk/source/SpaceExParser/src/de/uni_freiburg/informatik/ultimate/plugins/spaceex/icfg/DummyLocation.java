package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class DummyLocation implements ILocation {

	private final String mFilename;

	public DummyLocation(final String filename) {
		mFilename = filename;
	}

	@Override
	public String getFileName() {
		return mFilename;
	}

	@Override
	public int getStartLine() {
		return -1;
	}

	@Override
	public int getEndLine() {
		return -1;
	}

	@Override
	public int getStartColumn() {
		return -1;
	}

	@Override
	public int getEndColumn() {
		return -1;
	}

	@Override
	public ILocation getOrigin() {
		return null;
	}

	@Override
	public IAnnotations getCheck() {
		return null;
	}

	@Override
	public boolean isLoop() {
		return false;
	}

}
