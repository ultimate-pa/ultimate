package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class DummyLocation implements ILocation {
	
	private final String mFilename;
	
	public DummyLocation(String filename) {
		mFilename = filename;
	}
	
	@Override
	public String getFileName() {
		// TODO Auto-generated method stub
		return mFilename;
	}
	
	@Override
	public int getStartLine() {
		// TODO Auto-generated method stub
		return 0;
	}
	
	@Override
	public int getEndLine() {
		// TODO Auto-generated method stub
		return 0;
	}
	
	@Override
	public int getStartColumn() {
		// TODO Auto-generated method stub
		return 0;
	}
	
	@Override
	public int getEndColumn() {
		// TODO Auto-generated method stub
		return 0;
	}
	
	@Override
	public ILocation getOrigin() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public IAnnotations getCheck() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public boolean isLoop() {
		// TODO Auto-generated method stub
		return false;
	}
	
}
