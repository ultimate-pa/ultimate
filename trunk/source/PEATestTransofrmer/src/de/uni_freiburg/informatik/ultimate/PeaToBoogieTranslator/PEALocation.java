package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;


import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class PEALocation<T> implements ILocation {
	
	// pea element (e.g. edge, phase, ...)
	private T element;
	private ILocation origin;
	
	public PEALocation(T element){
		this.element = element;
	}
	
	public T getElement(){
		return this.element;
	}

	@Override
	public String getFileName() {
		return this.origin.getFileName();
	}

	@Override
	public int getStartLine() {
		return this.origin.getStartLine();
	}

	@Override
	public int getEndLine() {
		return this.origin.getEndLine();
	}

	@Override
	public int getStartColumn() {
		return this.origin.getStartColumn();
	}

	@Override
	public int getEndColumn() {
		return this.origin.getEndColumn();
	}

	@Override
	public ILocation getOrigin() {
		return this.origin;
	}

	@Override
	public Check getCheck() {
		return null;
	}

	@Override
	public boolean isLoop() {
		return false;
	}

}
