package de.uni_freiburg.informatik.ultimate.model;

public class AbstractElementTest extends IElementTest<IElement> {

	@Override
	protected IElement createInstance() {
		return new AbstractElement();
	}
	
}
