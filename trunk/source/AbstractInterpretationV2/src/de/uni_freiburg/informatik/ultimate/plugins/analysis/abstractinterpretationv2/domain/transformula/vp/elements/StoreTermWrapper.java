package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;

public class StoreTermWrapper implements IArrayWrapper {

	private IArrayWrapper mBaseArray;
	
	private List<IElementWrapper> mIndex; // this is a list because the array may be multidimensional

	private IElementWrapper mValue;
	
	
}
