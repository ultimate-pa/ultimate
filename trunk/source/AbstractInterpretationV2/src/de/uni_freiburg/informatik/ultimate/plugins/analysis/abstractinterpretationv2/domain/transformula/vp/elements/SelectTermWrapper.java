package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Set;

public class SelectTermWrapper implements IElementWrapper {
	
	IArrayWrapper mArray;

	List<IElementWrapper> mIndices; // this is a list because we may have a multidimensional array

	WrapperSideCondition mSideCondition;
	
	

//	public SelectTermWrapper(IArrayWrapper mArray, List<IElementWrapper> mIndices,
//			WrapperSideCondition mSideCondition) {
//		super();
//		this.mArray = mArray;
//		this.mIndices = mIndices;
//		this.mSideCondition = mSideCondition;
//	}



	public SelectTermWrapper(IArrayWrapper array, List<IElementWrapper> indices) {
		this.mArray = mArray;
		this.mIndices = mIndices;
	}



	@Override
	public Set<ISingleElementWrapper> getElements() {
//		return Collections.singleton(this); // TODO: not sure about this
		assert false;
		return null;
	}
}
