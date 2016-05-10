package de.uni_freiburg.informatik.ultimate.model.structure;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.model.IElementTest;
import de.uni_freiburg.informatik.ultimate.models.structure.IWalkable;

public abstract class IWalkableTest<T extends IWalkable> extends IElementTest<T> {
	
	@Test
	public void getSuccessorNeverReturnsNull() {
		Assert.assertNull(instance.getSuccessors());
	}
	
}
