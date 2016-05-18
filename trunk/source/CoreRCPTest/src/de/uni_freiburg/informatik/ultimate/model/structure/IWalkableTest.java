package de.uni_freiburg.informatik.ultimate.model.structure;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.IElementTest;

public abstract class IWalkableTest<T extends IWalkable> extends IElementTest<T> {
	
	@Test
	public void getSuccessorNeverReturnsNull() {
		Assert.assertNull(instance.getSuccessors());
	}
	
}
