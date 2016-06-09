package de.uni_freiburg.informatik.ultimate.model.structure;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.InterfaceTest;
import de.uni_freiburg.informatik.ultimate.core.model.models.IVisualizable;

//import de.uni_freiburg.informatik.junit_helper.InterfaceTest;

public abstract class IVisualizableTest<T extends IVisualizable> extends InterfaceTest<T> {

	//TODO: Not exactly specified, if this is really specified in the interface! Check this!
	@Test
	public void getVisualizationGraphNotNull() {
		Assert.assertNotNull(instance.getVisualizationGraph());
	}
	
}
