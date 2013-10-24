package de.uni_freiburg.informatik.ultimate;

import org.junit.Before;
import org.junit.Test;
import org.junit.Assert;

public abstract class InterfaceTest<T> {
	
	protected T instance;
	
	protected abstract T createInstance();
	
	@Before
	public void createTestInstance() {
		this.instance = createInstance();
	}
	
	@Test
	public void createInstanceCreatesDifferentInstances() {
		T i1 = createInstance();
		T i2 = createInstance();
		
		// Reference comparison
		boolean same = i1 == i2;
		
		Assert.assertFalse("Instances must not be reference equal", same);
	}
	
}
