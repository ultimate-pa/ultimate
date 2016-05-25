package de.uni_freiburg.informatik.ultimate;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public abstract class InterfaceTest<T> {
	
	protected T instance;
	
	protected abstract T createInstance();
	
	@Before
	public void createTestInstance() {
		this.instance = createInstance();
	}
	
	@Test
	public void createInstanceCreatesDifferentInstances() {
		final T i1 = createInstance();
		final T i2 = createInstance();
		
		// Reference comparison
		final boolean same = i1 == i2;
		
		Assert.assertFalse("Instances must not be reference equal", same);
	}
	
}
