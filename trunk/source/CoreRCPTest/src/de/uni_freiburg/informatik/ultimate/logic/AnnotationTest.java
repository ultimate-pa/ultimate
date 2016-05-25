package de.uni_freiburg.informatik.ultimate.logic;

import org.junit.Assert;
import org.junit.Test;

public class AnnotationTest {



	@Test
	public void idtestPlugin() {
		final Annotation anno = new Annotation("somekey", this);

		Assert.assertEquals("Keytest", "somekey", anno.getKey());
		Assert.assertEquals("Valtest", this, anno.getValue());
	}
}
