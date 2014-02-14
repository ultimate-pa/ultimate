package de.uni_freiburg.informatik.ultimate.logic;

import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;
/*
import org.junit.experimental.categories.Category;

import de.uni_freiburg.informatik.junit_helper.categories.ExampleCategory;
*/

public class AnnotationTest {

	@Test
	public void testA() {
		Assert.assertEquals(true, true);
	}
	
	@Test
	public void gtest23333sdfg() {
		System.out.println("Some output");
		Assert.assertEquals("this test should fail!", false, true);
	}

	@Test
	// @Category(ExampleCategory.class)
	public void idtestPlugin() {
		Annotation anno = new Annotation("somekey", this);

		Assert.assertEquals("Keytest", "somekey", anno.getKey());
		Assert.assertEquals("Valtest", this, anno.getValue());
		//Assert.assertEquals("bla", 2, anno.hashCode());
	}
}
