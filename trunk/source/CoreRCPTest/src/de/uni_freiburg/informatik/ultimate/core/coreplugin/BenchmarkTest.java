package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.lang.reflect.Field;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;

/***
 * 
 * @author Jeremi
 *
 */
public class BenchmarkTest {

	@BeforeClass
	public static void Setup() {
		//setup logging 
		Logger root = Logger.getRootLogger();
		if (!root.getAllAppenders().hasMoreElements()) {
			// No appenders means log4j is not initialized
			root.addAppender(new ConsoleAppender(new PatternLayout(PatternLayout.TTCC_CONVERSION_PATTERN)));
		}
		//TODO: decide how to make this testable
		//setup UltimateServices singleton: this may backfire hard, as many of UltimateServices methods depend on an actual application 
 		UltimateServices.createInstance(null);
	}

//	/**
//	 * Example of testing an private field. Methods are similar.
//	 */
//	@Test
//	// @Category(ExampleCategory.class)
//	public void testbenchmarkTestA() {
//
//		Benchmark b = new Benchmark();
//
//		Assert.assertEquals("'toString' should contain be empty", "",
//				b.toString());
//
//	}

//	@Test
//	// @Category(ExampleCategory.class)
//	public void benchmarkTestPrivateField() {
//
//		Field field;
//		try {
//			Benchmark benchmark_instance = new Benchmark();
//			benchmark_instance.start("testtitle");
//
//			field = Benchmark.class.getDeclaredField("m_Title");
//			field.setAccessible(true);
//			String field_value = (String) field.get(benchmark_instance);
//
//			Assert.assertEquals("testtitle", field_value);
//
//		} catch (Exception e) {
//			Assert.fail(e.getMessage());
//		}
//
//	}

	/*
	 * @Test
	 * 
	 * @Category(ExampleCategory.class) public void
	 * benchmarkTestPrivateFieldWithPrivateTester() throws
	 * PrivateInvocationException {
	 * 
	 * Benchmark b = new Benchmark(); b.start("eintitle");
	 * 
	 * Assert.assertEquals("title should be 'eintitle'", "eintitle", new
	 * PrivateTester<String>().getField(b, "m_Title") );
	 * 
	 * }
	 */

}
