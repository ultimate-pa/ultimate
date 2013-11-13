package de.uni_freiburg.informatik.junit_helper.testfactory;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.TestClass;
import static org.junit.Assert.*;

public class FactoryTestRunner extends BlockJUnit4ClassRunner {

	private ArrayList<FrameworkMethod> mTests;

	public FactoryTestRunner(Class<?> claaas) throws InitializationError {
		super(claaas);
	}

	protected Collection<? extends FrameworkMethod> generateFactoryTests() {
		System.out.println(this + ".generateFactoryTests()");
		List<FrameworkFactoryTest> tests = new ArrayList<FrameworkFactoryTest>();
		TestClass classUnderTest = getTestClass();

		// create an instance of the current class
		Object currentInstance = null;
		try {
			currentInstance = classUnderTest.getOnlyConstructor().newInstance();
		} catch (Exception e1) {
			e1.printStackTrace();
			return tests;
		}

		// Find all methods in the current class marked with @TestFactory.
		for (FrameworkMethod method : classUnderTest
				.getAnnotatedMethods(TestFactory.class)) {

			// Execute the current @TestFactory method
			Object factoryMethod;
			try {

				factoryMethod = method.getMethod().invoke(currentInstance);
			} catch (Exception e) {
				e.printStackTrace();
				continue;
			}

			if (factoryMethod.getClass().isArray()) {
				// Did the factory return an array? If so, make it a list.
				factoryMethod = Arrays.asList((Object[]) factoryMethod);
			}

			if (!(factoryMethod instanceof Iterable<?>)) {
				// Did the factory return a single object? If so, put it in a
				// list.
				factoryMethod = Collections.singletonList(factoryMethod);
			}

			// For each object returned by the factory.
			for (Object instance : (Iterable<?>) factoryMethod) {
				// Find any methods marked with @FactoryTest and add them to the
				// return list

				for (FrameworkMethod m : new TestClass(instance.getClass())
						.getAnnotatedMethods(FactoryTestMethod.class)) {
					tests.add(new FrameworkFactoryTest(m.getMethod(), instance,
							instance.toString()));
				}
			}
		}

		return tests;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see org.junit.runners.BlockJUnit4ClassRunner#computeTestMethods()
	 */
	@Override
	protected List<FrameworkMethod> computeTestMethods() {
		if (mTests == null) {
			mTests = new ArrayList<FrameworkMethod>();
		}
		if (mTests.size() == 0) {
			// generateFactoryTests collects all tests from invoking methods
			// that
			// are marked with @TestFactory
			mTests.addAll(generateFactoryTests());

			if (mTests.size() == 0) {
				// ok, so no factory tests were generated; in this case, we add
				// our own factory test that will a) always fail and b) report
				// to the user that no dynamic test was generated and that this
				// is failure
				try {
					final String errorMsg = getTestClass().getName()
							+ " did not return any dynamic tests";
					mTests.add(new FrameworkFactoryTest(FailingTest.class
							.getMethod("NoFactoryTestMethod"),
							new FailingTest(), errorMsg));
				} catch (Exception e) {
					// this reflection is always safe
				}

			}

			// computeTestMethods returns all methods that are marked with @Test
			mTests.addAll(super.computeTestMethods());
		}
		return mTests;
	}

	public class FailingTest {
		public void NoFactoryTestMethod() {
			fail("TestSuite run with custom runner FactoryTestRunner must return at least one dynamic generated test through their @TestFactory methods");
		}
	}
}
