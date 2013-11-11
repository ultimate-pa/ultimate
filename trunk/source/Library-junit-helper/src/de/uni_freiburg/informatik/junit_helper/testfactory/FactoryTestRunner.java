package de.uni_freiburg.informatik.junit_helper.testfactory;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.TestClass;

public class FactoryTestRunner extends BlockJUnit4ClassRunner {

	private ArrayList<FrameworkMethod> mTests;

	public FactoryTestRunner(Class<?> claaas) throws InitializationError {
		super(claaas);
		mTests = new ArrayList<FrameworkMethod>();
	}

	protected Collection<? extends FrameworkMethod> generateFactoryTests() {
		List<FrameworkFactoryTest> tests = new ArrayList<FrameworkFactoryTest>();
		TestClass classUnderTest = getTestClass();

		// create an instance of the current class
		Object currentInstance = null;
		try {
			currentInstance = classUnderTest.getOnlyConstructor().newInstance();
		} catch (InstantiationException | IllegalAccessException
				| IllegalArgumentException | InvocationTargetException e1) {
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
			} catch (IllegalAccessException | IllegalArgumentException
					| InvocationTargetException e) {
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
		// computeTestMethods returns all methods that are marked with @Test
		mTests.addAll(super.computeTestMethods());

		// generateFactoryTests collects all tests from invoking methods that
		// are marked with @TestFactory
		mTests.addAll(generateFactoryTests());
		return mTests;
	}

	@Override
	protected void validateInstanceMethods(List<Throwable> errors) {
		// this method is overriden to allow for "empty" test classes, i.e.
		// classes containing only methods with @TestFactory
		validatePublicVoidNoArgMethods(After.class, false, errors);
		validatePublicVoidNoArgMethods(Before.class, false, errors);
		validateTestMethods(errors);
	}

}
