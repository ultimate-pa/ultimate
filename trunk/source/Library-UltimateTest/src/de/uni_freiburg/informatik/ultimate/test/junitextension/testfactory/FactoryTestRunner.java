/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE JUnit Helper Library.
 * 
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory;

import static org.junit.Assert.fail;

import java.lang.annotation.Annotation;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.junit.AfterClass;
import org.junit.internal.runners.statements.RunAfters;
import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.Statement;
import org.junit.runners.model.TestClass;

/**
 * {@link FactoryTestRunner} is used through JUnit to instantiate Ultimate's dynamic tests. JUnit instantiates this
 * runner for each class marked with <code>@RunWith(FactoryTestRunner.class)</code> (see {@link FactoryTestRunner}). The
 * runner then instantiates this class and executes the classes' methods marked with <code>@TestFactory</code> (see
 * {@link TestFactory}. On the resulting instances, all methods marked with <code>@FactoryTestMethod</code> (see
 * {@link FactoryTestMethod}) are then executed as single test.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class FactoryTestRunner extends BlockJUnit4ClassRunner {

	private List<FrameworkMethod> mTests;
	private final String mTestSuiteName;

	private Object mTestSuiteInstance;

	public FactoryTestRunner(final Class<?> claaas) throws InitializationError {
		super(claaas);
		mTestSuiteName = claaas.getSimpleName();
	}

	protected Collection<? extends FrameworkMethod> generateFactoryTests() {
		final List<FrameworkFactoryTest> tests = new ArrayList<>();
		final TestClass classUnderTest = getTestClass();

		// create an instance of the current class
		final Object currentInstance;
		if (mTestSuiteInstance == null) {
			try {
				currentInstance = classUnderTest.getOnlyConstructor().newInstance();

			} catch (final Throwable e1) {
				e1.printStackTrace();
				return tests;
			}
			mTestSuiteInstance = currentInstance;
		} else {
			currentInstance = mTestSuiteInstance;
		}

		// Find all methods in the current class marked with @TestFactory.
		for (final FrameworkMethod method : classUnderTest.getAnnotatedMethods(TestFactory.class)) {

			// Execute the current @TestFactory method
			Object factoryMethodResult;
			try {
				factoryMethodResult = method.getMethod().invoke(currentInstance);
			} catch (final InvocationTargetException ex) {
				System.err.println("Exception during invocation of test method:");
				final Throwable cause = ex.getCause();
				if (cause != null) {
					cause.printStackTrace();
				}
				continue;
			} catch (final Exception e) {
				e.printStackTrace();
				continue;
			}

			if (factoryMethodResult.getClass().isArray()) {
				// Did the factory return an array? If so, make it a list.
				factoryMethodResult = Arrays.asList((Object[]) factoryMethodResult);
			}

			if (!(factoryMethodResult instanceof Iterable<?>)) {
				// Did the factory return a single object? If so, put it in a
				// list.
				factoryMethodResult = Collections.singletonList(factoryMethodResult);
			}

			// For each object returned by the factory.
			for (final Object instance : (Iterable<?>) factoryMethodResult) {
				// Find any methods marked with @FactoryTest and add them to the
				// return list

				for (final FrameworkMethod m : new TestClass(instance.getClass())
						.getAnnotatedMethods(FactoryTestMethod.class)) {
					tests.add(new FrameworkFactoryTest(m.getMethod(), instance, instance.toString()));
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
			mTests = new ArrayList<>();
		}
		if (mTests.isEmpty()) {
			// generateFactoryTests collects all tests from invoking methods
			// that
			// are marked with @TestFactory
			mTests.addAll(generateFactoryTests());

			if (mTests.isEmpty()) {
				// ok, so no factory tests were generated; in this case, we add
				// our own factory test that will a) always fail and b) report
				// to the user that no dynamic test was generated and that this
				// is failure
				try {
					final String errorMsg = getTestClass().getName() + " did not return any dynamic tests";
					mTests.add(new FrameworkFactoryTest(FailingTest.class.getMethod("NoFactoryTestMethod"),
							new FailingTest(), errorMsg));
				} catch (final Exception e) {
					// this reflection is always safe
				}

			}

			// computeTestMethods returns all methods that are marked with @Test
			mTests.addAll(super.computeTestMethods());
		}
		return mTests;
	}

	@Override
	protected Object createTest() throws Exception {
		return mTestSuiteInstance;
	}

	@Override
	protected String getName() {
		return mTestSuiteName;
	}

	@Override
	protected void validatePublicVoidNoArgMethods(final Class<? extends Annotation> arg0, final boolean arg1,
			final List<Throwable> arg2) {
		return;
	}

	@SuppressWarnings("restriction")
	@Override
	protected Statement withAfterClasses(final Statement statement) {
		// enabling non-static after class methods
		final List<FrameworkMethod> afters = getTestClass().getAnnotatedMethods(AfterClass.class);
		return afters.isEmpty() ? statement : new RunAfters(statement, afters, mTestSuiteInstance);
	}

	public class FailingTest {
		public void NoFactoryTestMethod() {
			fail("TestSuite run with custom runner FactoryTestRunner must return at least one dynamic generated test through their @TestFactory methods");
		}
	}
}
