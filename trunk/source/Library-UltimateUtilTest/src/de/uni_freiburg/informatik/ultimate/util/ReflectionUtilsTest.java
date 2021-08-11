/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Collections;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

public class ReflectionUtilsTest {

	private static final String INSTANCE_IS_NULL = "instance is null";

	@Test
	public void loadInterfaceImplementingClasses() {
		Set<Class<? extends ITestInterface>> classes = Collections.emptySet();
		try {
			classes = ReflectionUtil.getClassesImplementingInterfaceFromFolder(ITestInterface.class);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue(classes == null ? "[]" : classes.toString(),
				classes.contains(TestInterfaceImplementation.class));
	}

	@Test
	public void instantiateStaticInnerClass() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiateClass(TestInterfaceImplementationStatic.class);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue(INSTANCE_IS_NULL, instance != null);
	}

	@Test
	public void instantiateNonStaticInnerClass() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiateClass(TestInterfaceImplementation.class);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue(INSTANCE_IS_NULL, instance != null);
	}

	@Test
	public void instantiateWithParamsTwoInt() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiateClass(TestInterfaceImplManyConstructors.class, 1, 2, 3);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue(INSTANCE_IS_NULL, instance != null);
		Assert.assertTrue(INSTANCE_IS_NULL, "IntIntInt".equals(instance.doIt()));
	}

	@Test
	public void instantiateWithParamsOneObject() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiateClass(TestInterfaceImplManyConstructors.class, new Object());
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue(INSTANCE_IS_NULL, instance != null);
		Assert.assertTrue(INSTANCE_IS_NULL, "Object".equals(instance.doIt()));
	}

	@Test
	public void instantiateWithParamsOneNull() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiateClass(TestInterfaceImplManyConstructors.class, new Object[] { null });
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue(INSTANCE_IS_NULL, instance != null);
		Assert.assertTrue(INSTANCE_IS_NULL, "Object".equals(instance.doIt()));
	}

	public interface ITestInterface {
		public String doIt();
	}

	public class TestInterfaceImplementation implements ITestInterface {

		@Override
		public String doIt() {
			return "Doing it";
		}
	}

	public static class TestInterfaceImplementationStatic implements ITestInterface {

		@Override
		public String doIt() {
			return "Doing it statically";
		}
	}

	public static class TestInterfaceImplManyConstructors implements ITestInterface {

		private final String mMsg;

		public TestInterfaceImplManyConstructors(final Object x) {
			mMsg = "Object";
		}

		public TestInterfaceImplManyConstructors(final Object x, final int y) {
			mMsg = "ObjectInt";
		}

		public TestInterfaceImplManyConstructors(final int x, final int y) {
			mMsg = "IntInt";
		}

		public TestInterfaceImplManyConstructors(final int x, final int y, final int z) {
			mMsg = "IntIntInt";
		}

		@Override
		public String doIt() {
			return mMsg;
		}

	}
}
