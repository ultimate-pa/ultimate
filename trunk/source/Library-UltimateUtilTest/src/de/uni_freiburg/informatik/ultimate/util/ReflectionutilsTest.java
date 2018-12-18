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

public class ReflectionutilsTest {

	@Test
	public void loadInterfaceImplementingClasses() {
		Set<Class<?>> classes = Collections.emptySet();
		try {
			classes = ReflectionUtil.getClassesImplementingInterfaceFromFolder(ITestInterface.class);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue("", classes.contains(TestInterfaceImplementation.class));
	}

	@Test
	public void instantiateStaticInnerClass() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiate(TestInterfaceImplementationStatic.class);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue("", instance != null);
	}

	@Test
	public void instantiateNonStaticInnerClass() {
		ITestInterface instance = null;
		try {
			instance = ReflectionUtil.instantiate(TestInterfaceImplementation.class);
		} catch (final Throwable e) {
			e.printStackTrace();
		}
		Assert.assertTrue("", instance != null);
	}

	public interface ITestInterface {
		public void doIt();
	}

	public class TestInterfaceImplementation implements ITestInterface {

		@Override
		public void doIt() {
			System.out.println("Doing it");
		}
	}

	public static class TestInterfaceImplementationStatic implements ITestInterface {

		@Override
		public void doIt() {
			System.out.println("Doing it");
		}
	}
}
