/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE UnitTest Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.util;

import java.io.File;
import java.lang.management.ManagementFactory;
import java.lang.reflect.Method;

import javax.management.MBeanServer;

public class HeapDumper {
	// This is the name of the HotSpot Diagnostic MBean
	private static final String HOTSPOT_BEAN_NAME = "com.sun.management:type=HotSpotDiagnostic";

	// field to store the hotspot diagnostic MBean
	private static volatile Object sHotspotMBean;

	/**
	 * Call this method from your application whenever you want to dump a heap
	 * snapshot into a file.
	 * 
	 * @param fileName
	 *            name of the heap dump file
	 * @param live
	 *            flag that tells whether to dump only the live objects
	 */
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static void dumpHeap(String fileName, boolean live) {
		final Object hotspotMBean = getHotspotMBean();
		if (hotspotMBean == null) {
			return;
		}
		try {
			// invoke per reflection to avoid explicit dependeny resolution.
			// Will fail.
			final Class clazz = Class.forName("com.sun.management.HotSpotDiagnosticMXBean");
			final Method m = clazz.getMethod("dumpHeap", String.class, boolean.class);
			m.invoke(getHotspotMBean(), prepareFilename(fileName), live);
		} catch (final RuntimeException re) {
			throw re;
		} catch (final Exception exp) {
			throw new RuntimeException(exp);
		}
	}

	private static String prepareFilename(String filename) {
		final File f = new File(filename + de.uni_freiburg.informatik.ultimate.util.CoreUtil.getCurrentDateTimeAsString() + ".hprof");
		return f.getAbsolutePath();
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static Object getHotspotMBean() {
		if (sHotspotMBean == null) {
			synchronized (HeapDumper.class) {
				if (sHotspotMBean == null) {
					// initialize the hotspot diagnostic MBean field
					try {
						final Class clazz = Class.forName("com.sun.management.HotSpotDiagnosticMXBean");
						final MBeanServer server = ManagementFactory.getPlatformMBeanServer();
						final Object bean = ManagementFactory.newPlatformMXBeanProxy(server, HOTSPOT_BEAN_NAME, clazz);
						sHotspotMBean = bean;
					} catch (final RuntimeException re) {
						throw re;
					} catch (final Exception exp) {
						throw new RuntimeException(exp);
					}
				}
			}
		}
		return sHotspotMBean;
	}

}
