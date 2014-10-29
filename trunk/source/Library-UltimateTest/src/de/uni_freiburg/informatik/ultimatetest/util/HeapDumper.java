package de.uni_freiburg.informatik.ultimatetest.util;

import javax.management.MBeanServer;

import java.io.File;
import java.lang.management.ManagementFactory;
import java.lang.reflect.Method;

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
		Object hotspotMBean = getHotspotMBean();
		if (hotspotMBean == null) {
			return;
		}
		try {
			// invoke per reflection to avoid explicit dependeny resolution.
			// Will fail.
			Class clazz = Class.forName("com.sun.management.HotSpotDiagnosticMXBean");
			Method m = clazz.getMethod("dumpHeap", String.class, boolean.class);
			m.invoke(getHotspotMBean(), prepareFilename(fileName), live);
		} catch (RuntimeException re) {
			throw re;
		} catch (Exception exp) {
			throw new RuntimeException(exp);
		}
	}

	private static String prepareFilename(String filename) {
		File f = new File(filename + de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getCurrentDateTimeAsString() + ".hprof");
		return f.getAbsolutePath();
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static Object getHotspotMBean() {
		if (sHotspotMBean == null) {
			synchronized (HeapDumper.class) {
				if (sHotspotMBean == null) {
					// initialize the hotspot diagnostic MBean field
					try {
						Class clazz = Class.forName("com.sun.management.HotSpotDiagnosticMXBean");
						MBeanServer server = ManagementFactory.getPlatformMBeanServer();
						Object bean = ManagementFactory.newPlatformMXBeanProxy(server, HOTSPOT_BEAN_NAME, clazz);
						sHotspotMBean = bean;
					} catch (RuntimeException re) {
						throw re;
					} catch (Exception exp) {
						throw new RuntimeException(exp);
					}
				}
			}
		}
		return sHotspotMBean;
	}

}