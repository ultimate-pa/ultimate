package de.uni_freiburg.informatik.ultimate.util;

import java.lang.management.ManagementFactory;
import java.lang.management.RuntimeMXBean;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class VMUtils {

	public static String getVMInfos() {
		RuntimeMXBean runtimeMxBean = ManagementFactory.getRuntimeMXBean();
		String br = System.getProperty("line.separator");
		StringBuilder sb = new StringBuilder();
		sb.append("VM Information is:").append(br);
		sb.append(" * Name: ").append(runtimeMxBean.getName()).append(br);
		try {
			sb.append(" * VM name: ").append(runtimeMxBean.getVmName()).append(br);
			sb.append(" * VM vendor: ").append(runtimeMxBean.getVmVendor()).append(br);
			sb.append(" * VM version: ").append(runtimeMxBean.getVmVersion()).append(br);
			sb.append(" * VM arguments: ").append(Utils.join(runtimeMxBean.getInputArguments(), ",")).append(br);
			sb.append(" * Spec name: ").append(runtimeMxBean.getSpecName()).append(br);
			sb.append(" * Spec vendor: ").append(runtimeMxBean.getSpecVendor()).append(br);
			sb.append(" * Spec version: ").append(runtimeMxBean.getSpecVersion()).append(br);
			sb.append(" * Management spec version: ").append(runtimeMxBean.getManagementSpecVersion()).append(br);
			sb.append(" * Library : ").append(runtimeMxBean.getLibraryPath()).append(br);
		} catch (Error err) {
			sb.append("Error accessing VM information: ").append(err).append(br);
		}
		return sb.delete(sb.length() - br.length(), sb.length()).toString();
	}

	public static boolean areAssertionsEnabled() {
		boolean rtr = false;
		assert rtr = true;
		return rtr;
	}
}
