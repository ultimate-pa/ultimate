/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.lang.management.ManagementFactory;
import java.lang.management.RuntimeMXBean;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class VMUtils {

	public static String getVMInfos() {
		final RuntimeMXBean runtimeMxBean = ManagementFactory.getRuntimeMXBean();
		final String br = System.getProperty("line.separator");
		final StringBuilder sb = new StringBuilder();
		sb.append("VM Information is:").append(br);
		sb.append(" * Name: ").append(runtimeMxBean.getName()).append(br);
		try {
			sb.append(" * VM name: ").append(runtimeMxBean.getVmName()).append(br);
			sb.append(" * VM vendor: ").append(runtimeMxBean.getVmVendor()).append(br);
			sb.append(" * VM version: ").append(runtimeMxBean.getVmVersion()).append(br);
			sb.append(" * VM arguments: ").append(CoreUtil.join(runtimeMxBean.getInputArguments(), ",")).append(br);
			sb.append(" * Spec name: ").append(runtimeMxBean.getSpecName()).append(br);
			sb.append(" * Spec vendor: ").append(runtimeMxBean.getSpecVendor()).append(br);
			sb.append(" * Spec version: ").append(runtimeMxBean.getSpecVersion()).append(br);
			sb.append(" * Management spec version: ").append(runtimeMxBean.getManagementSpecVersion()).append(br);
			sb.append(" * Library : ").append(runtimeMxBean.getLibraryPath()).append(br);
		} catch (final Error err) {
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
