/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import java.util.Map;

/**
 * Simple struct that contains information about the interrupt-service-routines in program. Names of the ISR related
 * functions are stored as Strings.
 */
public class ISRInfo {
	// Map IRQ to ISR Name
	private Map<Integer, String> mISRMap;

	// Names of the corresponding functions

	private String mRequestEnable;
	private String mRequestDisable;
	private String mSetPriority;
	private String mGetPriority;

	public ISRInfo(final Map<Integer, String> isrMap, final String reqEnable, final String reqDisable,
			final String setPrio, final String getPrio) {
		mISRMap = isrMap;
		mRequestEnable = reqEnable;
		mRequestDisable = reqDisable;
		mSetPriority = setPrio;
		mGetPriority = getPrio;
	}

	public Map<Integer, String> getISRMap() {
		return mISRMap;
	}

	public String getRequestEnable() {
		return mRequestEnable;
	}

	public String getRequestDisable() {
		return mRequestDisable;
	}

	public String getSetPriority() {
		return mSetPriority;
	}

	public String getGetPriority() {
		return mGetPriority;
	}

	public void setISRMap(final Map<Integer, String> isrMap) {
		mISRMap = isrMap;
	}

	public void setRequestEnable(final String reqEnable) {
		mRequestEnable = reqEnable;
	}

	public void setRequestDisable(final String reqDisable) {
		mRequestDisable = reqDisable;
	}

	public void setSetPriority(final String setPrio) {
		mSetPriority = setPrio;
	}

	public void setGetPriority(final String getPrio) {
		mGetPriority = getPrio;
	}
}
