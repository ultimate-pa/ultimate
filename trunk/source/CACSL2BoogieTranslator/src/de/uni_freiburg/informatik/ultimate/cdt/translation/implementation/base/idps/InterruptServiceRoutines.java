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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;

/**
 * Simple struct that stores Boogie procedures associated to interrupt-service-routines used for the IDP to TBP
 * translation
 */
public class InterruptServiceRoutines {
	// Map IRQ to ISR Name
	private Map<Integer, Procedure> mISRMap;

	// Names of the corresponding functions

	private Map<Integer, Procedure> mRequestEnable;
	private Map<Integer, Procedure> mRequestDisable;
	private Procedure mSetPriority;
	private Procedure mGetPriority;
	private Procedure mMainProcedure;

	public InterruptServiceRoutines(final Map<Integer, Procedure> isrMap, final Map<Integer, Procedure> reqEnable,
			final Map<Integer, Procedure> reqDisable, final Procedure setPrio, final Procedure getPrio,
			final Procedure mainProcedure) {
		mISRMap = isrMap;
		mRequestEnable = reqEnable;
		mRequestDisable = reqDisable;
		mSetPriority = setPrio;
		mGetPriority = getPrio;
		mMainProcedure = mainProcedure;
	}

	public Map<Integer, Procedure> getISRMap() {
		return mISRMap;
	}

	public Map<Integer, Procedure> getRequestEnable() {
		return mRequestEnable;
	}

	public Map<Integer, Procedure> getRequestDisable() {
		return mRequestDisable;
	}

	public Procedure getSetPriority() {
		return mSetPriority;
	}

	public Procedure getGetPriority() {
		return mGetPriority;
	}

	public Procedure getMainProcedure() {
		return mMainProcedure;
	}

	public void setISRMap(final Map<Integer, Procedure> isrMap) {
		mISRMap = isrMap;
	}

	public void setRequestEnable(final Map<Integer, Procedure> reqEnable) {
		mRequestEnable = reqEnable;
	}

	public void setRequestDisable(final Map<Integer, Procedure> reqDisable) {
		mRequestDisable = reqDisable;
	}

	public void setSetPriority(final Procedure setPrio) {
		mSetPriority = setPrio;
	}

	public void setGetPriority(final Procedure getPrio) {
		mGetPriority = getPrio;
	}

	public void setMainProcedure(final Procedure mainProcedure) {
		mMainProcedure = mainProcedure;
	}
}
