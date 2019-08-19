/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;

/**
 * Adds thread instances to an ICFG
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ThreadInstance {

	private final String mThreadInstanceName;
	private final String mThreadTemplateName;

	private final IProgramNonOldVar[] mIdVars;
	private final IProgramNonOldVar mInUseVar;

	private IcfgLocation mErrorLocation;

	public ThreadInstance(final String threadInstanceName, final String threadTemplateName, final IProgramNonOldVar[] idVars,
			final IProgramNonOldVar inUseVar, final IcfgLocation errorLocation) {
		super();
		mThreadInstanceName = threadInstanceName;
		mThreadTemplateName = threadTemplateName;
		mIdVars = idVars;
		mInUseVar = inUseVar;
		mErrorLocation = errorLocation;
	}

	public String getThreadInstanceName() {
		return mThreadInstanceName;
	}

	public String getThreadTemplateName() {
		return mThreadTemplateName;
	}

	public IProgramNonOldVar[] getIdVars() {
		return mIdVars;
	}

	public IProgramNonOldVar getInUseVar() {
		return mInUseVar;
	}

	public IcfgLocation getErrorLocation() {
		return mErrorLocation;
	}

	public void setErrorLocation(final IcfgLocation errorLocation) {
		mErrorLocation = errorLocation;
	}






}
