/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.services.model;

import java.io.File;
import org.apache.log4j.Logger;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @deprecated We do not use preludes anymore, but various controller still
 *             incorporate this.
 */
@Deprecated
public class PreludeProvider {

	private File mPrelude;

	public PreludeProvider(String preludefile, Logger logger) {
		// get the logger of the core
		if (preludefile != null) {
			File foo = new File(preludefile);
			// prelude file must exist and must be readable
			if (!foo.exists()) {
				logger.error("Prelude file " + preludefile
						+ " doesn't exist! It will be ignored when processing the toolchain!");
				mPrelude = null;
			} else {
				if (!foo.canRead()) {
					logger.error("Prelude file " + preludefile
							+ " is not readable! It will be ignored when processing the toolchain!");
					mPrelude = null;
				} else {
					this.mPrelude = foo;
				}
			}
		} else {
			this.mPrelude = null;
		}
	}

	public File getPreludeFile() {
		return this.mPrelude;
	}

}
