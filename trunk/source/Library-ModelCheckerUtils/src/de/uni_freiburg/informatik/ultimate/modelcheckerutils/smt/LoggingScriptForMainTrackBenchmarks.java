/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;

public class LoggingScriptForMainTrackBenchmarks extends LoggingScriptForNonIncrementalBenchmarks {
	
	private int m_WrittenScriptCounter = 0;

	public LoggingScriptForMainTrackBenchmarks(Script script,
			String baseFilename, String directory) {
		super(script, baseFilename, directory);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		LBool sat = super.checkSat();
		if (sat == LBool.UNKNOWN) {
			File file = constructFile("_" + String.valueOf(m_WrittenScriptCounter));
			writeCommandStackToFile(file, m_CommandStack);
			m_WrittenScriptCounter++;
		}
		return sat;
	}
	
	

}
