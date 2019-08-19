/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.ISmtCommand;

public class LoggingScriptForUnsatCoreBenchmarks extends
		LoggingScriptForNonIncrementalBenchmarks {


	private LinkedList<ArrayList<ISmtCommand<?>>> mCommandStackAtLastGetUnsatCore;

	public LoggingScriptForUnsatCoreBenchmarks(final Script script,
			final String baseFilename, final String directory) {
		super(script, baseFilename, directory);
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		final Term[] result = super.getUnsatCore();
		mCommandStackAtLastGetUnsatCore = deepCopyOfCommandStack();
		return result;
	}

	@Override
	public void exit() {
		if (mCommandStackAtLastGetUnsatCore != null) {
			writeCommandStackToFile(constructFile("_UnsatCore"), mCommandStackAtLastGetUnsatCore);
		}
		super.exit();
	}





}
