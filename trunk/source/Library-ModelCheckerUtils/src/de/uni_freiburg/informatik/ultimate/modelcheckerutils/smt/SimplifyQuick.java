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
/*
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE ModelCheckerUtils Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;

/**
 * Variant of {@link SimplifyDDA} that uses SMTInterpol's "quick check". The
 * "quick check" is much faster but returns UNKNOWN much more often. Here, we
 * always start a new instance of SMTInterpol. The input is transferred to this
 * new instance such that each non-boolean subterm is replaced by a fresh
 * boolean constant. This ensures that SMTInterpol is able to handle the term.
 * 
 * @author Matthias Heizmann
 *
 */
public class SimplifyQuick {

	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private IToolchainStorage mStorage;
	private static final int TIMOUT_IN_SECONDS = 10;

	public SimplifyQuick(Script script, IUltimateServiceProvider services) {
		mScript = script;
		mServices = services;
	}

	public Term getSimplifiedTerm(Term inputTerm) throws SMTLIBException {

		Settings settings = new SolverBuilder.Settings(false, "", TIMOUT_IN_SECONDS * 1000, null, false, null, null);
		Script simplificationScript = SolverBuilder.buildScript(mServices, mStorage, settings);
		simplificationScript.setLogic(Logics.CORE);
		TermTransferrer towards = new TermTransferrerBooleanCore(simplificationScript);
		Term foreign = towards.transform(inputTerm);

		simplificationScript.setOption(":check-type", "QUICK");
		SimplifyDDAWithTimeout dda = new SimplifyDDAWithTimeout(simplificationScript, false, mServices);
		Term foreignsimplified = dda.getSimplifiedTerm(foreign);
		// simplificationScript.setOption(":check-type", "FULL");

		TermTransferrer back = new TermTransferrer(mScript, towards.getBacktranferMapping());
		Term simplified = back.transform(foreignsimplified);
		simplificationScript.exit();

		return simplified;
	}
}
