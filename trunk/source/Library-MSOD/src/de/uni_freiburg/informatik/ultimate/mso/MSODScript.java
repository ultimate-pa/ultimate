/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSOD Library package.
 *
 * The ULTIMATE MSOD Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSOD Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSOD Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSOD Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSOD Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.mso.MSODSolver.MSODLogic;

/**
 * Solver for Monadic Second Order Difference Logic Formulas
 *
 * TODO Check inputs.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODScript extends NoopScript {
	private final AutomataLibraryServices mAutomataLibrarayServices;
	private final MSODSolver mMSODSolver;
	private final ILogger mLogger;
	private Term mAssertionTerm;
	private Map<Term, Term> mModel;

	public MSODScript(final IUltimateServiceProvider services, final ILogger logger, final MSODLogic logic) {
		mAutomataLibrarayServices = new AutomataLibraryServices(services);
		mLogger = logger;
		mMSODSolver = new MSODSolver(services, this, logger, logic);
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mAssertionTerm = mAssertionTerm == null ? term : term("and", new Term[] { mAssertionTerm, term });
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		mLogger.info("Input term: " + mAssertionTerm);

		try {
			mModel = mMSODSolver.getResult(this, mLogger, mAutomataLibrarayServices, mAssertionTerm);

			if (mModel != null) {
				mLogger.info("SAT");
				mModel.entrySet().forEach(e -> mLogger.info(e.getKey() + ": " + e.getValue()));
				return LBool.SAT;
			}

		} catch (final Exception e) {
			mLogger.error(e);
			return LBool.UNKNOWN;
		}

		mLogger.info("UNSAT");
		return LBool.UNSAT;
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException {
		final Map<Term, Term> result = new HashMap<>();

		if (mModel == null) {
			return result;
		}

		for (final Term term : terms) {
			final Term value = mModel.get(term);

			if (value != null) {
				result.put(term, value);
			}
		}

		return result;
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}
}
