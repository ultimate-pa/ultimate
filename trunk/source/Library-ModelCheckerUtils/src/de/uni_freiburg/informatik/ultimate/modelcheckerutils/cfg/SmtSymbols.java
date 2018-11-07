/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SmtSymbols {

	public static final int HARDCODED_SERIALNUMBER_FOR_AXIOMS = 0;

	private final IPredicate mAxioms;

	/**
	 * Create an empty {@link SmtSymbols} instance.
	 */
	public SmtSymbols(final Script script) {
		this(script.term("true"), new String[0]);
	}

	public SmtSymbols(final Term axioms, final String[] defininingProcedures) {
		this(new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, defininingProcedures, axioms, Collections.emptySet(),
				axioms));
	}

	public SmtSymbols(final IPredicate axioms) {
		assert axioms.getClosedFormula() == axioms.getFormula() : "Axioms are not closed";
		assert axioms.getFormula().getFreeVars().length == 0 : "Axioms are not closed";
		assert axioms.getProcedures() != null;
		mAxioms = axioms;
	}

	public SmtSymbols addAxiom(final Script script, final Term additionalAxioms) {
		final Term newAxioms = SmtUtils.and(script, mAxioms.getClosedFormula(), additionalAxioms);
		final IPredicate newAxiomsPred = new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, new String[0],
				additionalAxioms, Collections.emptySet(), newAxioms);
		return new SmtSymbols(newAxiomsPred);
	}

	/**
	 * Assert all symbols defined by this SmtSymbols in a fresh script.
	 *
	 * @param script
	 *            the new solver.
	 */
	public void transferSymbols(final Script script) {
		final TermTransferrer tt = new TermTransferrer(script);
		final LBool quickCheckAxioms = script.assertTerm(tt.transform(mAxioms.getClosedFormula()));
		assert quickCheckAxioms != LBool.UNSAT : "Axioms are inconsistent";
	}

	public void classify(final TermClassifier cs) {
		cs.checkTerm(mAxioms.getFormula());
	}

	public IPredicate getAxioms() {
		return mAxioms;
	}

}
