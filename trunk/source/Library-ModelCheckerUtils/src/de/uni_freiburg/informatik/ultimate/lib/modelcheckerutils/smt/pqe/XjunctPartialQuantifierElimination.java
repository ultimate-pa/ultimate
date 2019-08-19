/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Abstract superclass for our partial quantifier elimination for Xjuncts of a XNF.
 * @author Matthias Heizmann
 */

public abstract class XjunctPartialQuantifierElimination {
	protected final Script mScript;
	protected final ManagedScript mMgdScript;
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;


	public XjunctPartialQuantifierElimination(final ManagedScript script,
			final IUltimateServiceProvider services) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mMgdScript = script;
		mScript = script.getScript();
	}
	public abstract String getName();
	public abstract String getAcronym();
	/**
	 * Returns true if the returned result is again an Xjunction (conjunction
	 * for existential quantifier, disjunction for universal quantifier).
	 * E.g., if we apply TIR for existential quantification to a conjunction,
	 * we may obtain a (large) disjunction of conjunction.
	 */
	public abstract boolean resultIsXjunction();

	/**
	 * Try to remove {@link TermVariable}s from the set <code>eliminatees</code>
	 * such that the following holds.
	 * <p>
	 * If the quantifier is an existential (resp. universal) quantifier this method
	 * returns an array of {@link Term}s <code>result</code> such that
	 * <code>∃ eliminatees. ⋀ dualJuncts</code> is equivalent to
	 * <code>∃ eliminatees'. ⋀ result</code> (resp.
	 * <code>∀ eliminatees. ⋁ dualJuncts</code> is equivalent to
	 * <code>∀ eliminatees'. ⋁ result</code>) where eliminatees' refers to the
	 * content of the set after this method was executed.
	 * <p>
	 * Which and how many variables from the set <code>eliminatees</code> can be
	 * removed depends on the quantifier elimination algorithm that implements this
	 * method.
	 * <p>
	 * Every variable that was successfully eliminated is removed from the set.
	 * However, due to formula simplifications some variables might get removed
	 * accidentally. Hence, there might be variables that are not removed from
	 * the eliminatees set but do not occur in the resulting terms.
	 */
	public abstract Term[] tryToEliminate(int quantifier, Term[] dualJuncts, Set<TermVariable> eliminatees);

}
