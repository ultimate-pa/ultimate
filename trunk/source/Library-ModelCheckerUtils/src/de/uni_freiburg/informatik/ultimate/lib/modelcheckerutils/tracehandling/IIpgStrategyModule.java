/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <T>
 * @param <LETTER>
 */
public interface IIpgStrategyModule<T extends IInterpolantGenerator<LETTER>, LETTER extends IAction> {

	InterpolantComputationStatus getInterpolantComputationStatus();

	Collection<QualifiedTracePredicates> getPerfectInterpolantSequences();

	Collection<QualifiedTracePredicates> getImperfectInterpolantSequences();

	void aggregateStatistics(final RefinementEngineStatisticsGenerator statistics);

	T getOrConstruct();

	/**
	 * @see IRefinementEngine#getHoareTripleChecker()
	 * @see IRefinementStrategy#getHoareTripleChecker(IRefinementEngine)
	 * @return
	 */
	IHoareTripleChecker getHoareTripleChecker();

	/**
	 * @see IRefinementEngine#getPredicateUnifier()()
	 * @see IRefinementStrategy#getPredicateUnifier(IRefinementEngine)
	 * @return A predicate unifier that is required by this {@link IIpgStrategyModule} or null if no particular
	 *         predicate unifier is required.
	 */
	IPredicateUnifier getPredicateUnifier();
}
