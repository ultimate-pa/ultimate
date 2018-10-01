/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * Checks a trace for feasibility and, if infeasible, constructs a proof of infeasibility.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            The type of the infeasibility proof, e.g., an interpolant automaton or a set of Hoare triples.
 */
public interface IRefinementEngine<T> {
	/**
	 * @return Feasibility status of the counterexample trace.
	 */
	LBool getCounterexampleFeasibility();

	/**
	 * This method may only be called if {@link #getCounterexampleFeasibility()} returns {@code UNSAT}.
	 *
	 * @return Proof of infeasibility.
	 */
	T getInfeasibilityProof();

	/**
	 * @return Predicate unifier.
	 */
	IPredicateUnifier getPredicateUnifier();

	boolean providesICfgProgramExecution();

	/**
	 * @return RCFG program execution.
	 */
	IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getIcfgProgramExecution();

	/**
	 * Does sometimes return a Hoare triple checker. TODO: Find out under which conditions a Hoare triple checker is
	 * returned.
	 */
	IHoareTripleChecker getHoareTripleChecker();

	boolean somePerfectSequenceFound();
}
