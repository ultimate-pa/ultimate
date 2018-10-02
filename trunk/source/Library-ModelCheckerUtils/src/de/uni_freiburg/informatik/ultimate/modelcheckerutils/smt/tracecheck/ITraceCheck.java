/*
 * Copyright (C) 2016-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * An {@link ITraceCheck} is used to determine whether a trace satisfies a postcondition under a given precondition.
 *
 * A trace is specified as sequence of {@link IcfgEdge}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ITraceCheck {

	/**
	 * Returns
	 * <ul>
	 * <li>SAT if the trace does not fulfill its specification,
	 * <li>UNSAT if the trace does fulfill its specification,
	 * <li>UNKNOWN if it was not possible to determine if the trace fulfills its specification.
	 * </ul>
	 */
	LBool isCorrect();

	IPredicate getPrecondition();

	IPredicate getPostcondition();

	Map<Integer, IPredicate> getPendingContexts();

	boolean providesRcfgProgramExecution();

	/**
	 * Return the RcfgProgramExecution that has been computed by computeRcfgProgramExecution().
	 */
	IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution();

	IStatisticsDataProvider getTraceCheckBenchmark();

	/**
	 * If during a trace check a {@link ToolchainCanceledException} occurs, the {@link ITraceCheck} may catch this
	 * exception and perform cleanup. Users of {@link ITraceCheck} can then call this method to check whether such an
	 * exception occured and rethrow it if necessary.
	 *
	 * @return the {@link ToolchainCanceledException} that was thrown if the computation was cancelled. If the
	 *         computation was not cancelled, we return null.
	 * @deprecated DD: cleanup should happen in a finally block inside of ITraceCheck. If callers need to perform
	 *             cleanup, they themselves can add a finally block.
	 */
	@Deprecated
	ToolchainCanceledException getToolchainCanceledExpection();

	/**
	 * If the result of {@link #isCorrect()} is {@link LBool#UNKNOWN}m this method can be called to obtain more
	 * information about the result.
	 *
	 * @return A {@link TraceCheckReasonUnknown} instance.
	 */
	TraceCheckReasonUnknown getTraceCheckReasonUnknown();

	/**
	 * @return true iff trace check was successfully finished. Examples for a not successfully finished trace check are:
	 *         Crash of solver, Toolchain cancelled, etc.
	 */
	boolean wasTracecheckFinishedNormally();

}