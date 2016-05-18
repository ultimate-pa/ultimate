/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class MonolithicHoareTripleChecker implements IHoareTripleChecker {
	
	private final SmtManager m_SmtManager;
	private HoareTripleCheckerStatisticsGenerator m_HoareTripleCheckerStatistics;
	
	

	public MonolithicHoareTripleChecker(SmtManager smtManager) {
		super();
		m_SmtManager = smtManager;
		m_HoareTripleCheckerStatistics = new HoareTripleCheckerStatisticsGenerator();
	}

	@Override
	public Validity checkInternal(IPredicate pre, IInternalAction act, IPredicate succ) {
		m_HoareTripleCheckerStatistics.continueEdgeCheckerTime();
		Validity result = IHoareTripleChecker.lbool2validity(m_SmtManager.isInductive(pre, act, succ));
		m_HoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			m_HoareTripleCheckerStatistics.getSolverCounterSat().incIn();
			break;
		case UNKNOWN:
			m_HoareTripleCheckerStatistics.getSolverCounterUnknown().incIn();
			break;
		case VALID:
			m_HoareTripleCheckerStatistics.getSolverCounterUnsat().incIn();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public Validity checkCall(IPredicate pre, ICallAction act, IPredicate succ) {
		m_HoareTripleCheckerStatistics.continueEdgeCheckerTime();
		Validity result =  IHoareTripleChecker.lbool2validity(m_SmtManager.isInductiveCall(pre, (Call) act, succ));
		m_HoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			m_HoareTripleCheckerStatistics.getSolverCounterSat().incCa();
			break;
		case UNKNOWN:
			m_HoareTripleCheckerStatistics.getSolverCounterUnknown().incCa();
			break;
		case VALID:
			m_HoareTripleCheckerStatistics.getSolverCounterUnsat().incCa();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			IReturnAction act, IPredicate succ) {
		m_HoareTripleCheckerStatistics.continueEdgeCheckerTime();
		Validity result =  IHoareTripleChecker.lbool2validity(m_SmtManager.isInductiveReturn(preLin, preHier, (Return) act, succ));
		m_HoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			m_HoareTripleCheckerStatistics.getSolverCounterSat().incRe();
			break;
		case UNKNOWN:
			m_HoareTripleCheckerStatistics.getSolverCounterUnknown().incRe();
			break;
		case VALID:
			m_HoareTripleCheckerStatistics.getSolverCounterUnsat().incRe();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return m_HoareTripleCheckerStatistics;
	}

	@Override
	public void releaseLock() {
		// do nothing, since objects of this class do not lock the solver
	}
	
	

}
