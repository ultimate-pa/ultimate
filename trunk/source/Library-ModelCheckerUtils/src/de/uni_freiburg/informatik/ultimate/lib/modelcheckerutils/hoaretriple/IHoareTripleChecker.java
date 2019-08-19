/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript.ILockHolderWithVoluntaryLockRelease;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;

/**
 * Object that implement this interface check if Hoare Triples are valid. Hoare triples that we check are of the form {
 * P } act { Q } where P and Q are given by IPredicates, act has to be a single action. Note that for return statements
 * we have to check a quadruple
 *
 * @author Matthias Heizmann
 *
 */
public interface IHoareTripleChecker extends ILockHolderWithVoluntaryLockRelease {

	/**
	 * Hoare Triple Truth Value. This is the result of a Hoare triple check.
	 */
	public enum Validity {
		VALID, INVALID, UNKNOWN, NOT_CHECKED
	}

	/**
	 * Check if the Hoare triple {pre} act {succ} is valid for an internal action act. Internal transition means that
	 * the program is in the same procedure before and after the action act was executed.
	 */
	Validity checkInternal(IPredicate pre, IInternalAction act, IPredicate succ);

	/**
	 * Check if the Hoare triple {pre} call {succ} is valid for a call action.
	 */
	Validity checkCall(IPredicate pre, ICallAction act, IPredicate succ);

	/**
	 * Check if the Hoare quadruple {preLin} {preHier} return {succ} is valid for a return transition. Here, the action
	 * has to be a return, preLin is the IPredicate that describes a set of states of the called procedure before the
	 * return, preHier is the IPredicate that describes a set of states of the calling procedure before the call, and
	 * succ is the IPredicate that describes a set of states of the called procedure.
	 */
	Validity checkReturn(IPredicate preLin, IPredicate preHier, IReturnAction act, IPredicate succ);

	HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark();

	static Validity convertLBool2Validity(final LBool lbool) {
		switch (lbool) {
		case SAT:
			return Validity.INVALID;
		case UNKNOWN:
			return Validity.UNKNOWN;
		case UNSAT:
			return Validity.VALID;
		default:
			throw new AssertionError();
		}
	}
	
	static LBool convertValidity2Lbool(final Validity validity) {
		switch (validity) {
		case INVALID:
			return LBool.SAT;
		case NOT_CHECKED:
			throw new AssertionError();
		case UNKNOWN:
			return LBool.UNKNOWN;
		case VALID:
			return LBool.UNSAT;
		default:
			throw new AssertionError();
		}
	}

	public enum HoareTripleCheckerStatisticsDefinitions implements IStatisticsElement {

		SDtfs(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SDslu(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SDs(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SdLazy(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SolverSat(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SolverUnsat(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SolverUnknown(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		SolverNotchecked(Integer.class, StatisticsType.IN_CA_RE_ADDITION, StatisticsType.DATA_BEFORE_KEY),

		Time(Integer.class, StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),;

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		HoareTripleCheckerStatisticsDefinitions(final Class<?> clazz,
				final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(name()).apply(o);
		}

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}
	}

}
