/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.loopaccelerator.Accelerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class AcceleratedInterpolationMain<LETTER extends IIcfgTransition<?>>
		implements IInterpolatingTraceCheck<LETTER> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final List<LETTER> mCounterexample;
	private final IPredicateUnifier mPredicateUnifier;

	private final Accelerator mLoopAccelerator;

	public AcceleratedInterpolationMain(final ILogger logger, final ITraceCheckPreferences prefs,
			final IPredicateUnifier predicateUnifier, final List<LETTER> counterexample) {
		mLogger = logger;
		mServices = prefs.getUltimateServices();
		mCounterexample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mLogger.debug("Accelerated Interpolation engaged!");
		mLoopAccelerator = new Accelerator();
	}

	@Override
	public LBool isCorrect() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPredicate getPrecondition() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPredicate getPostcondition() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public List<LETTER> getTrace() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPredicate[] getInterpolants() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isPerfectSequence() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

}
