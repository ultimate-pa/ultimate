/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.AbstractCounterexample;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RcfgResultReporter<STATE extends IAbstractState<STATE>, ACTION extends IcfgEdge, LOC extends IcfgLocation>
		implements IResultReporter<STATE, ACTION, LOC> {

	protected final IUltimateServiceProvider mServices;
	private final IIcfg<LOC> mIcfg;
	private final Set<LOC> mUnsafeLocs;
	private boolean mIsFinished;

	public RcfgResultReporter(final IIcfg<LOC> icfg, final IUltimateServiceProvider services) {
		mServices = services;
		mIcfg = icfg;
		mUnsafeLocs = new HashSet<>();
		mIsFinished = false;
	}

	@Override
	public void reportPossibleError(final AbstractCounterexample<DisjunctiveAbstractState<STATE>, ACTION, LOC> cex) {
		final Map<Integer, ProgramState<Term>> programStates = new HashMap<>();
		final List<IcfgEdge> trace = new ArrayList<>();

		programStates.put(-1, computeProgramState(cex.getInitialState()));

		int i = 0;
		for (final Triple<DisjunctiveAbstractState<STATE>, LOC, ACTION> elem : cex.getAbstractExecution()) {
			trace.add(elem.getThird().getLabel());
			programStates.put(i, computeProgramState(elem.getFirst()));
			++i;
		}
		final IcfgProgramExecution<IcfgEdge> pex = IcfgProgramExecution.create(trace, programStates);

		final LOC errorLoc = getLast(cex);
		if (!mUnsafeLocs.add(errorLoc)) {
			throw new AssertionError("You added a possible error for this location twice: " + errorLoc);
		}
		final IResult result = new UnprovableResult<>(Activator.PLUGIN_ID, errorLoc,
				mServices.getBacktranslationService(), pex, "abstract domain could reach this error location");

		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

	private ProgramState<Term> computeProgramState(final DisjunctiveAbstractState<STATE> abstractMultiState) {
		// TODO: Compute program state
		return new ProgramState<>(Collections.emptyMap(), Term.class);
	}

	private LOC getLast(final AbstractCounterexample<DisjunctiveAbstractState<STATE>, ACTION, LOC> cex) {
		final int size = cex.getAbstractExecution().size();
		return cex.getAbstractExecution().get(size - 1).getSecond();
	}

	@Override
	public void reportFinished() {
		assert !mIsFinished : "You should not call this method twice";
		mIsFinished = true;

		final Set<LOC> errorLocs = IcfgUtils.getErrorLocations(mIcfg);
		if (mUnsafeLocs.isEmpty()) {
			final AllSpecificationsHoldResult result = AllSpecificationsHoldResult
					.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, errorLocs.size());
			reportResult(result);
		}

		final Set<LOC> safeLocs = DataStructureUtils.difference(errorLocs, mUnsafeLocs);
		for (final IcfgLocation safeErrorLoc : safeLocs) {
			final PositiveResult<IIcfgElement> pResult =
					new PositiveResult<>(Activator.PLUGIN_NAME, safeErrorLoc, mServices.getBacktranslationService());
			reportResult(pResult);
		}
	}

	private void reportResult(final IResult result) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

}
