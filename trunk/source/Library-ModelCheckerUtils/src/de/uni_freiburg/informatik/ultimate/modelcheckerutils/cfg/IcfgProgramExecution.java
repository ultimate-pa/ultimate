/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.NoBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgProgramExecution implements IProgramExecution<IIcfgTransition<IcfgLocation>, Term> {

	private final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> mTrace;
	private final Map<Integer, ProgramState<Term>> mPartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] mBranchEncoders;

	@SuppressWarnings("unchecked")
	public IcfgProgramExecution(final List<? extends IIcfgTransition<?>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping) {
		this(trace, partialProgramStateMapping, new ArrayList<Map<TermVariable, Boolean>>().toArray(new Map[0]), null);
	}

	public IcfgProgramExecution(final List<? extends IIcfgTransition<?>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders) {
		this(trace, partialProgramStateMapping, branchEncoders, null);
	}

	public IcfgProgramExecution(final List<? extends IIcfgTransition<?>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final List<IRelevanceInformation> relevanceInformation) {
		assert trace != null;
		assert partialProgramStateMapping != null;
		assert branchEncoders != null;
		assert relevanceInformation == null || trace.size() == relevanceInformation.size() : "incompatible sizes";

		// a list of boogieastnodes is a trace that consists of atomic
		// statements.
		final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> atomictrace = new ArrayList<>();
		for (int i = 0; i < trace.size(); i++) {
			final IIcfgTransition<IcfgLocation> te = (IIcfgTransition<IcfgLocation>) trace.get(i);
			final IRelevanceInformation ri;
			if (relevanceInformation == null) {
				ri = null;
			} else {
				ri = relevanceInformation.get(i);
			}
			if (te instanceof IIcfgCallTransition<?>) {
				atomictrace.add(new AtomicTraceElement<>(te, te, StepInfo.PROC_CALL, ri, te.getPrecedingProcedure(),
						te.getSucceedingProcedure()));
			} else if (te instanceof IIcfgReturnTransition<?, ?>) {
				atomictrace.add(new AtomicTraceElement<>(te, te, StepInfo.PROC_RETURN, ri, te.getPrecedingProcedure(),
						te.getSucceedingProcedure()));
			} else {
				atomictrace.add(new AtomicTraceElement<>(te, ri));
			}
		}

		mTrace = atomictrace;
		mPartialProgramStateMapping = partialProgramStateMapping;
		mBranchEncoders = branchEncoders;
	}

	public Map<TermVariable, Boolean>[] getBranchEncoders() {
		return mBranchEncoders;
	}

	@Override
	public int getLength() {
		return mTrace.size();
	}

	@Override
	public AtomicTraceElement<IIcfgTransition<IcfgLocation>> getTraceElement(final int i) {
		return mTrace.get(i);
	}

	@Override
	public ProgramState<Term> getProgramState(final int i) {
		if (i < 0 || i >= mTrace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return mPartialProgramStateMapping.get(i);
	}

	@Override
	public ProgramState<Term> getInitialProgramState() {
		return mPartialProgramStateMapping.get(-1);
	}

	@Override
	public String toString() {
		final ProgramExecutionFormatter<IIcfgTransition<IcfgLocation>, Term> pef =
				new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider());
		return pef.formatProgramExecution(this);
	}

	@Override
	public Class<Term> getExpressionClass() {
		return Term.class;
	}

	@Override
	public Class<? extends IIcfgTransition<IcfgLocation>> getTraceElementClass() {
		return IcfgEdge.class;
	}

	public Class<? extends IIcfgTransition<? extends IcfgLocation>> getsTraceElementClass() {
		return IcfgEdge.class;
	}

	public IcfgProgramExecution addRelevanceInformation(final List<IRelevanceInformation> relevanceInformation) {
		final List<IIcfgTransition<IcfgLocation>> edgeSequence = new ArrayList<>();
		for (final AtomicTraceElement<IIcfgTransition<IcfgLocation>> ate : mTrace) {
			edgeSequence.add(ate.getTraceElement());
		}
		return new IcfgProgramExecution(edgeSequence, mPartialProgramStateMapping, mBranchEncoders,
				relevanceInformation);
	}

	@Override
	public IBacktranslationValueProvider<IIcfgTransition<IcfgLocation>, Term> getBacktranslationValueProvider() {
		return new NoBacktranslationValueProvider<>();
	}

}
