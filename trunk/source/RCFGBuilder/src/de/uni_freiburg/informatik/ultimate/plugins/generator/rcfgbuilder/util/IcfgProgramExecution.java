/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgProgramExecution implements IProgramExecution<IcfgEdge, Term> {

	private final List<AtomicTraceElement<IcfgEdge>> mTrace;
	private final Map<Integer, ProgramState<Term>> mPartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] mBranchEncoders;
	private final Map<String, ILocation> mOverapproximations;

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
		final List<AtomicTraceElement<IcfgEdge>> atomictrace = new ArrayList<>();
		for (int i = 0; i < trace.size(); i++) {
			final IcfgEdge te = (IcfgEdge) trace.get(i);
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
		mOverapproximations = getOverapproximations(trace);
	}

	/**
	 * Returns all overapproximations that were done on this trace.
	 */
	public Map<String, ILocation> getOverapproximations() {
		return mOverapproximations;
	}

	public Map<TermVariable, Boolean>[] getBranchEncoders() {
		return mBranchEncoders;
	}

	@Override
	public int getLength() {
		return mTrace.size();
	}

	@Override
	public AtomicTraceElement<IcfgEdge> getTraceElement(final int i) {
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

	public static Map<String, ILocation> getOverapproximations(final List<? extends IElement> trace) {
		final Map<String, ILocation> result = new HashMap<>();
		for (final IElement cb : trace) {
			final Overapprox overapprox = Overapprox.getAnnotation(cb);
			if (overapprox == null) {
				continue;
			}
			result.putAll(overapprox.getOverapproximatedLocations());
		}
		return result;
	}

	private static String ppsToString(final ProgramState<Term> pps) {
		String result;
		if (pps == null) {
			result = null;
		} else {
			final StringBuilder sb = new StringBuilder();
			for (final Term variable : pps.getVariables()) {
				final Term value = pps.getValues(variable).iterator().next();
				sb.append("  ");
				final String var = variable.toStringDirect();
				final String val = value.toStringDirect();
				sb.append(var).append("=").append(val);
			}
			result = sb.toString();
		}
		return result;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		String valuation = ppsToString(getInitialProgramState());
		final String lineSeparator = CoreUtil.getPlatformLineSeparator();

		sb.append("=== Start of program execution ===").append(lineSeparator);
		if (valuation != null) {
			sb.append("initial values:");
			sb.append(valuation);
			sb.append(lineSeparator);
		}
		for (int i = 0; i < mTrace.size(); i++) {
			sb.append("statement");
			sb.append(i);
			sb.append(": ");
			sb.append(mTrace.get(i).toString());
			sb.append(lineSeparator);
			valuation = ppsToString(getProgramState(i));
			if (valuation != null) {
				sb.append("values");
				sb.append(i);
				sb.append(":");
				sb.append(valuation);
				sb.append(lineSeparator);
			}
		}
		sb.append("=== End of program execution");
		return sb.toString();
	}

	@Override
	public Class<Term> getExpressionClass() {
		return Term.class;
	}

	@Override
	public Class<IcfgEdge> getTraceElementClass() {
		return IcfgEdge.class;
	}

	@Override
	public String getSVCOMPWitnessString() {
		return null;
	}

	public List<UnprovabilityReason> getUnprovabilityReasons() {
		final List<UnprovabilityReason> unproabilityReasons = new ArrayList<>();
		for (final Entry<String, ILocation> entry : mOverapproximations.entrySet()) {
			unproabilityReasons
					.add(new UnprovabilityReason("overapproximation of " + entry.getKey(), entry.getValue()));
		}
		return unproabilityReasons;
	}

	public IcfgProgramExecution addRelevanceInformation(final List<IRelevanceInformation> relevanceInformation) {
		final List<IcfgEdge> edgeSequence = new ArrayList<>();
		for (final AtomicTraceElement<IcfgEdge> ate : mTrace) {
			edgeSequence.add(ate.getTraceElement());
		}
		return new IcfgProgramExecution(edgeSequence, mPartialProgramStateMapping, mBranchEncoders,
				relevanceInformation);
	}

}
