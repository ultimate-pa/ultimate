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

package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RcfgProgramExecution implements IProgramExecution<RCFGEdge, Expression> {

	private final List<AtomicTraceElement<RCFGEdge>> mTrace;
	private final Map<Integer, ProgramState<Expression>> mPartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] mBranchEncoders;
	private final Map<String, ILocation> mOverapproximations;

	@SuppressWarnings("unchecked")
	public RcfgProgramExecution(final List<? extends RCFGEdge> trace,
			final Map<Integer, ProgramState<Expression>> partialProgramStateMapping) {
		this(trace, partialProgramStateMapping, new ArrayList<Map<TermVariable, Boolean>>().toArray(new Map[0]));
	}

	public RcfgProgramExecution(final List<? extends RCFGEdge> trace,
			final Map<Integer, ProgramState<Expression>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders) {
		assert trace != null;
		assert partialProgramStateMapping != null;
		assert branchEncoders != null;

		// a list of boogieastnodes is a trace that consists of atomic
		// statements.
		ArrayList<AtomicTraceElement<RCFGEdge>> atomictrace = new ArrayList<>();
		for (RCFGEdge te : trace) {
			if (te instanceof Call) {
				atomictrace.add(new AtomicTraceElement<RCFGEdge>(te, te, StepInfo.PROC_CALL));
			} else if (te instanceof Return) {
				atomictrace.add(new AtomicTraceElement<RCFGEdge>(te, te, StepInfo.PROC_RETURN));
			} else {
				atomictrace.add(new AtomicTraceElement<RCFGEdge>(te));
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
	public AtomicTraceElement<RCFGEdge> getTraceElement(int i) {
		return mTrace.get(i);
	}

	@Override
	public ProgramState<Expression> getProgramState(int i) {
		if (i < 0 || i >= mTrace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return mPartialProgramStateMapping.get(i);
	}

	@Override
	public ProgramState<Expression> getInitialProgramState() {
		return mPartialProgramStateMapping.get(-1);
	}

	public static Map<String, ILocation> getOverapproximations(List<? extends RCFGEdge> trace) {
		Map<String, ILocation> result = new HashMap<>();
		for (RCFGEdge cb : trace) {
			if (cb.getPayload().hasAnnotation()) {
				HashMap<String, IAnnotations> annotations = cb.getPayload().getAnnotations();
				if (annotations.containsKey(Overapprox.getIdentifier())) {
					Overapprox overapprox = (Overapprox) annotations.get(Overapprox.getIdentifier());
					@SuppressWarnings("unchecked")
					Map<String, ILocation> reason2Location = (Map<String, ILocation>) overapprox.getAnnotationsAsMap()
							.get(Overapprox.s_LOCATION_MAPPING);
					for (Entry<String, ILocation> entry : reason2Location.entrySet()) {
						result.put(entry.getKey(), entry.getValue());
					}
				}
			}
		}
		return result;
	}

	private String ppstoString(ProgramState<Expression> pps) {
		String result;
		if (pps == null) {
			result = null;
		} else {
			StringBuilder sb = new StringBuilder();
			for (Expression variable : pps.getVariables()) {
				Expression value = pps.getValues(variable).iterator().next();
				sb.append("  ");
				String var = BoogiePrettyPrinter.print(variable);
				String val = BoogiePrettyPrinter.print(value);
				sb.append(var).append("=").append(val);
			}
			result = sb.toString();
		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String valuation = ppstoString(getInitialProgramState());
		String lineSeparator = CoreUtil.getPlatformLineSeparator();

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
			valuation = ppstoString(getProgramState(i));
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

	/**
	 * Workaround to satisfy the parameters of results.
	 * 
	 * @return
	 */
	@Deprecated
	public List<ILocation> getLocationList() {
		List<ILocation> result = new ArrayList<ILocation>();
		for (AtomicTraceElement<RCFGEdge> cb : mTrace) {
			result.add(cb.getTraceElement().getPayload().getLocation());
		}
		return result;
	}

	@Override
	public Class<Expression> getExpressionClass() {
		return Expression.class;
	}

	@Override
	public Class<RCFGEdge> getTraceElementClass() {
		return RCFGEdge.class;
	}

	@Override
	public String getSVCOMPWitnessString() {
		return null;
	}

	public List<UnprovabilityReason> getUnprovabilityReasons() {
		List<UnprovabilityReason> unproabilityReasons = new ArrayList<UnprovabilityReason>();
		for (Entry<String, ILocation> entry : mOverapproximations.entrySet()) {
			unproabilityReasons.add(new UnprovabilityReason(entry.getKey(), entry.getValue()));
		}
		return unproabilityReasons;
	}

}
