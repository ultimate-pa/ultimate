/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * Edge in a recursive control flow graph that represents a sequence of CodeBlocks which are executed one after the
 * other if this edge is executed.
 *
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class SequentialComposition extends CodeBlock implements IInternalAction {

	private static final long serialVersionUID = 9192152338120598669L;
	private final List<CodeBlock> mCodeBlocks;
	private final String mPrettyPrinted;
	private final int mCallsWithoutReturns;

	SequentialComposition(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final CfgSmtToolkit csToolkit, final boolean simplify, final boolean extPqe,
			final IUltimateServiceProvider services, final List<CodeBlock> codeBlocks,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		super(serialNumber, source, target, services.getLoggingService().getLogger(Activator.PLUGIN_ID));

		mCodeBlocks = codeBlocks;
		final StringBuilder prettyPrinted = new StringBuilder();
		mCallsWithoutReturns = getCheckedOpenCalls(codeBlocks).size();

		for (final CodeBlock currentCodeblock : codeBlocks) {
			currentCodeblock.disconnectSource();
			currentCodeblock.disconnectTarget();
			prettyPrinted.append(currentCodeblock.getPrettyPrintedStatements());
			ModelUtils.copyAnnotations(currentCodeblock, this);
		}
		mPrettyPrinted = prettyPrinted.toString();

		// workaround: set annotation with this pluginId again, because it was
		// overwritten by the mergeAnnotations method
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, mAnnotation);

		final boolean transformToCNF =
				services.getPreferenceProvider(Activator.PLUGIN_ID).getBoolean(RcfgPreferenceInitializer.LABEL_CNF);

		mTransitionFormula = getInterproceduralTransFormula(csToolkit, simplify, extPqe, transformToCNF, false, mLogger,
				services, codeBlocks, xnfConversionTechnique, simplificationTechnique);
		mTransitionFormulaWithBranchEncoders = getInterproceduralTransFormula(csToolkit, simplify, extPqe,
				transformToCNF, true, mLogger, services, codeBlocks, xnfConversionTechnique, simplificationTechnique);
	}

	private Deque<Call> getCheckedOpenCalls(final List<CodeBlock> codeBlocks) {
		final Deque<Call> callstack = new ArrayDeque<>();
		for (final CodeBlock currentCodeblock : codeBlocks) {
			if (currentCodeblock instanceof Call) {
				callstack.addFirst((Call) currentCodeblock);
			} else if (currentCodeblock instanceof Return) {
				final Return currentReturn = (Return) currentCodeblock;
				if (callstack.isEmpty()) {
					throw new IllegalArgumentException("Call/Return order violated");
				}
				final Call lastCall = callstack.removeFirst();
				if (!Objects.equals(currentReturn.getCallStatement(), lastCall.getCallStatement())) {
					throw new IllegalArgumentException("Call/Return order violated");
				}
			} else if (currentCodeblock.getNumberOfOpenCalls() != 0) {
				if (currentCodeblock instanceof SequentialComposition) {
					final SequentialComposition seqComp = (SequentialComposition) currentCodeblock;
					final Deque<Call> innerCallstack = getCheckedOpenCalls(seqComp.getCodeBlocks());
					callstack.addAll(innerCallstack);
				} else {
					throw new IllegalArgumentException("Open calls are only supported in sequential compositions");
				}
			}
		}
		return callstack;
	}

	@Override
	public String getPrettyPrintedStatements() {
		return mPrettyPrinted;
	}

	@Visualizable
	public List<CodeBlock> getCodeBlocks() {
		return mCodeBlocks;
	}

	@Override
	public void setTransitionFormula(final UnmodifiableTransFormula transFormula) {
		throw new UnsupportedOperationException("transition formula is computed in constructor");
	}

	/**
	 * Returns Transformula for a sequence of CodeBlocks that may (opposed to the method sequentialComposition) contain
	 * also Call and Return.
	 *
	 * @param logger
	 * @param services
	 */
	public static UnmodifiableTransFormula getInterproceduralTransFormula(final CfgSmtToolkit csToolkit,
			final boolean simplify, final boolean extPqe, final boolean tranformToCNF, final boolean withBranchEncoders,
			final ILogger logger, final IUltimateServiceProvider services, final List<CodeBlock> codeBlocks,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		return getInterproceduralTransFormula(csToolkit, simplify, extPqe, tranformToCNF, withBranchEncoders, null,
				null, null, null, logger, services, codeBlocks, xnfConversionTechnique, simplificationTechnique);
	}

	private static UnmodifiableTransFormula getInterproceduralTransFormula(final CfgSmtToolkit csToolkit,
			final boolean simplify, final boolean extPqe, final boolean tranformToCNF, final boolean withBranchEncoders,
			final String nameStartProcedure, final UnmodifiableTransFormula[] beforeCall, final Call call,
			final Return ret, final ILogger logger, final IUltimateServiceProvider services,
			final List<CodeBlock> codeBlocks, final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		final List<UnmodifiableTransFormula> beforeFirstPendingCall = new ArrayList<>();
		Call lastUnmatchedCall = null;
		int callsSinceLastUnmatchedCall = 0;
		int returnsSinceLastUnmatchedCall = 0;
		List<CodeBlock> afterLastUnmatchedCall = new ArrayList<>();
		for (int i = 0; i < codeBlocks.size(); i++) {
			if (lastUnmatchedCall == null) {
				if (codeBlocks.get(i) instanceof Call) {
					lastUnmatchedCall = (Call) codeBlocks.get(i);
				} else {
					assert !(codeBlocks.get(i) instanceof Return);
					if (withBranchEncoders) {
						beforeFirstPendingCall.add(codeBlocks.get(i).getTransitionFormulaWithBranchEncoders());
					} else {
						beforeFirstPendingCall.add(codeBlocks.get(i).getTransitionFormula());
					}
				}
			} else {
				if (codeBlocks.get(i) instanceof Return) {
					if (callsSinceLastUnmatchedCall == returnsSinceLastUnmatchedCall) {
						final Return correspondingReturn = (Return) codeBlocks.get(i);
						final List<CodeBlock> codeBlocksBetween = new ArrayList<>(afterLastUnmatchedCall);
						final UnmodifiableTransFormula localTransFormula =
								getInterproceduralTransFormula(csToolkit, simplify, extPqe, tranformToCNF,
										withBranchEncoders, null, null, lastUnmatchedCall, correspondingReturn, logger,
										services, codeBlocksBetween, xnfConversionTechnique, simplificationTechnique);
						beforeFirstPendingCall.add(localTransFormula);
						lastUnmatchedCall = null;
						callsSinceLastUnmatchedCall = 0;
						returnsSinceLastUnmatchedCall = 0;
						afterLastUnmatchedCall = new ArrayList<>();
					} else {
						returnsSinceLastUnmatchedCall++;
						afterLastUnmatchedCall.add(codeBlocks.get(i));
					}
					assert callsSinceLastUnmatchedCall >= returnsSinceLastUnmatchedCall;
				} else if (codeBlocks.get(i) instanceof Call) {
					callsSinceLastUnmatchedCall++;
					afterLastUnmatchedCall.add(codeBlocks.get(i));
				} else {
					afterLastUnmatchedCall.add(codeBlocks.get(i));
				}
			}
		}

		final UnmodifiableTransFormula tfForCodeBlocks;
		if (lastUnmatchedCall == null) {
			assert afterLastUnmatchedCall.isEmpty();
			// no pending call in codeBlocks
			tfForCodeBlocks = TransFormulaUtils.sequentialComposition(logger, services, csToolkit.getManagedScript(),
					simplify, extPqe, tranformToCNF, xnfConversionTechnique, simplificationTechnique,
					beforeFirstPendingCall);
		} else {
			// there is a pending call in codeBlocks
			assert ret == null : "no pending call between call and return possible!";
			final List<CodeBlock> codeBlocksBetween = afterLastUnmatchedCall;
			tfForCodeBlocks = getInterproceduralTransFormula(csToolkit, simplify, extPqe, tranformToCNF,
					withBranchEncoders, codeBlocks.get(0).getPrecedingProcedure(),
					beforeFirstPendingCall.toArray(new UnmodifiableTransFormula[beforeFirstPendingCall.size()]),
					lastUnmatchedCall, null, logger, services, codeBlocksBetween, xnfConversionTechnique,
					simplificationTechnique);
		}

		UnmodifiableTransFormula result;
		if (call == null) {
			assert ret == null;
			assert beforeCall == null;
			result = tfForCodeBlocks;
		} else {
			if (ret == null) {
				final String proc = call.getCallStatement().getMethodName();
				final UnmodifiableTransFormula oldVarsAssignment =
						csToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(proc);
				final UnmodifiableTransFormula globalVarsAssignment =
						csToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(proc);
				final String nameEndProcedure;
				if (lastUnmatchedCall == null) {
					nameEndProcedure = proc;
				} else {
					nameEndProcedure = lastUnmatchedCall.getCallStatement().getMethodName();
				}
				final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure =
						csToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(nameEndProcedure);
				result = TransFormulaUtils.sequentialCompositionWithPendingCall(csToolkit.getManagedScript(), simplify,
						extPqe, tranformToCNF, Arrays.asList(beforeCall), call.getLocalVarsAssignment(),
						oldVarsAssignment, globalVarsAssignment, tfForCodeBlocks, logger, services,
						modifiableGlobalsOfEndProcedure, xnfConversionTechnique, simplificationTechnique,
						csToolkit.getSymbolTable(), nameStartProcedure, call.getPrecedingProcedure(),
						call.getCallStatement().getMethodName(), nameEndProcedure,
						csToolkit.getModifiableGlobalsTable());
			} else {
				assert beforeCall == null;
				final String proc = call.getCallStatement().getMethodName();
				final UnmodifiableTransFormula oldVarsAssignment =
						csToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(proc);
				final UnmodifiableTransFormula globalVarsAssignment =
						csToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(proc);
				result = TransFormulaUtils.sequentialCompositionWithCallAndReturn(csToolkit.getManagedScript(),
						simplify, extPqe, tranformToCNF, call.getLocalVarsAssignment(), oldVarsAssignment,
						globalVarsAssignment, tfForCodeBlocks, ret.getTransitionFormula(), logger, services,
						xnfConversionTechnique, simplificationTechnique, csToolkit.getSymbolTable(),
						csToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(proc));
			}

		}
		return result;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final CodeBlock cb : mCodeBlocks) {
			sb.append(cb.toString());
		}
		return sb.toString();
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		return getTransitionFormula();
	}

	@Override
	protected int getNumberOfOpenCalls() {
		return mCallsWithoutReturns;
	}
}
