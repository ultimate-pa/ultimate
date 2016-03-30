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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * Edge in a recursive control flow graph that represents a sequence of
 * CodeBlocks which are executed one after the other if this edge is executed.
 */
public class SequentialComposition extends CodeBlock implements IInternalAction {

	private static final long serialVersionUID = 9192152338120598669L;
	private final List<CodeBlock> m_CodeBlocks;
	private final String m_PrettyPrinted;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "CodeBlocks (Sequentially Composed)", "PrettyPrintedStatements",
			"TransitionFormula", "OccurenceInCounterexamples" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "CodeBlocks (Sequentially Composed)") {
			return m_CodeBlocks;
		} else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrinted;
		} else if (field == "TransitionFormula") {
			return m_TransitionFormula;
		} else if (field == "OccurenceInCounterexamples") {
			return m_OccurenceInCounterexamples;
		} else {
			throw new UnsupportedOperationException("Unknown field " + field);
		}
	}

	SequentialComposition(int serialNumber, ProgramPoint source, ProgramPoint target, Boogie2SMT boogie2smt,
			ModifiableGlobalVariableManager modGlobVarManager, boolean simplify, boolean extPqe,
			IUltimateServiceProvider services, List<CodeBlock> codeBlocks) {
		super(serialNumber, source, target, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		this.m_CodeBlocks = codeBlocks;

		StringBuilder prettyPrinted = new StringBuilder();

		int numberCalls = 0;
		int numberReturns = 0;
		for (int i = 0; i < codeBlocks.size(); i++) {
			if (codeBlocks.get(i) instanceof InterproceduralSequentialComposition) {
				throw new IllegalArgumentException("InterproceduralSequentialComposition "
						+ "must not participate in sequential compositions");
			} else if (codeBlocks.get(i) instanceof Call) {
				numberCalls++;
			} else if (codeBlocks.get(i) instanceof Return) {
				numberReturns++;
			} else if (codeBlocks.get(i) instanceof StatementSequence || codeBlocks.get(i) instanceof SequentialComposition
					|| codeBlocks.get(i) instanceof ParallelComposition || codeBlocks.get(i) instanceof Summary
					|| codeBlocks.get(i) instanceof GotoEdge) {
				// do nothing
			} else {
				throw new IllegalArgumentException("unknown CodeBlock");
			}
			codeBlocks.get(i).disconnectSource();
			codeBlocks.get(i).disconnectTarget();
			prettyPrinted.append(codeBlocks.get(i).getPrettyPrintedStatements());
			ModelUtils.copyAnnotations(codeBlocks.get(i), this);
		}
		// workaround: set annotation with this pluginId again, because it was
		// overwritten by the mergeAnnotations method
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, m_Annotation);
		checkNumberOfCallsAndReturns(numberCalls, numberReturns);

		boolean s_TransformToCNF = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
				.getBoolean(RcfgPreferenceInitializer.LABEL_CNF);

		m_TransitionFormula = getInterproceduralTransFormula(boogie2smt, modGlobVarManager, simplify, extPqe,
				s_TransformToCNF, false, mLogger, services, codeBlocks);
		m_TransitionFormulaWithBranchEncoders = getInterproceduralTransFormula(boogie2smt, modGlobVarManager, simplify,
				extPqe, s_TransformToCNF, true, mLogger, services, codeBlocks);

		m_PrettyPrinted = prettyPrinted.toString();
	}

	protected void checkNumberOfCallsAndReturns(int numberCalls, int numberReturns) {
		if (numberCalls != numberReturns) {
			throw new IllegalArgumentException("same number of calls and returns required");
		}
	}

	@Override
	public String getPrettyPrintedStatements() {
		return m_PrettyPrinted;
	}

	public List<CodeBlock> getCodeBlocks() {
		return m_CodeBlocks;
	}

	@Override
	public void setTransitionFormula(TransFormula transFormula) {
		throw new UnsupportedOperationException("transition formula is computed in constructor");
	}

	/**
	 * Returns Transformula for a sequence of CodeBlocks that may (opposed to
	 * the method sequentialComposition) contain also Call and Return.
	 * 
	 * @param logger
	 * @param services
	 */
	public static TransFormula getInterproceduralTransFormula(Boogie2SMT boogie2smt,
			ModifiableGlobalVariableManager modGlobVarManager, boolean simplify, boolean extPqe, boolean tranformToCNF,
			boolean withBranchEncoders, Logger logger, IUltimateServiceProvider services, List<CodeBlock> codeBlocks) {
		return getInterproceduralTransFormula(boogie2smt, modGlobVarManager, simplify, extPqe, tranformToCNF,
				withBranchEncoders, null, null, null, logger, services, codeBlocks);
	}

	private static TransFormula getInterproceduralTransFormula(Boogie2SMT boogie2smt,
			ModifiableGlobalVariableManager modGlobVarManager, boolean simplify, boolean extPqe, boolean tranformToCNF,
			boolean withBranchEncoders, TransFormula[] beforeCall, Call call, Return ret, Logger logger,
			IUltimateServiceProvider services, List<CodeBlock> codeBlocks) {
		List<TransFormula> beforeFirstPendingCall = new ArrayList<TransFormula>();
		Call lastUnmatchedCall = null;
		int callsSinceLastUnmatchedCall = 0;
		int returnsSinceLastUnmatchedCall = 0;
		List<CodeBlock> afterLastUnmatchedCall = new ArrayList<CodeBlock>();
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
						Return correspondingReturn = (Return) codeBlocks.get(i);
						List<CodeBlock> codeBlocksBetween = new ArrayList<CodeBlock>(afterLastUnmatchedCall);
						TransFormula localTransFormula = getInterproceduralTransFormula(boogie2smt, modGlobVarManager,
								simplify, extPqe, tranformToCNF, withBranchEncoders, null, lastUnmatchedCall,
								correspondingReturn, logger, services, codeBlocksBetween);
						beforeFirstPendingCall.add(localTransFormula);
						lastUnmatchedCall = null;
						callsSinceLastUnmatchedCall = 0;
						returnsSinceLastUnmatchedCall = 0;
						afterLastUnmatchedCall = new ArrayList<CodeBlock>();
					} else {
						returnsSinceLastUnmatchedCall++;
						afterLastUnmatchedCall.add(codeBlocks.get(i));
					}
					assert (callsSinceLastUnmatchedCall >= returnsSinceLastUnmatchedCall);
				} else if (codeBlocks.get(i) instanceof Call) {
					callsSinceLastUnmatchedCall++;
					afterLastUnmatchedCall.add(codeBlocks.get(i));
				} else {
					afterLastUnmatchedCall.add(codeBlocks.get(i));
				}
			}
		}

		final TransFormula tfForCodeBlocks;
		if (lastUnmatchedCall == null) {
			assert afterLastUnmatchedCall.isEmpty();
			// no pending call in codeBlocks
			tfForCodeBlocks = TransFormula.sequentialComposition(logger, services, boogie2smt, simplify, extPqe,
					tranformToCNF, beforeFirstPendingCall.toArray(new TransFormula[0]));
		} else {
			// there is a pending call in codeBlocks
			assert (ret == null) : "no pending call between call and return possible!";
			List<CodeBlock> codeBlocksBetween = afterLastUnmatchedCall;
			tfForCodeBlocks = getInterproceduralTransFormula(boogie2smt, modGlobVarManager, simplify, extPqe,
					tranformToCNF, withBranchEncoders, beforeFirstPendingCall.toArray(new TransFormula[0]),
					lastUnmatchedCall, null, logger, services, codeBlocksBetween);
		}

		TransFormula result;
		if (call == null) {
			assert (ret == null);
			assert (beforeCall == null);
			result = tfForCodeBlocks;
		} else {
			if (ret == null) {
				String proc = call.getCallStatement().getMethodName();
				TransFormula oldVarsAssignment = modGlobVarManager.getOldVarsAssignment(proc);
				final String nameEndProcedure;
				if (lastUnmatchedCall == null) {
					nameEndProcedure = proc;
				} else {				
					nameEndProcedure = lastUnmatchedCall.getCallStatement().getMethodName();
				}
				Set<BoogieVar> modifiableGlobalsOfEndProcedure = modGlobVarManager.getModifiedBoogieVars(nameEndProcedure);
				result = TransFormula.sequentialCompositionWithPendingCall(boogie2smt, simplify, extPqe, tranformToCNF,
						Arrays.asList(beforeCall), call.getTransitionFormula(), oldVarsAssignment, tfForCodeBlocks, logger, services, modifiableGlobalsOfEndProcedure);
			} else {
				assert (beforeCall == null);
				String proc = call.getCallStatement().getMethodName();
				TransFormula oldVarsAssignment = modGlobVarManager.getOldVarsAssignment(proc);
				TransFormula globalVarsAssignment = modGlobVarManager.getGlobalVarsAssignment(proc);
				result = TransFormula.sequentialCompositionWithCallAndReturn(boogie2smt, simplify, extPqe,
						tranformToCNF, call.getTransitionFormula(), oldVarsAssignment, globalVarsAssignment,
						tfForCodeBlocks, ret.getTransitionFormula(), logger, services);
			}

		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (CodeBlock cb : m_CodeBlocks) {
			sb.append(cb.toString());
		}
		return sb.toString();
	}

	@Override
	public TransFormula getTransformula() {
		return getTransitionFormula();
	}

}
