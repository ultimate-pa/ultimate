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

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * Edge in a recursive control flow graph that represents a sequence of CodeBlocks which are executed one after the
 * other if this edge is executed.
 * 
 * @author Matthias Heizmann
 */
public class SequentialComposition extends CodeBlock implements IInternalAction {

	private static final long serialVersionUID = 9192152338120598669L;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new attributes.
	 */
	private static final String[] ATTRIBUTE_FIELDS = { "CodeBlocks (Sequentially Composed)", "PrettyPrintedStatements",
			"TransitionFormula", "OccurenceInCounterexamples" };

	private final List<CodeBlock> mCodeBlocks;
	private final String mPrettyPrinted;

	SequentialComposition(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target, final ManagedScript mgdScript,
			final ModifiableGlobalVariableManager modGlobVarManager, final boolean simplify, final boolean extPqe,
			final IUltimateServiceProvider services, final List<CodeBlock> codeBlocks, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique, final ICfgSymbolTable symbolTable) {
		super(serialNumber, source, target, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		mCodeBlocks = codeBlocks;

		final StringBuilder prettyPrinted = new StringBuilder();

		int numberCalls = 0;
		int numberReturns = 0;
		for (int i = 0; i < codeBlocks.size(); i++) {
			if (codeBlocks.get(i) instanceof InterproceduralSequentialComposition) {
				throw new IllegalArgumentException(
						"InterproceduralSequentialComposition " + "must not participate in sequential compositions");
			} else if (codeBlocks.get(i) instanceof Call) {
				numberCalls++;
			} else if (codeBlocks.get(i) instanceof Return) {
				numberReturns++;
			} else if (codeBlocks.get(i) instanceof StatementSequence
					|| codeBlocks.get(i) instanceof SequentialComposition
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
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, mAnnotation);
		checkNumberOfCallsAndReturns(numberCalls, numberReturns);

		final boolean transformToCNF =
				services.getPreferenceProvider(Activator.PLUGIN_ID).getBoolean(RcfgPreferenceInitializer.LABEL_CNF);

		mTransitionFormula = getInterproceduralTransFormula(mgdScript, modGlobVarManager, simplify, extPqe,
				transformToCNF, false, mLogger, services, codeBlocks, xnfConversionTechnique, simplificationTechnique, symbolTable);
		mTransitionFormulaWithBranchEncoders = getInterproceduralTransFormula(mgdScript, modGlobVarManager, simplify,
				extPqe, transformToCNF, true, mLogger, services, codeBlocks, xnfConversionTechnique, simplificationTechnique, symbolTable);

		mPrettyPrinted = prettyPrinted.toString();
	}

	@Override
	protected String[] getFieldNames() {
		return ATTRIBUTE_FIELDS;
	}

	@Override
	protected Object getFieldValue(final String field) {
		if ("CodeBlocks (Sequentially Composed)".equals(field)) {
			return mCodeBlocks;
		} else if ("PrettyPrintedStatements".equals(field)) {
			return mPrettyPrinted;
		} else if ("TransitionFormula".equals(field)) {
			return mTransitionFormula;
		} else if ("OccurenceInCounterexamples".equals(field)) {
			return mOccurenceInCounterexamples;
		} else {
			throw new UnsupportedOperationException("Unknown field " + field);
		}
	}
	
	protected void checkNumberOfCallsAndReturns(final int numberCalls, final int numberReturns) {
		if (numberCalls != numberReturns) {
			throw new IllegalArgumentException("same number of calls and returns required");
		}
	}

	@Override
	public String getPrettyPrintedStatements() {
		return mPrettyPrinted;
	}

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
	 * @param symbolTable 
	 */
	public static UnmodifiableTransFormula getInterproceduralTransFormula(final ManagedScript boogie2smt,
			final ModifiableGlobalVariableManager modGlobVarManager, final boolean simplify, final boolean extPqe, final boolean tranformToCNF,
			final boolean withBranchEncoders, final ILogger logger, final IUltimateServiceProvider services, 
			final List<CodeBlock> codeBlocks,final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique, 
			final ICfgSymbolTable symbolTable) {
		return getInterproceduralTransFormula(boogie2smt, modGlobVarManager, simplify, extPqe, tranformToCNF,
				withBranchEncoders, null, null, null, null, logger, services, codeBlocks, xnfConversionTechnique, simplificationTechnique, symbolTable);
	}

	private static UnmodifiableTransFormula getInterproceduralTransFormula(final ManagedScript mgdScript,
			final ModifiableGlobalVariableManager modGlobVarManager, final boolean simplify, final boolean extPqe, final boolean tranformToCNF,
			final boolean withBranchEncoders, final String nameStartProcedure, final UnmodifiableTransFormula[] beforeCall, final Call call, final Return ret, final ILogger logger,
			final IUltimateServiceProvider services, final List<CodeBlock> codeBlocks, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique, final ICfgSymbolTable symbolTable) {
		final List<UnmodifiableTransFormula> beforeFirstPendingCall = new ArrayList<UnmodifiableTransFormula>();
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
						final Return correspondingReturn = (Return) codeBlocks.get(i);
						final List<CodeBlock> codeBlocksBetween = new ArrayList<CodeBlock>(afterLastUnmatchedCall);
						final UnmodifiableTransFormula localTransFormula = getInterproceduralTransFormula(mgdScript,
								modGlobVarManager, simplify, extPqe, tranformToCNF, withBranchEncoders, null, null,
								lastUnmatchedCall, correspondingReturn, logger, services, codeBlocksBetween, 
								xnfConversionTechnique, simplificationTechnique, symbolTable);
						beforeFirstPendingCall.add(localTransFormula);
						lastUnmatchedCall = null;
						callsSinceLastUnmatchedCall = 0;
						returnsSinceLastUnmatchedCall = 0;
						afterLastUnmatchedCall = new ArrayList<CodeBlock>();
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
			tfForCodeBlocks = TransFormulaUtils.sequentialComposition(logger, services, mgdScript, simplify, extPqe,
					tranformToCNF, xnfConversionTechnique, simplificationTechnique, beforeFirstPendingCall);
		} else {
			// there is a pending call in codeBlocks
			assert ret == null : "no pending call between call and return possible!";
			final List<CodeBlock> codeBlocksBetween = afterLastUnmatchedCall;
			tfForCodeBlocks = getInterproceduralTransFormula(mgdScript, modGlobVarManager, simplify, extPqe,
					tranformToCNF, withBranchEncoders, codeBlocks.get(0).getPrecedingProcedure(),
					beforeFirstPendingCall.toArray(new UnmodifiableTransFormula[beforeFirstPendingCall.size()]), lastUnmatchedCall,
					null, logger, services, codeBlocksBetween, xnfConversionTechnique, simplificationTechnique, symbolTable);
		}

		UnmodifiableTransFormula result;
		if (call == null) {
			assert ret == null;
			assert beforeCall == null;
			result = tfForCodeBlocks;
		} else {
			if (ret == null) {
				final String proc = call.getCallStatement().getMethodName();
				final UnmodifiableTransFormula oldVarsAssignment = modGlobVarManager.getOldVarsAssignment(proc);
				final UnmodifiableTransFormula globalVarsAssignment = modGlobVarManager.getGlobalVarsAssignment(proc);
				final String nameEndProcedure;
				if (lastUnmatchedCall == null) {
					nameEndProcedure = proc;
				} else {
					nameEndProcedure = lastUnmatchedCall.getCallStatement().getMethodName();
				}
				final Set<IProgramVar> modifiableGlobalsOfEndProcedure =
						modGlobVarManager.getModifiedBoogieVars(nameEndProcedure);
				result = TransFormulaUtils.sequentialCompositionWithPendingCall(mgdScript, simplify, extPqe, tranformToCNF,
						Arrays.asList(beforeCall), call.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment,
						tfForCodeBlocks, logger, services, modifiableGlobalsOfEndProcedure, 
						xnfConversionTechnique, simplificationTechnique, symbolTable, 
						nameStartProcedure, call.getPrecedingProcedure(), call.getCallStatement().getMethodName(), nameEndProcedure, modGlobVarManager);
			} else {
				assert beforeCall == null;
				final String proc = call.getCallStatement().getMethodName();
				final UnmodifiableTransFormula oldVarsAssignment = modGlobVarManager.getOldVarsAssignment(proc);
				final UnmodifiableTransFormula globalVarsAssignment = modGlobVarManager.getGlobalVarsAssignment(proc);
				result = TransFormulaUtils.sequentialCompositionWithCallAndReturn(mgdScript, simplify, extPqe,
						tranformToCNF, call.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment,
						tfForCodeBlocks, ret.getTransitionFormula(), logger, services, 
						xnfConversionTechnique, simplificationTechnique, 
						symbolTable, modGlobVarManager.getModifiedBoogieVars(proc));
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

}
