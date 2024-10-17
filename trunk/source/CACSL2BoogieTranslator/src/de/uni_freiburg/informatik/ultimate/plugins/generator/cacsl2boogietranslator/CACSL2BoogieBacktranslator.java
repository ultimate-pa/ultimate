/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023-2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDoStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTForStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionCallExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDefinition;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIfStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTranslationUnit;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTWhileStatement;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.Multigraph;
import de.uni_freiburg.informatik.ultimate.core.lib.models.MultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.ProcedureContract;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLTransformer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Boogie2ACSL.BacktranslatedExpression;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Translation from Boogie to C for traces and expressions.
 *
 * @author dietsch@informatik.uni-freiburg.de
 */
public class CACSL2BoogieBacktranslator extends
		DefaultTranslator<BoogieASTNode, CACSLLocation, Expression, BacktranslatedExpression, String, String, ILocation> {

	/**
	 * Throw error in cases where we know that the backtranslation is not exact.
	 */
	private static final boolean DEBUG_ERROR_FOR_UNFINISHED_BACKTRANSLATION = false;

	private static final String UNFINISHED_BACKTRANSLATION = "Unfinished Backtranslation";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final LocationFactory mLocationFactory;
	private final CACSL2BoogieBacktranslatorMapping mMapping;
	private boolean mGenerateBacktranslationWarnings;
	private boolean mBacktranslationWarned;
	private final Boogie2ACSL mBoogie2ACSL;

	public CACSL2BoogieBacktranslator(final IUltimateServiceProvider services, final TypeSizes typeSizes,
			final CACSL2BoogieBacktranslatorMapping mapping, final LocationFactory locationFactory,
			final FlatSymbolTable symbolTable) {
		super(BoogieASTNode.class, CACSLLocation.class, Expression.class, BacktranslatedExpression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMapping = mapping;
		mGenerateBacktranslationWarnings = true;
		mBacktranslationWarned = false;
		mLocationFactory = locationFactory;
		mBoogie2ACSL = new Boogie2ACSL(typeSizes, mapping, symbolTable, this::reportUnfinishedBacktranslation);
	}

	@Override
	public List<CACSLLocation> translateTrace(final List<BoogieASTNode> trace) {
		// dirty but quick: convert trace to program execution
		// TODO: set the correct step info (but how?)
		// TODO: Support concurrency

		final List<AtomicTraceElement<BoogieASTNode>> ateTrace = trace.stream()
				.map(a -> new AtomicTraceElementBuilder<BoogieASTNode>()
						.setToStringFunc(BoogiePrettyPrinter.getBoogieToStringProvider()).setStepAndElement(a).build())
				.collect(Collectors.toList());
		final IProgramExecution<BoogieASTNode, Expression> tracePE =
				new BoogieProgramExecution(Collections.emptyMap(), ateTrace, false);
		final IProgramExecution<CACSLLocation, BacktranslatedExpression> translatedPE =
				translateProgramExecution(tracePE);
		final List<CACSLLocation> translatedTrace = new ArrayList<>();

		for (int i = 0; i < translatedPE.getLength(); ++i) {
			final AtomicTraceElement<CACSLLocation> ate = translatedPE.getTraceElement(i);
			// perhaps we have to skip steps here, but lets try it this way and see how it goes
			translatedTrace.add(ate.getStep());
		}
		return translatedTrace;
	}

	@Override
	public IProgramExecution<CACSLLocation, BacktranslatedExpression>
			translateProgramExecution(final IProgramExecution<BoogieASTNode, Expression> oldPE) {

		assert checkCallStackSourceProgramExecution(mLogger,
				oldPE) : "callstack of initial program execution already broken";

		// initial state
		ProgramState<BacktranslatedExpression> initialState = translateProgramState(oldPE.getInitialProgramState());

		// translate trace and program state in tandem
		final List<AtomicTraceElement<CACSLLocation>> translatedATEs = new ArrayList<>();
		final List<ProgramState<BacktranslatedExpression>> translatedProgramStates = new ArrayList<>();
		for (int i = 0; i < oldPE.getLength(); ++i) {

			final AtomicTraceElement<BoogieASTNode> ate = oldPE.getTraceElement(i);
			final ILocation loc = ate.getTraceElement().getLocation();

			final AtomicTraceElement<CACSLLocation> newAte;
			if (loc instanceof CLocation) {
				final CLocation cloc = (CLocation) loc;
				if (cloc.ignoreDuringBacktranslation()) {
					// we skip all clocs that can be ignored, i.e. things that
					// belong to internal structures
					continue;
				}

				final IASTNode cnode = cloc.getNode();

				if (cnode == null) {
					reportUnfinishedBacktranslation("Skipping invalid CLocation because IASTNode is null");
					continue;
				}

				if (cnode instanceof CASTTranslationUnit) {
					// if cnode points to the TranslationUnit, cnode should be
					// Ultimate.init or Ultimate.start and we make our
					// initial state right after them here
					// if we already have some explicit declarations, we just
					// skip the whole initial state business and use this as the
					// last normal state
					i = findMergeSequence(oldPE, i, loc);
					if (cnode instanceof CASTTranslationUnit) {
						if (!translatedATEs.isEmpty()) {
							translatedProgramStates.remove(translatedProgramStates.size() - 1);
							translatedProgramStates.add(translateProgramState(oldPE.getProgramState(i)));
						} else {
							initialState = translateProgramState(oldPE.getProgramState(i));
						}
					}
					continue;
				} else if (cnode instanceof CASTIfStatement) {
					// if cnode is an if, we point to the condition
					final CASTIfStatement ifstmt = (CASTIfStatement) cnode;
					newAte = AtomicTraceElementBuilder.fromReplaceElementAndStep(ate, (CACSLLocation) cloc)
							.setStep(mLocationFactory.createCLocation(ifstmt.getConditionExpression())).build();
				} else if (cnode instanceof CASTWhileStatement) {
					// if cnode is a while, we know that it is not ignored and that
					// it comes from the if(!cond)break; construct in Boogie.
					// we therefore invert the stepinfo, i.e. from condevaltrue
					// to condevalfalse
					newAte = handleLoopConditional(ate, cloc, ((CASTWhileStatement) cnode).getCondition());
				} else if (cnode instanceof CASTDoStatement) {
					// same as while
					newAte = handleLoopConditional(ate, cloc, ((CASTDoStatement) cnode).getCondition());
				} else if (cnode instanceof CASTForStatement) {
					// same as while
					newAte = handleLoopConditional(ate, cloc, ((CASTForStatement) cnode).getConditionExpression());
				} else if (cnode instanceof CASTFunctionCallExpression) {
					// more complex, handled separately
					i = handleCASTFunctionCallExpression(oldPE, i, (CASTFunctionCallExpression) cnode, cloc,
							translatedATEs, translatedProgramStates);
					assert translatedATEs.size() == translatedProgramStates.size();
					continue;
				} else {
					// just use as it, all special cases should have been
					// handled

					// first, check if we should merge all things in a row that point to the same
					// location, as they only contain temporary stuff
					// FIXME: merge relevance information of skipped ATEs
					i = findMergeSequence(oldPE, i, loc);

					if (ate.getTraceElement() instanceof HavocStatement && checkTempHavoc(ate)) {
						// we dont want to see no dirty temp havoc
						continue;
					}
					newAte = AtomicTraceElementBuilder.fromReplaceElementAndStep(ate, (CACSLLocation) cloc)
							.setStepInfo(StepInfo.NONE).build();
				}

			} else if (loc instanceof ACSLLocation) {
				// for now, just use ACSL as-it
				newAte = AtomicTraceElementBuilder.fromReplaceElementAndStep(ate, (CACSLLocation) loc).build();
			} else {
				// invalid location
				reportUnfinishedBacktranslation("Invalid location (Location is no CACSLLocation)");
				continue;
			}
			if (newAte != null) {
				assert checkProcedureNames(ate, newAte) : "callstack is broken";
				translatedATEs.add(newAte);
				translatedProgramStates.add(translateProgramState(oldPE.getProgramState(i)));
			}
			assert translatedATEs.size() == translatedProgramStates.size();
		}

		assert checkCallStackTarget(mLogger, translatedATEs) : "callstack broken after initial translation";

		// TODO: This is hacky because we get imprecise counterexamples for empty loops like BugForLoop01 -- the real
		// reason must be the null node itself
		// remove all ATEs where the step node is null
		final Iterator<AtomicTraceElement<CACSLLocation>> iter = translatedATEs.iterator();
		final Iterator<ProgramState<BacktranslatedExpression>> iterPs = translatedProgramStates.iterator();
		while (iter.hasNext()) {
			final CACSLLocation step = iter.next().getStep();
			final ProgramState<BacktranslatedExpression> programStateAfter = iterPs.next();
			if (!(step instanceof CLocation)) {
				continue;
			}
			final IASTNode node = ((CLocation) step).getNode();
			if (node == null) {
				mLogger.warn(
						"Removing null node from list of ATEs: ATE " + step + " program state " + programStateAfter);
				iter.remove();
				iterPs.remove();
				assert checkCallStackTarget(mLogger, translatedATEs) : "callstack broken after removal of " + node;
			}
		}

		// replace all expr eval occurences with the right atomictraceelements and return the result
		final List<AtomicTraceElement<CACSLLocation>> checkedTranslatedATEs = checkForSubtreeInclusion(translatedATEs);
		assert checkCallStackTarget(mLogger,
				checkedTranslatedATEs) : "callstack broken after subtree inclusion reduction";
		if (mBacktranslationWarned) {
			reportUnfinishedBacktranslation("The program execution was not completely translated back.");
		}
		return new CACSLProgramExecution(initialState, checkedTranslatedATEs, translatedProgramStates,
				oldPE.isConcurrent());
	}

	/**
	 * @return true if the supplied {@link AtomicTraceElement} is a havoc statement that havocs temporary variables.
	 *         Expects that ate represents a havoc statement.
	 */
	private boolean checkTempHavoc(final AtomicTraceElement<BoogieASTNode> ate) {
		final HavocStatement havoc = (HavocStatement) ate.getTraceElement();
		final CheckForTempVars check = new CheckForTempVars();
		check.processStatement(havoc);
		return check.areAllTemp();
	}

	private AtomicTraceElement<CACSLLocation> handleLoopConditional(final AtomicTraceElement<BoogieASTNode> ate,
			final CACSLLocation cloc, final IASTExpression condition) {
		final EnumSet<StepInfo> newSi = invertConditionInStepInfo(ate.getStepInfo());
		if (newSi == null) {
			return null;
		}
		final CACSLLocation step = mLocationFactory.createCLocation(condition);
		final AtomicTraceElementBuilder<CACSLLocation> builder = new AtomicTraceElementBuilder<>();

		if (ate.hasThreadId()) {
			builder.setThreadId(ate.getThreadId());
		}
		builder.setRelevanceInformation(ate.getRelevanceInformation()).setElement(cloc).setStep(step).setStepInfo(newSi)
				.setProcedures(ate.getPrecedingProcedure(), ate.getSucceedingProcedure());
		return builder.build();
	}

	/**
	 * This method converts condition eval false to condition eval true and vice versa. It is used because we translate
	 * C loop conditions to if(!cond) break; in Boogie, i.e., while in Boogie, the condition was true, in C it is false
	 * and vice versa.
	 *
	 * @param oldSiSet
	 * @return
	 */
	private EnumSet<StepInfo> invertConditionInStepInfo(final EnumSet<StepInfo> oldSiSet) {
		if (!oldSiSet.contains(StepInfo.CONDITION_EVAL_FALSE) && !oldSiSet.contains(StepInfo.CONDITION_EVAL_TRUE)) {
			reportUnfinishedBacktranslation(
					"Expected StepInfo for loop construct to contain Condition, but it did not");
			return null;
		}
		final EnumSet<StepInfo> set = EnumSet.noneOf(StepInfo.class);
		for (final StepInfo oldSi : oldSiSet) {
			switch (oldSi) {
			case CONDITION_EVAL_FALSE:
				set.add(StepInfo.CONDITION_EVAL_TRUE);
				break;
			case CONDITION_EVAL_TRUE:
				set.add(StepInfo.CONDITION_EVAL_FALSE);
				break;
			default:
				set.add(oldSi);
				break;
			}
		}
		return set;
	}

	/**
	 * If we encounter a {@link CASTFunctionCallExpression} during backtranslation, we have to consider various special
	 * cases. Sometimes we need to ignore it, sometimes we compress multiple statements to one. This function handles
	 * all these cases and returns the index the loop should increase and continue.
	 *
	 * @param programExecution
	 *            The {@link IProgramExecution} that is translated
	 * @param index
	 *            The current index
	 * @param fcall
	 *            The {@link CASTFunctionCallExpression} at the current index
	 * @param cloc
	 *            The {@link CLocation} at the current index.
	 * @param translatedAtoTraceElems
	 *            The already translated {@link AtomicTraceElement}s
	 * @param translatedProgramStates
	 *            The already translated {@link ProgramState}s
	 * @return The index with which the translation loop should continue
	 */
	private int handleCASTFunctionCallExpression(final IProgramExecution<BoogieASTNode, Expression> programExecution,
			final int index, final CASTFunctionCallExpression fcall, final CLocation cloc,
			final List<AtomicTraceElement<CACSLLocation>> translatedAtoTraceElems,
			final List<ProgramState<BacktranslatedExpression>> translatedProgramStates) {
		// directly after the function call expression we find
		// for each argument a CASTFunctionDefinition / AssignmentStatement that
		// maps the input variable to a new local one (because boogie function
		// params are immutable)
		// we throw them away
		final AtomicTraceElement<BoogieASTNode> currentATE = programExecution.getTraceElement(index);
		final BoogieASTNode currentTraceElement = currentATE.getTraceElement();

		if (!(currentTraceElement instanceof CallStatement)) {
			return handleNonCallDuringCASTFunctionCallExpression(programExecution, index, cloc, translatedAtoTraceElems,
					translatedProgramStates, currentATE, currentTraceElement);
		}

		if (currentATE.hasStepInfo(StepInfo.NONE)) {
			// this is some temp var stuff; we can safely ignore it
			return index;
		}

		if (currentATE.hasStepInfo(StepInfo.FUNC_CALL)) {
			// this is some call to read / write in our memory model during a method dispatch. We can ignore it and wait
			// for the actual call
			return index;
		}

		if (currentATE.hasStepInfo(StepInfo.PROC_CALL)) {
			// if this ATE is a call and the next valid ATE is a return,
			// the called method does not have a body and we should compress it to an FCALL
			final int nextIndex = getNextValidIndex(programExecution, index + 1);
			if (nextIndex != -1) {
				// there is a valid next ATE
				final AtomicTraceElement<BoogieASTNode> nextATE = programExecution.getTraceElement(nextIndex);
				if (nextATE.hasStepInfo(StepInfo.PROC_RETURN) && haveSameThreadId(currentATE, nextATE)) {
					assert !currentATE.hasStepInfo(StepInfo.FORK) && !nextATE.hasStepInfo(StepInfo.FORK);
					final AtomicTraceElementBuilder<CACSLLocation> ateBuilder = new AtomicTraceElementBuilder<>();
					ateBuilder.addStepInfo(StepInfo.FUNC_CALL);
					ateBuilder.setRelevanceInformation(getCombinedRelevanceInfo(currentATE, nextATE));
					ateBuilder.setStepAndElement(cloc);
					ateBuilder.setProcedures(currentATE.getPrecedingProcedure(), nextATE.getSucceedingProcedure());
					if (currentATE.hasThreadId()) {
						ateBuilder.setThreadId(currentATE.getThreadId());
					}
					translatedAtoTraceElems.add(ateBuilder.build());
					translatedProgramStates.add(translateProgramState(programExecution.getProgramState(nextIndex)));
					assert checkCallStackTarget(mLogger,
							translatedAtoTraceElems) : "callstack broken during handleCASTFunctionCallExpression";
					return nextIndex;
				}
			}
		}

		translatedAtoTraceElems
				.add(AtomicTraceElementBuilder.fromReplaceElementAndStep(currentATE, (CACSLLocation) cloc).build());
		translatedProgramStates.add(translateProgramState(programExecution.getProgramState(index)));
		assert checkCallStackTarget(mLogger,
				translatedAtoTraceElems) : "callstack broken during handleCASTFunctionCallExpression";
		return index;
	}

	private int handleNonCallDuringCASTFunctionCallExpression(
			final IProgramExecution<BoogieASTNode, Expression> programExecution, final int index, final CLocation cloc,
			final List<AtomicTraceElement<CACSLLocation>> translatedAtoTraceElems,
			final List<ProgramState<BacktranslatedExpression>> translatedProgramStates,
			final AtomicTraceElement<BoogieASTNode> currentATE, final BoogieASTNode currentTraceElement) {
		// this is some special case, e.g. an assert false or a havoc or a fork or a join
		final EnumSet<StepInfo> stepInfo;
		if (currentTraceElement instanceof AssertStatement) {
			// its an assert, keep it
			stepInfo = currentATE.getStepInfo();
		} else if (currentTraceElement instanceof HavocStatement) {
			if (checkTempHavoc(currentATE)) {
				// it is a temporary havoc, throw it away
				return index;
			}
			stepInfo = currentATE.getStepInfo();
		} else if (currentTraceElement instanceof ForkStatement) {
			// its a fork, keep it
			stepInfo = EnumSet.copyOf(currentATE.getStepInfo());
			stepInfo.add(StepInfo.FORK);
			stepInfo.add(StepInfo.FUNC_CALL);
		} else if (currentTraceElement instanceof JoinStatement) {
			// its a join, keep it
			stepInfo = EnumSet.copyOf(currentATE.getStepInfo());
			stepInfo.add(StepInfo.JOIN);
			stepInfo.add(StepInfo.FUNC_CALL);
		} else {
			// if this anything else we just throw it away
			return index;
		}
		translatedAtoTraceElems.add(AtomicTraceElementBuilder
				.fromReplaceElementAndStep(currentATE, (CACSLLocation) cloc, cloc).setStepInfo(stepInfo).build());
		translatedProgramStates.add(translateProgramState(programExecution.getProgramState(index)));
		assert checkCallStackTarget(mLogger,
				translatedAtoTraceElems) : "callstack broken during handleCASTFunctionCallExpression";
		return index;
	}

	private static boolean haveSameThreadId(final AtomicTraceElement<?>... ates) {
		if (ates == null || ates.length < 2) {
			return true;
		}
		int haveThreadId = 0;
		for (final AtomicTraceElement<?> ate : ates) {
			if (ate.hasThreadId()) {
				haveThreadId++;
			}
		}
		if (haveThreadId == 0) {
			return true;
		}
		if (haveThreadId != ates.length) {
			throw new AssertionError("Mixed AtomicTraceElements");
		}

		final int threadId = ates[0].getThreadId();
		for (final AtomicTraceElement<?> ate : ates) {
			if (threadId != ate.getThreadId()) {
				return false;
			}
		}
		return true;
	}

	private static int getNextValidIndex(final IProgramExecution<BoogieASTNode, Expression> programExecution,
			final int index) {
		for (int i = index; i < programExecution.getLength(); ++i) {
			final AtomicTraceElement<BoogieASTNode> nextATE = programExecution.getTraceElement(i);
			final ILocation loc = nextATE.getTraceElement().getLocation();
			if (!(loc instanceof CLocation)) {
				return i;
			}
			final CLocation nextcloc = (CLocation) loc;
			if (nextcloc.ignoreDuringBacktranslation()) {
				continue;
			}
			if (nextcloc.getNode() instanceof CASTTranslationUnit) {
				continue;
			}
			return i;
		}
		return -1;
	}

	/**
	 * Combine the relevance information of call and return statement. Be careful if one of them is null.
	 */
	private static IRelevanceInformation getCombinedRelevanceInfo(final AtomicTraceElement<BoogieASTNode> ate1,
			final AtomicTraceElement<BoogieASTNode> ate2) {
		final IRelevanceInformation info1 = ate1.getRelevanceInformation();
		final IRelevanceInformation info2 = ate2.getRelevanceInformation();
		if (info1 == null) {
			return info2;
		}
		if (info2 == null) {
			return info1;
		}
		return info1.merge(info2);
	}

	/**
	 * Starts from some point in the programExecution i and finds a j >= i && j < programExecution.length s.t. all
	 * elements [i..j] have the same location. If i is invalid (outside of [0..programExecution.length-1]), this method
	 * throws an IllegalArgumentException.
	 *
	 * @param programExecution
	 * @param i
	 * @param loc
	 * @return
	 */
	private static int findMergeSequence(final IProgramExecution<BoogieASTNode, Expression> programExecution,
			final int i, final ILocation loc) {
		if (i >= programExecution.getLength() || i < 0) {
			throw new IllegalArgumentException("i has an invalid value");
		}
		int j = i;
		for (; j < programExecution.getLength(); ++j) {
			// search for other nodes that have the same location in order to merge them all into one new statement
			final AtomicTraceElement<BoogieASTNode> lookahead = programExecution.getTraceElement(j);
			if (!loc.equals(lookahead.getTraceElement().getLocation())) {
				j--;
				break;
			}
		}
		// jump to the resulting statement
		if (j < programExecution.getLength()) {
			return j;
		}
		return programExecution.getLength() - 1;
	}

	@Override
	public ProgramState<BacktranslatedExpression> translateProgramState(final ProgramState<Expression> programState) {
		if (programState == null) {
			// cannot translate nothin'
			return null;
		}
		final Map<BacktranslatedExpression, Collection<BacktranslatedExpression>> translatedStateMap = new HashMap<>();
		final ProgramState<Expression> compressedProgramState = compressProgramState(programState);

		// Suppress backtranslation warnings for program states
		// We just skip variables like pointers or aux-vars in the programs states
		// TODO: This is a bit hacky, but we need to distinguish the translation of invariants and program states.
		final boolean generateOld = mGenerateBacktranslationWarnings;
		final boolean warnedOld = mBacktranslationWarned;
		mGenerateBacktranslationWarnings = false;
		for (final Expression varName : compressedProgramState.getVariables()) {
			translateProgramStateEntry(varName, compressedProgramState, translatedStateMap);
		}
		mGenerateBacktranslationWarnings = generateOld;
		mBacktranslationWarned = warnedOld;
		return new ProgramState<>(translatedStateMap, BacktranslatedExpression.class);

	}

	private void translateProgramStateEntry(final Expression varName,
			final ProgramState<Expression> compressedProgramState,
			final Map<BacktranslatedExpression, Collection<BacktranslatedExpression>> translatedStateMap) {
		// first, translate name
		final BacktranslatedExpression newVarName = translateExpressionForProgramState(varName);
		if (newVarName == null) {
			return;
		}
		// then, translate values
		final Collection<Expression> varValues = compressedProgramState.getValues(varName);
		final Collection<BacktranslatedExpression> newVarValues = new ArrayList<>();
		for (final Expression varValue : varValues) {
			final BacktranslatedExpression newVarValue = translateExpressionForProgramState(varValue);
			if (newVarValue != null) {
				newVarValues.add(newVarValue);
			}
		}

		// finally, merge with possibly existing values for this name
		if (!newVarValues.isEmpty()) {
			final Collection<BacktranslatedExpression> oldVarValues = translatedStateMap.put(newVarName, newVarValues);
			if (oldVarValues != null) {
				newVarValues.addAll(oldVarValues);
			}
		}
	}

	/**
	 * Replace base and offset with one {@link TemporaryPointerExpression}
	 *
	 * @param programState
	 *            May not be null
	 */
	private ProgramState<Expression> compressProgramState(final ProgramState<Expression> programState) {
		final List<Pair<Expression, Collection<Expression>>> oldEntries = new ArrayList<>();
		final List<Pair<Expression, Collection<Expression>>> newEntries = new ArrayList<>();

		for (final Expression var : programState.getVariables()) {
			final Pair<Expression, Collection<Expression>> entry = new Pair<>(var, programState.getValues(var));
			oldEntries.add(entry);
		}

		int x = -1;
		int y = 0;
		while (x < y) {
			// collect all pointer
			x = newEntries.size();
			extractTemporaryPointerExpression(oldEntries, newEntries);
			y = newEntries.size();
		}

		newEntries.addAll(oldEntries);
		final Map<Expression, Collection<Expression>> map = new HashMap<>();
		for (final Pair<Expression, Collection<Expression>> entry : newEntries) {
			final Collection<Expression> newValues = entry.getSecond();
			final Collection<Expression> oldValues = map.put(entry.getFirst(), entry.getSecond());
			if (oldValues != null) {
				newValues.addAll(oldValues);
			}
		}

		return new ProgramState<>(map, Expression.class);
	}

	private void extractTemporaryPointerExpression(final List<Pair<Expression, Collection<Expression>>> oldEntries,
			final List<Pair<Expression, Collection<Expression>>> newEntries) {
		for (int i = oldEntries.size() - 1; i >= 0; i--) {
			final Pair<Expression, Collection<Expression>> entry = oldEntries.get(i);

			boolean isPointerBase = false;
			boolean isOld = false;
			if (isPointerBase(entry.getFirst())) {
				isPointerBase = true;
				isOld = false;
			} else if (isOldPointerBase(entry.getFirst())) {
				isPointerBase = true;
				isOld = true;
			}
			if (isPointerBase) {
				final String name = getPointerName(entry.getFirst(), isOld);
				for (int j = oldEntries.size() - 1; j >= 0; j--) {
					final Pair<Expression, Collection<Expression>> otherentry = oldEntries.get(j);
					if (!isPointerOffsetFor(otherentry.getFirst(), name, isOld)) {
						continue;
					}
					final Expression tmpPointerVar = assemblePointer(entry.getFirst(), otherentry.getFirst(), isOld);

					if (entry.getSecond().size() != 1 || otherentry.getSecond().size() != 1) {
						reportUnfinishedBacktranslation("Pointers with multiple values");
					}
					final var valueBase = DataStructureUtils.getOneAndOnly(entry.getSecond(), "pointer base");
					final var valueOffset = DataStructureUtils.getOneAndOnly(otherentry.getSecond(), "pointer offset");
					final TemporaryPointerExpression tmpPointerValue =
							new TemporaryPointerExpression(entry.getFirst().getLocation(), valueBase, valueOffset);

					final Pair<Expression, Collection<Expression>> newEntry =
							new Pair<>(tmpPointerVar, new ArrayList<>());
					newEntry.getSecond().add(tmpPointerValue);
					newEntries.add(newEntry);
					oldEntries.remove(entry);
					oldEntries.remove(otherentry);
					return;
				}
			}
		}
	}

	private static boolean isPointerBase(final Expression expr) {
		if (expr instanceof IdentifierExpression) {
			return ((IdentifierExpression) expr).getIdentifier().endsWith(SFO.POINTER_BASE);
		}
		return false;
	}

	private static boolean isOldPointerBase(final Expression expr) {
		if (expr instanceof UnaryExpression) {
			return ((UnaryExpression) expr).getOperator() == Operator.OLD
					&& isPointerBase(((UnaryExpression) expr).getExpr());
		}
		return false;
	}

	private static boolean isPointerOffsetFor(final Expression expr, final String name, final boolean isOld) {
		if (isOld && expr instanceof UnaryExpression) {
			final var uexp = (UnaryExpression) expr;
			return uexp.getOperator() == Operator.OLD && isPointerOffsetFor(uexp.getExpr(), name, false);
		}
		if (!isOld && expr instanceof IdentifierExpression) {
			final var identifier = ((IdentifierExpression) expr).getIdentifier();
			return identifier.startsWith(name) && identifier.endsWith(SFO.POINTER_OFFSET);
		}
		return false;
	}

	private static String getPointerName(final Expression base, final boolean isOld) {
		if (isOld) {
			return getPointerName(((UnaryExpression) base).getExpr(), false);
		}
		final String baseName = ((IdentifierExpression) base).getIdentifier();
		return baseName.substring(0, baseName.length() - SFO.POINTER_BASE.length());
	}

	private Expression assemblePointer(final Expression base, final Expression offset, final boolean isOld) {
		if (isOld) {
			return new UnaryExpression(base.getLoc(), Operator.OLD,
					assemblePointer(((UnaryExpression) base).getExpr(), ((UnaryExpression) offset).getExpr(), false));
		}
		return new TemporaryPointerExpression(base.getLoc(), base, offset);
	}

	@Override
	public IBacktranslatedCFG<String, CACSLLocation> translateCFG(final IBacktranslatedCFG<String, BoogieASTNode> cfg) {
		// mLogger.info("################# Input: " + cfg.getClass().getSimpleName());
		// printHondas(cfg, mLogger::info);
		// printCFG(cfg, mLogger::info);
		final boolean oldValue = mGenerateBacktranslationWarnings;
		mGenerateBacktranslationWarnings = false;
		IBacktranslatedCFG<String, CACSLLocation> translated = translateCFG(cfg, (a, b, c) -> translateCFGEdge(a, b, c),
				(a, b, c) -> new CACSLBacktranslatedCFG(a, b, c, mLogger, mServices));
		translated = reduceCFGs(translated);
		// mLogger.info("################# Output: " + translated.getClass().getSimpleName());
		// printHondas(translated, mLogger::info);
		// printCFG(translated, mLogger::info);
		mGenerateBacktranslationWarnings = oldValue;
		return translated;
	}

	@SuppressWarnings("unchecked")
	private <TVL, SVL> Multigraph<TVL, CACSLLocation> translateCFGEdge(
			final Map<IExplicitEdgesMultigraph<?, ?, SVL, ? extends BoogieASTNode, ?>, Multigraph<TVL, CACSLLocation>> cache,
			final IMultigraphEdge<?, ?, ?, BoogieASTNode, ?> oldEdge,
			final Multigraph<TVL, CACSLLocation> newSourceNode) {

		final IExplicitEdgesMultigraph<?, ?, SVL, BoogieASTNode, ?> oldTarget =
				(IExplicitEdgesMultigraph<?, ?, SVL, BoogieASTNode, ?>) oldEdge.getTarget();
		final Multigraph<TVL, CACSLLocation> currentSource = newSourceNode;

		Multigraph<TVL, CACSLLocation> lastTarget = cache.get(oldTarget);
		if (lastTarget == null) {
			lastTarget = (Multigraph<TVL, CACSLLocation>) createLabeledWitnessNode(oldTarget);
			cache.put(oldTarget, lastTarget);
		}
		final BoogieASTNode label = oldEdge.getLabel();
		if (label == null) {
			new MultigraphEdge<>(currentSource, null, lastTarget);
			return lastTarget;
		}

		final ILocation loc = label.getLocation();
		final ConditionAnnotation coan = ConditionAnnotation.getAnnotation(oldEdge);
		createCFGMultigraphEdge(currentSource, loc, lastTarget, coan != null && coan.isNegated());
		return lastTarget;
	}

	@Override
	public ProcedureContract<BacktranslatedExpression, BacktranslatedExpression> translateProcedureContract(
			final ProcedureContract<Expression, ? extends Expression> oldContract, final ILocation context) {
		if (context instanceof CACSLLocation && ((CACSLLocation) context).ignoreDuringBacktranslation()) {
			return null;
		}

		final var newRequires = oldContract.getRequires() == null ? null
				: translateExpressionWithContext(oldContract.getRequires(), context);

		// Use special method that translates Boogie's modifies clauses into additional conjuncts in "ensures".
		final var newEnsures = mBoogie2ACSL.translateEnsuresExpression(oldContract.getEnsures(), context,
				(Set<IdentifierExpression>) oldContract.getModifies());

		// Create a new contract without modifies clause.
		return new ProcedureContract<>(oldContract.getProcedure(), newRequires, newEnsures);
	}

	private <TVL> void createCFGMultigraphEdge(final Multigraph<TVL, CACSLLocation> currentSource, final ILocation loc,
			final Multigraph<TVL, CACSLLocation> lastTarget, final boolean isNegated) {
		final MultigraphEdge<TVL, CACSLLocation> edge;
		if (loc instanceof CLocation) {
			final CLocation cloc = (CLocation) loc;
			if (cloc.ignoreDuringBacktranslation()) {
				// we skip all clocs that can be ignored, i.e. things that
				// belong to internal structures
				edge = new MultigraphEdge<>(currentSource, null, lastTarget);
			} else {
				final IASTNode cnode = cloc.getNode();
				if (cnode == null) {
					reportUnfinishedBacktranslation("Skipping invalid CLocation because IASTNode is null");
					edge = new MultigraphEdge<>(currentSource, null, lastTarget);
				} else if (cnode instanceof CASTTranslationUnit) {
					edge = new MultigraphEdge<>(currentSource, null, lastTarget);
				} else if (cnode instanceof CASTIfStatement) {
					final CASTIfStatement ifstmt = (CASTIfStatement) cnode;
					edge = new MultigraphEdge<>(currentSource,
							mLocationFactory.createCLocation(ifstmt.getConditionExpression()), lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTWhileStatement) {
					final CASTWhileStatement whileStmt = (CASTWhileStatement) cnode;
					edge = new MultigraphEdge<>(currentSource,
							mLocationFactory.createCLocation(whileStmt.getCondition()), lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTDoStatement) {
					// same as while
					final CASTDoStatement doStmt = (CASTDoStatement) cnode;
					edge = new MultigraphEdge<>(currentSource, mLocationFactory.createCLocation(doStmt.getCondition()),
							lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTForStatement) {
					// same as while
					final CASTForStatement forStmt = (CASTForStatement) cnode;
					edge = new MultigraphEdge<>(currentSource,
							mLocationFactory.createCLocation(forStmt.getConditionExpression()), lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTFunctionCallExpression) {
					edge = new MultigraphEdge<>(currentSource, cloc, lastTarget);
				} else if (cnode instanceof CASTFunctionDefinition) {
					edge = new MultigraphEdge<>(currentSource, null, lastTarget);
				} else {
					edge = new MultigraphEdge<>(currentSource, cloc, lastTarget);
				}
			}
		} else if (loc instanceof ACSLLocation) {
			final ACSLLocation aloc = (ACSLLocation) loc;
			edge = new MultigraphEdge<>(currentSource, aloc, lastTarget);
		} else {
			// invalid location
			reportUnfinishedBacktranslation("Invalid location (Location is no CACSLLocation)");
			edge = new MultigraphEdge<>(currentSource, null, lastTarget);
		}
	}

	private IBacktranslatedCFG<String, CACSLLocation>
			reduceCFGs(final IBacktranslatedCFG<String, CACSLLocation> translated) {
		for (final IExplicitEdgesMultigraph<?, ?, String, CACSLLocation, ?> root : translated.getCFGs()) {
			reduceCFG(root);
		}
		return translated;
	}

	@SuppressWarnings("unchecked")
	private void reduceCFG(final IExplicitEdgesMultigraph<?, ?, String, CACSLLocation, ?> root) {
		final Deque<Multigraph<String, CACSLLocation>> worklist = new ArrayDeque<>();
		final Set<IExplicitEdgesMultigraph<?, ?, String, CACSLLocation, ?>> closed = new HashSet<>();
		int i = 0;
		worklist.add((Multigraph<String, CACSLLocation>) root);
		while (!worklist.isEmpty()) {
			final Multigraph<String, CACSLLocation> current = worklist.remove();
			if (!closed.add(current)) {
				continue;
			}

			for (final MultigraphEdge<String, CACSLLocation> outEdge : new ArrayList<>(current.getOutgoingEdges())) {
				final Multigraph<String, CACSLLocation> target = outEdge.getTarget();
				final List<MultigraphEdge<String, CACSLLocation>> targetOutEdges = target.getOutgoingEdges();
				if (target.getLabel() == null && target.getIncomingEdges().size() == 1) {
					// remove target and outedge if target is not labeled and has only one incoming edge and ....
					if (outEdge.getLabel() == null || targetOutEdges.size() == 1
							&& outEdge.getLabel().equals(targetOutEdges.get(0).getLabel())) {
						++i;
						// ... this edge is unlabeled (i.e., a skip), or
						// ... the only outgoing edge from target is identically labeled (i.e., there was a
						// duplication). Also, remove outedge.
						outEdge.disconnectSource();
						outEdge.disconnectTarget();
						for (final MultigraphEdge<String, CACSLLocation> out : new ArrayList<>(targetOutEdges)) {
							out.redirectSource(current);
						}
					}
				}

				if (outEdge.getLabel() == null && target.getIncomingEdges().size() > 1
						&& current.getOutgoingEdges().size() > 1) {
					// remove outEdge if it has no label and the target wont get disconnected and the source wont become
					// a sink
					outEdge.disconnectSource();
					outEdge.disconnectTarget();
				}
			}

			for (final MultigraphEdge<String, CACSLLocation> out : current.getOutgoingEdges()) {
				worklist.add(out.getTarget());
			}
		}
		if (i > 0) {
			mLogger.info("Reduced CFG by removing " + i + " nodes and edges");
			reduceCFG(root);
		}
	}

	private BacktranslatedExpression translateExpressionForProgramState(final Expression expression) {
		// Translate TemporaryPointerExpression properly
		if (expression instanceof TemporaryPointerExpression) {
			final TemporaryPointerExpression pointer = (TemporaryPointerExpression) expression;
			final Expression base = pointer.mBase;
			if (base instanceof IdentifierExpression) {
				final IdentifierExpression id = (IdentifierExpression) base;
				final String name = id.getIdentifier();
				// If the base is of the form a!base, just translate a accordingly
				if (name.endsWith(SFO.POINTER_BASE)) {
					final String originalName = name.substring(0, name.length() - SFO.POINTER_BASE.length() - 1);
					return translateExpression(new IdentifierExpression(id.getLoc(), id.getType(), originalName,
							id.getDeclarationInformation()));
				}
			}
			// Otherwise create a value like {base:offset}
			// This is not a real ACSL-expression, so we wrap it into FakeAcslPointerExpression
			return new BacktranslatedExpression(
					new FakeAcslPointerExpression(translateExpression(base), translateExpression(pointer.mOffset)));
		}
		return translateExpression(expression);
	}

	@Override
	public BacktranslatedExpression translateExpressionWithContext(final Expression expression,
			final ILocation context) {
		if (context instanceof CACSLLocation && ((CACSLLocation) context).ignoreDuringBacktranslation()) {
			return null;
		}
		return mBoogie2ACSL.translateExpression(expression, context);
	}

	@Override
	public BacktranslatedExpression translateExpression(final Expression expression) {
		return translateExpressionWithContext(expression, null);
	}

	private void reportUnfinishedBacktranslation(final String message) {
		if (DEBUG_ERROR_FOR_UNFINISHED_BACKTRANSLATION) {
			throw new AssertionError(UNFINISHED_BACKTRANSLATION + ": " + message);
		}
		mBacktranslationWarned = true;
		if (!mGenerateBacktranslationWarnings) {
			return;
		}
		final String fullMessage = UNFINISHED_BACKTRANSLATION + ": " + message;
		mLogger.warn(fullMessage);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new GenericResult(Activator.PLUGIN_ID, UNFINISHED_BACKTRANSLATION, fullMessage, Severity.WARNING));
	}

	private static IRelevanceInformation mergeRelevaneInformation(final IRelevanceInformation... relInfos) {
		if (relInfos == null || relInfos.length == 0) {
			return null;
		}
		if (relInfos.length == 1) {
			return relInfos[0];
		}
		return Arrays.stream(relInfos).filter(a -> a != null).reduce(null, (a, b) -> (a == null ? b : a.merge(b)));
	}

	/**
	 * A subtree check that sacrifices memory consumption for speed. It is about 20x faster, but uses a lookup table. A
	 * subtree check is used to determine if a trace element is actually a nesting of some later trace element in the
	 * error path (like in x = x++ + ++x, were x++ and ++x are nestings of +, and + is a nesting of the assignment).
	 * There may be a better solution to this (its rather expensive).
	 */
	protected static List<AtomicTraceElement<CACSLLocation>>
			checkForSubtreeInclusion(final List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements) {

		// first, compute lookup data structure
		final Map<AtomicTraceElement<CACSLLocation>, Set<IASTNode>> ateToParents = new HashMap<>();
		for (final AtomicTraceElement<CACSLLocation> ate : translatedAtomicTraceElements) {
			if (!(ate.getStep() instanceof CLocation)) {
				continue;
			}
			final IASTNode origNode = ((CLocation) ate.getStep()).getNode();
			final Set<IASTNode> parents = new HashSet<>();

			IASTNode currentParent = origNode.getParent();
			while (currentParent != null) {
				parents.add(currentParent);
				currentParent = currentParent.getParent();
			}

			ateToParents.put(ate, parents);
		}

		// second, compute actual tree inclusion check
		final List<AtomicTraceElement<CACSLLocation>> rtr = new ArrayList<>();
		for (int i = 0; i < translatedAtomicTraceElements.size(); ++i) {
			final AtomicTraceElement<CACSLLocation> ate = translatedAtomicTraceElements.get(i);
			final AtomicTraceElement<CACSLLocation> currentResult = checkForSubtreeInclusion(ate,
					translatedAtomicTraceElements, i + 1, StepInfo.EXPR_EVAL, ateToParents);
			rtr.add(currentResult);
		}
		return rtr;
	}

	private static AtomicTraceElement<CACSLLocation> checkForSubtreeInclusion(
			final AtomicTraceElement<CACSLLocation> ate,
			final List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements, final int start,
			final StepInfo newSi, final Map<AtomicTraceElement<CACSLLocation>, Set<IASTNode>> ateToParents) {

		final Set<IASTNode> parents = ateToParents.get(ate);

		if (parents == null) {
			// not implemented for ACSL
			return ate;
		}
		final IASTNode origNode = ((CLocation) ate.getStep()).getNode();

		if (!(origNode instanceof IASTExpression)) {
			// do nothing for statements
			return ate;
		}

		for (int j = start; j < translatedAtomicTraceElements.size(); ++j) {
			final AtomicTraceElement<CACSLLocation> current = translatedAtomicTraceElements.get(j);
			if (!(current.getStep() instanceof CLocation)) {
				// skip acsl nodes
				continue;
			}

			final IASTNode candidate = ((CLocation) current.getStep()).getNode();
			if (parents.contains(candidate)) {
				if (current.hasThreadId() || ate.hasThreadId()) {
					if (!current.hasThreadId() || !ate.hasThreadId()) {
						throw new AssertionError("Mixing concurrent and sequential program executions is not allowed");
					}
					if (current.getThreadId() != ate.getThreadId()) {
						// "Interleaving expression evaluation"
						return ate;
					}
				}
				EnumSet<StepInfo> set = ate.getStepInfo();
				if (set.isEmpty() || set.contains(StepInfo.NONE)) {
					set = EnumSet.of(newSi);
				} else {
					set.add(newSi);
				}

				return AtomicTraceElementBuilder.from(ate).setElement(current.getStep()).setStep(ate.getStep())
						.setStepInfo(set)
						.setRelevanceInformation(mergeRelevaneInformation(ate.getRelevanceInformation(),
								current.getRelevanceInformation()))
						.build();
			}
		}
		return ate;
	}

	@Override
	protected void printBrokenCallStackSource(final List<AtomicTraceElement<BoogieASTNode>> trace, final int i) {
		mLogger.fatal(new ProgramExecutionFormatter<>(new BoogieBacktranslationValueProvider())
				.formatProgramExecution(new BoogieProgramExecution(trace.subList(0, i), false)));
	}

	@Override
	protected void printBrokenCallStackTarget(final List<AtomicTraceElement<CACSLLocation>> trace, final int i) {
		mLogger.fatal(new ProgramExecutionFormatter<>(new CACSLBacktranslationValueProvider())
				.formatProgramExecution(new CACSLProgramExecution(trace.subList(0, i), false)));
	}

	private class CheckForTempVars extends BoogieTransformer {

		private boolean mAllAreTemp = true;

		protected boolean areAllTemp() {
			return mAllAreTemp;
		}

		@Override
		protected Statement processStatement(final Statement statement) {
			return super.processStatement(statement);
		}

		@Override
		protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
			if (lhs instanceof VariableLHS) {
				mAllAreTemp = mAllAreTemp && isTempVar(((VariableLHS) lhs).getIdentifier());
			}
			return super.processLeftHandSide(lhs);
		}

		private boolean isTempVar(final String identifier) {
			return mMapping.isTempVar(identifier);
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				mAllAreTemp = mAllAreTemp && isTempVar(((IdentifierExpression) expr).getIdentifier());
			}
			return super.processExpression(expr);
		}
	}

	private static class TemporaryPointerExpression extends Expression {

		private static final long serialVersionUID = 1L;
		private final Expression mBase;
		private final Expression mOffset;

		public TemporaryPointerExpression(final ILocation loc, final Expression base, final Expression offset) {
			super(loc);
			mBase = base;
			mOffset = offset;
		}

		@Override
		public String toString() {
			return mBase.toString() + " " + mOffset.toString();
		}

		@Override
		public void accept(final GeneratedBoogieAstVisitor visitor) {
			// nothing to accept here
		}

		@Override
		public Expression accept(final GeneratedBoogieAstTransformer visitor) {
			return null;
		}
	}

	private static class FakeAcslPointerExpression
			extends de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression {
		private final BacktranslatedExpression mBase;
		private final BacktranslatedExpression mOffset;

		public FakeAcslPointerExpression(final BacktranslatedExpression base, final BacktranslatedExpression offset) {
			mBase = base;
			mOffset = offset;
		}

		@Override
		public String toString() {
			return "{" + mBase + ":" + mOffset + "}";
		}

		@Override
		public void accept(final ACSLVisitor visitor) {
			// nothing to accept here

		}

		@Override
		public de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression accept(final ACSLTransformer visitor) {
			return null;
		}

	}
}
