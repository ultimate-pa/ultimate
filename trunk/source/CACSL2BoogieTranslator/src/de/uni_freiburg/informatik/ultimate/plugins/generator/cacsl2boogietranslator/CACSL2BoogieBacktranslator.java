/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.math.BigDecimal;
import java.math.BigInteger;
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

import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDoStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTForStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionCallExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDefinition;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIfStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTranslationUnit;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTWhileStatement;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.Multigraph;
import de.uni_freiburg.informatik.ultimate.core.lib.models.MultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Translation from Boogie to C for traces and expressions.
 *
 * @author dietsch@informatik.uni-freiburg.de
 */
public class CACSL2BoogieBacktranslator
		extends DefaultTranslator<BoogieASTNode, CACSLLocation, Expression, IASTExpression, String, String> {

	/**
	 * {@link VariableType} is used to distinguish various special variables after they are converted to strings.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private enum VariableType {
		RESULT,

		OLD,

		INVAR,

		NORMAL,

		AUX,

		VALID,

		POINTER_BASE,

		POINTER_OFFSET,

		UNKNOWN
	}

	private static final String UNFINISHED_BACKTRANSLATION = "Unfinished Backtranslation";

	private final Boogie2C mBoogie2C;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private AExpressionTranslation mExpressionTranslation;
	private boolean mGenerateBacktranslationWarnings;
	private LocationFactory mLocationFactory;

	public CACSL2BoogieBacktranslator(final IUltimateServiceProvider services) {
		super(BoogieASTNode.class, CACSLLocation.class, Expression.class, IASTExpression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBoogie2C = new Boogie2C();
		mGenerateBacktranslationWarnings = true;
	}

	public void setExpressionTranslation(final AExpressionTranslation expressionTranslation) {
		mExpressionTranslation = expressionTranslation;
	}

	public void setLocationFactory(final LocationFactory locationFactory) {
		mLocationFactory = locationFactory;
	}

	@Override
	public List<CACSLLocation> translateTrace(final List<BoogieASTNode> trace) {
		// dirty but quick: convert trace to program execution
		// TODO: set the correct step info (but how?)
		final List<AtomicTraceElement<BoogieASTNode>> ateTrace = trace.stream()
				.map(a -> new AtomicTraceElement<>(a, BoogiePrettyPrinter.getBoogieToStringprovider(), null))
				.collect(Collectors.toList());
		final IProgramExecution<BoogieASTNode, Expression> tracePE =
				new BoogieProgramExecution(Collections.emptyMap(), ateTrace);
		final IProgramExecution<CACSLLocation, IASTExpression> translatedPE = translateProgramExecution(tracePE);
		final List<CACSLLocation> translatedTrace = new ArrayList<>();

		for (int i = 0; i < translatedPE.getLength(); ++i) {
			final AtomicTraceElement<CACSLLocation> ate = translatedPE.getTraceElement(i);
			// perhaps we have to skip steps here, but lets try it this way and see how it goes
			translatedTrace.add(ate.getStep());
		}
		return translatedTrace;
	}

	@Override
	public IProgramExecution<CACSLLocation, IASTExpression>
			translateProgramExecution(final IProgramExecution<BoogieASTNode, Expression> oldPE) {

		// initial state
		ProgramState<IASTExpression> initialState = translateProgramState(oldPE.getInitialProgramState());

		// translate trace and program state in tandem
		final List<AtomicTraceElement<CACSLLocation>> translatedATEs = new ArrayList<>();
		final List<ProgramState<IASTExpression>> translatedProgramStates = new ArrayList<>();
		for (int i = 0; i < oldPE.getLength(); ++i) {

			final AtomicTraceElement<BoogieASTNode> ate = oldPE.getTraceElement(i);
			final ILocation loc = ate.getTraceElement().getLocation();

			if (loc instanceof CLocation) {
				final CLocation cloc = (CLocation) loc;
				if (cloc.ignoreDuringBacktranslation()) {
					// we skip all clocs that can be ignored, i.e. things that
					// belong to internal structures
					continue;
				}

				final IASTNode cnode = cloc.getNode();

				if (cnode == null) {
					reportUnfinishedBacktranslation(
							UNFINISHED_BACKTRANSLATION + ": Skipping invalid CLocation because IASTNode is null");
					continue;
				}

				final AtomicTraceElement<CACSLLocation> newAte;
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
					newAte = new AtomicTraceElement<>(cloc,
							mLocationFactory.createCLocation(ifstmt.getConditionExpression()), ate.getStepInfo(),
							ate.getRelevanceInformation());
				} else if (cnode instanceof CASTWhileStatement) {
					// if cnode is a while, we know that it is not ignored and that
					// it comes from the if(!cond)break; construct in Boogie.
					// we therefore invert the stepinfo, i.e. from condevaltrue
					// to condevalfalse
					newAte = handleConditional(ate, cloc, ((CASTWhileStatement) cnode).getCondition());
				} else if (cnode instanceof CASTDoStatement) {
					// same as while
					newAte = handleConditional(ate, cloc, ((CASTDoStatement) cnode).getCondition());
				} else if (cnode instanceof CASTForStatement) {
					// same as while
					newAte = handleConditional(ate, cloc, ((CASTForStatement) cnode).getConditionExpression());
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
					newAte = new AtomicTraceElement<>(cloc, cloc, ate.getStepInfo(), ate.getRelevanceInformation(),
							ate.getPrecedingProcedure(), ate.getSucceedingProcedure());
				}
				if (newAte != null) {
					translatedATEs.add(newAte);
					translatedProgramStates.add(translateProgramState(oldPE.getProgramState(i)));
				}

			} else if (loc instanceof ACSLLocation) {
				// for now, just use ACSL as-it
				translatedATEs
						.add(new AtomicTraceElement<CACSLLocation>((ACSLLocation) loc, ate.getRelevanceInformation()));
				translatedProgramStates.add(translateProgramState(oldPE.getProgramState(i)));

			} else {
				// invalid location
				reportUnfinishedBacktranslation(
						UNFINISHED_BACKTRANSLATION + ": Invalid location (Location is no CACSLLocation)");
			}
			assert translatedATEs.size() == translatedProgramStates.size();
		}

		// TODO: This is hacky because we get imprecise counterexamples for empty loops like BugForLoop01 -- the real
		// reason must be the null node itself
		// remove all ATEs where the step node is null

		final Iterator<AtomicTraceElement<CACSLLocation>> iter = translatedATEs.iterator();
		final Iterator<ProgramState<IASTExpression>> iterPs = translatedProgramStates.iterator();
		while (iter.hasNext()) {
			final CACSLLocation step = iter.next().getStep();
			final ProgramState<IASTExpression> programStateAfter = iterPs.next();
			if (!(step instanceof CLocation)) {
				continue;
			}
			final IASTNode node = ((CLocation) step).getNode();
			if (node == null) {
				mLogger.warn(
						"Removing null node from list of ATEs: ATE " + step + " program state " + programStateAfter);
				iter.remove();
				iterPs.remove();
			}
		}

		// replace all expr eval occurences with the right atomictraceelements and return the result
		final List<AtomicTraceElement<CACSLLocation>> checkedTranslatedATEs = checkForSubtreeInclusion(translatedATEs);
		return new CACSLProgramExecution(initialState, checkedTranslatedATEs, translatedProgramStates, mLogger,
				mServices);
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

	private AtomicTraceElement<CACSLLocation> handleConditional(final AtomicTraceElement<BoogieASTNode> ate,
			final CACSLLocation cloc, final IASTExpression condition) {
		final EnumSet<StepInfo> newSi = invertConditionInStepInfo(ate.getStepInfo());
		if (newSi == null) {
			return null;
		}
		return new AtomicTraceElement<>(cloc, mLocationFactory.createCLocation(condition), newSi,
				ate.getRelevanceInformation());
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
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION
					+ ": Expected StepInfo for loop construct to contain Condition, but it did not");
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
	 * cases. Sometimes we need to ignore it, sometimes we compress multiple statements to one.
	 *
	 * This function handles all these cases and returns the index the loop should increase and continue.
	 *
	 * @param programExecution
	 *            The {@link IProgramExecution} that is translated
	 * @param index
	 *            The current index
	 * @param fcall
	 *            The {@link CASTFunctionCallExpression} at the current index
	 * @param cloc
	 *            The {@link CLocation} at the current index.
	 * @param translatedAtomicTraceElements
	 *            The already translated {@link AtomicTraceElement}s
	 * @param translatedProgramStates
	 *            The already translated {@link ProgramState}s
	 * @return The index with which the translation loop should continue
	 */
	private int handleCASTFunctionCallExpression(final IProgramExecution<BoogieASTNode, Expression> programExecution,
			final int index, final CASTFunctionCallExpression fcall, final CLocation cloc,
			final List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements,
			final List<ProgramState<IASTExpression>> translatedProgramStates) {
		// directly after the function call expression we find
		// for each argument a CASTFunctionDefinition / AssignmentStatement that
		// maps the input variable to a new local one (because boogie function
		// params are immutable)
		// we throw them away
		final AtomicTraceElement<BoogieASTNode> currentATE = programExecution.getTraceElement(index);
		final BoogieASTNode currentTraceElement = currentATE.getTraceElement();

		if (!(currentTraceElement instanceof CallStatement)) {
			// this is some special case, e.g. an assert false or an havoc
			if (currentTraceElement instanceof AssertStatement) {
				translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc,
						currentATE.getStepInfo(), currentATE.getRelevanceInformation()));
				translatedProgramStates.add(translateProgramState(programExecution.getProgramState(index)));
				return index;
			} else if (currentTraceElement instanceof HavocStatement) {
				if (!checkTempHavoc(currentATE)) {
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc,
							currentATE.getStepInfo(), currentATE.getRelevanceInformation()));
					translatedProgramStates.add(translateProgramState(programExecution.getProgramState(index)));
					return index;
				}
			}
			// if this anything else we just throw it away
			return index;
		}

		if (currentATE.hasStepInfo(StepInfo.NONE)) {
			// this is some temp var stuff; we can safely ignore it
			return index;
		}

		if (index + 1 < programExecution.getLength()) {
			// if the next ATE is a return, the called method does not have a body and we should compress it to an
			// FCALL
			int i = index + 1;
			for (; i < programExecution.getLength(); ++i) {
				final ILocation loc = programExecution.getTraceElement(i).getTraceElement().getLocation();
				if (!(loc instanceof CLocation)) {
					break;
				}
				final CLocation nextcloc = (CLocation) loc;
				if (nextcloc.ignoreDuringBacktranslation()) {
					continue;
				}
				if (nextcloc.getNode() instanceof CASTTranslationUnit) {
					continue;
				}
				break;
			}
			if (i < programExecution.getLength()) {
				final AtomicTraceElement<BoogieASTNode> nextATE = programExecution.getTraceElement(i);
				if (nextATE.hasStepInfo(StepInfo.PROC_RETURN)) {
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc,
							StepInfo.FUNC_CALL, currentATE.getRelevanceInformation(),
							currentATE.getPrecedingProcedure(), currentATE.getPrecedingProcedure()));
					translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));
					return i;
				}
			}
		}

		final EnumSet<StepInfo> stepInfo = currentATE.getStepInfo();
		if (currentATE.hasStepInfo(StepInfo.PROC_RETURN)) {
			// we have to modify the previous statement in the translated list s.t it is the actual return and remove
			// the return stepinfo from this statement.
			stepInfo.remove(StepInfo.PROC_RETURN);
			final AtomicTraceElement<CACSLLocation> last =
					translatedAtomicTraceElements.remove(translatedAtomicTraceElements.size() - 1);
			final EnumSet<StepInfo> newStepInfo = EnumSet.copyOf(last.getStepInfo());
			newStepInfo.remove(StepInfo.NONE);
			newStepInfo.add(StepInfo.PROC_RETURN);
			final AtomicTraceElement<CACSLLocation> newLast = new AtomicTraceElement<>(last.getTraceElement(),
					last.getStep(), newStepInfo, last.getRelevanceInformation(), currentATE.getPrecedingProcedure(),
					currentATE.getSucceedingProcedure());
			translatedAtomicTraceElements.add(newLast);
		}

		translatedAtomicTraceElements
				.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc, stepInfo, currentATE.getRelevanceInformation(),
						currentATE.getPrecedingProcedure(), currentATE.getSucceedingProcedure()));
		translatedProgramStates.add(translateProgramState(programExecution.getProgramState(index)));
		return index;
	}

	/**
	 * Starts from some point in the programExecution i and finds a j >= i && j < programExecution.length s.t. all
	 * elements [i..j] have the same location.
	 *
	 * If i is invalid (outside of [0..programExecution.length-1]), this method throws an IllegalArgumentException.
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
			if (!lookahead.getTraceElement().getLocation().equals(loc)) {
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
	public ProgramState<IASTExpression> translateProgramState(final ProgramState<Expression> programState) {
		if (programState == null) {
			// cannot translate nothin'
			return null;
		}
		final Map<IASTExpression, Collection<IASTExpression>> translatedStateMap = new HashMap<>();
		final ProgramState<Expression> compressedProgramState = compressProgramState(programState);

		for (final Expression varName : compressedProgramState.getVariables()) {
			translateProgramStateEntry(varName, compressedProgramState, translatedStateMap);
		}
		if (translatedStateMap.isEmpty()) {
			return null;
		}
		return new ProgramState<>(translatedStateMap);

	}

	private void translateProgramStateEntry(final Expression varName,
			final ProgramState<Expression> compressedProgramState,
			final Map<IASTExpression, Collection<IASTExpression>> translatedStateMap) {
		// first, translate name
		final IASTExpression newVarName = translateExpression(varName);
		if (newVarName == null) {
			return;
		}
		final CType cType;
		if (newVarName instanceof FakeExpression) {
			cType = ((FakeExpression) newVarName).getCType();
		} else {
			cType = null;
		}

		// then, translate values
		final Collection<Expression> varValues = compressedProgramState.getValues(varName);
		final Collection<IASTExpression> newVarValues = new ArrayList<>();
		for (final Expression varValue : varValues) {
			final IASTExpression newVarValue = translateExpression(varValue, cType);
			if (newVarValue != null) {
				newVarValues.add(newVarValue);
			}
		}

		// finally, merge with possibly existing values for this name
		if (!newVarValues.isEmpty()) {
			final Collection<IASTExpression> oldVarValues = translatedStateMap.put(newVarName, newVarValues);
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

		return new ProgramState<>(map);
	}

	private void extractTemporaryPointerExpression(final List<Pair<Expression, Collection<Expression>>> oldEntries,
			final List<Pair<Expression, Collection<Expression>>> newEntries) {
		for (int i = oldEntries.size() - 1; i >= 0; i--) {
			final Pair<Expression, Collection<Expression>> entry = oldEntries.get(i);
			final String str = BoogiePrettyPrinter.print(entry.getFirst());
			if (entry.getFirst() instanceof IdentifierExpression && str.endsWith(SFO.POINTER_BASE)) {
				final String name = str.substring(0, str.length() - SFO.POINTER_BASE.length());
				for (int j = oldEntries.size() - 1; j >= 0; j--) {
					final Pair<Expression, Collection<Expression>> otherentry = oldEntries.get(j);
					final String other = BoogiePrettyPrinter.print(otherentry.getFirst());
					if (otherentry.getFirst() instanceof IdentifierExpression && other.endsWith(SFO.POINTER_OFFSET)
							&& other.startsWith(name)) {
						final TemporaryPointerExpression tmpPointerVar =
								new TemporaryPointerExpression(entry.getFirst().getLocation());
						tmpPointerVar.setBase(entry.getFirst());
						tmpPointerVar.setOffset(otherentry.getFirst());
						if (entry.getSecond().size() != 1 || otherentry.getSecond().size() != 1) {
							reportUnfinishedBacktranslation(
									UNFINISHED_BACKTRANSLATION + " Pointers with multiple values");
						}
						final TemporaryPointerExpression tmpPointerValue =
								new TemporaryPointerExpression(entry.getFirst().getLocation());
						for (final Expression baseValue : entry.getSecond()) {
							tmpPointerValue.setBase(baseValue);
						}
						for (final Expression offsetValue : otherentry.getSecond()) {
							tmpPointerValue.setOffset(offsetValue);
						}
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
	}

	@Override
	public IBacktranslatedCFG<String, CACSLLocation> translateCFG(final IBacktranslatedCFG<String, BoogieASTNode> cfg) {
		// mLogger.info("################# Input: " + cfg.getClass().getSimpleName());
		// printHondas(cfg, mLogger::info);
		// printCFG(cfg, mLogger::info);
		mGenerateBacktranslationWarnings = false;
		IBacktranslatedCFG<String, CACSLLocation> translated = translateCFG(cfg, (a, b, c) -> translateCFGEdge(a, b, c),
				(a, b, c) -> new CACSLBacktranslatedCFG(a, b, c, mLogger, mServices));
		translated = reduceCFGs(translated);
		// mLogger.info("################# Output: " + translated.getClass().getSimpleName());
		// printHondas(translated, mLogger::info);
		// printCFG(translated, mLogger::info);
		mGenerateBacktranslationWarnings = true;
		return translated;
	}

	@SuppressWarnings("unchecked")
	private <TVL, SVL> Multigraph<TVL, CACSLLocation> translateCFGEdge(
			final Map<IExplicitEdgesMultigraph<?, ?, SVL, BoogieASTNode, ?>, Multigraph<TVL, CACSLLocation>> cache,
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

	private <TVL, SVL> void createCFGMultigraphEdge(final Multigraph<TVL, CACSLLocation> currentSource,
			final ILocation loc, final Multigraph<TVL, CACSLLocation> lastTarget, final boolean isNegated) {
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
					reportUnfinishedBacktranslation(
							UNFINISHED_BACKTRANSLATION + ": Skipping invalid CLocation because IASTNode is null");
					edge = new MultigraphEdge<>(currentSource, null, lastTarget);
				} else if (cnode instanceof CASTTranslationUnit) {
					edge = new MultigraphEdge<>(currentSource, null, lastTarget);
				} else if (cnode instanceof CASTIfStatement) {
					final CASTIfStatement ifstmt = (CASTIfStatement) cnode;
					edge = new MultigraphEdge<>(currentSource,
							getConditionLoc(isNegated, ifstmt.getConditionExpression()), lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTWhileStatement) {
					final CASTWhileStatement whileStmt = (CASTWhileStatement) cnode;
					edge = new MultigraphEdge<>(currentSource, getConditionLoc(isNegated, whileStmt.getCondition()),
							lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTDoStatement) {
					// same as while
					final CASTDoStatement doStmt = (CASTDoStatement) cnode;
					edge = new MultigraphEdge<>(currentSource, getConditionLoc(isNegated, doStmt.getCondition()),
							lastTarget);
					new ConditionAnnotation(isNegated).annotate(edge);
				} else if (cnode instanceof CASTForStatement) {
					// same as while
					final CASTForStatement forStmt = (CASTForStatement) cnode;
					edge = new MultigraphEdge<>(currentSource,
							getConditionLoc(isNegated, forStmt.getConditionExpression()), lastTarget);
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
			reportUnfinishedBacktranslation(
					UNFINISHED_BACKTRANSLATION + ": Invalid location (Location is no CACSLLocation)");
			edge = new MultigraphEdge<>(currentSource, null, lastTarget);
		}
	}

	private CLocation getConditionLoc(final boolean isNegated, final IASTExpression condExpr) {
		return (CLocation) mLocationFactory.createCLocation(condExpr);
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

	@Override
	public IASTExpression translateExpression(final Expression expression) {
		return translateExpression(expression, null);
	}

	private IASTExpression translateExpression(final Expression expression, final CType cType) {
		if (expression instanceof UnaryExpression) {
			// handle old vars
			final UnaryExpression uexp = (UnaryExpression) expression;
			if (uexp.getOperator() == Operator.OLD) {
				final IASTExpression innerTrans = translateExpression(uexp.getExpr());
				if (innerTrans == null) {
					return null;
				}
				final CType newCType;
				if (innerTrans instanceof FakeExpression) {
					newCType = ((FakeExpression) innerTrans).getCType();
				} else {
					newCType = cType;
				}
				return new FakeExpression(innerTrans, "\\old(" + innerTrans.getRawSignature() + ")", newCType);
			}
		}

		if (expression instanceof TemporaryPointerExpression) {
			return ((TemporaryPointerExpression) expression).translate();
		}

		final ILocation loc = expression.getLocation();
		if (loc instanceof ACSLLocation) {
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": Expression "
					+ BoogiePrettyPrinter.print(expression) + " has an ACSLNode, but we do not support it yet");
			return null;

		}

		if (loc instanceof CLocation) {
			final CLocation cloc = (CLocation) loc;

			if (cloc.ignoreDuringBacktranslation()) {
				// this should lead to nothing
				return null;
			}

			final IASTNode cnode = cloc.getNode();
			if (cnode == null) {
				reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": Expression "
						+ BoogiePrettyPrinter.print(expression) + " has no C AST node");
				return null;
			}

			if (cnode instanceof IASTExpression) {
				return (IASTExpression) cnode;
			} else if (cnode instanceof CASTTranslationUnit) {
				// expressions that map to CASTTranslationUnit dont need to
				// be backtranslated
				return null;
			} else if (cnode instanceof CASTSimpleDeclaration) {
				return handleExpressionCASTSimpleDeclaration(expression, (CASTSimpleDeclaration) cnode);
			} else if (cnode instanceof CASTFunctionDefinition) {
				if (expression instanceof IdentifierExpression) {
					final IdentifierExpression orgidexp = (IdentifierExpression) expression;
					final TranslatedVariable origName = translateIdentifierExpression(orgidexp);
					if (origName != null) {
						return new FakeExpression(cnode, origName.toString(), origName.getCType());
					}
				}
				reportUnfinishedBacktranslation(
						UNFINISHED_BACKTRANSLATION + ": Expression " + BoogiePrettyPrinter.print(expression)
								+ " has a CASTFunctionDefinition but is no IdentifierExpression: "
								+ expression.getClass().getSimpleName());
				return null;
			} else if (cnode instanceof CASTFunctionDeclarator) {

				// this may be a function application:
				// - #res is the return value of the function

				if (expression instanceof IdentifierExpression) {
					final IdentifierExpression iexpr = (IdentifierExpression) expression;
					final TranslatedVariable origName = translateIdentifierExpression(iexpr);
					if (origName != null) {
						return new FakeExpression(cnode, origName.getName(), origName.getCType());
					}
				}
				reportUnfinishedBacktranslation(
						UNFINISHED_BACKTRANSLATION + ": Expression " + BoogiePrettyPrinter.print(expression)
								+ " has a C AST node but it is no IASTExpression: " + cnode.getClass());
				return null;
			} else {
				reportUnfinishedBacktranslation(
						UNFINISHED_BACKTRANSLATION + ": Expression " + BoogiePrettyPrinter.print(expression)
								+ " has a C AST node but it is no IASTExpression: " + cnode.getClass());
				return null;
			}
		} else if (expression instanceof IntegerLiteral) {
			return translateIntegerLiteral(cType, (IntegerLiteral) expression);
		} else if (expression instanceof BooleanLiteral) {
			return translateBooleanLiteral((BooleanLiteral) expression);
		} else if (expression instanceof RealLiteral) {
			return translateRealLiteral((RealLiteral) expression);
		} else if (expression instanceof BitvecLiteral) {
			return translateBitvecLiteral(cType, (BitvecLiteral) expression);
		} else if (expression instanceof FunctionApplication) {
			return translateFunctionApplication(cType, (FunctionApplication) expression);
		} else {
			// things that land here are typically synthesized contracts or
			// things like that. Here we replace Boogie variable names with C variable names
			final Expression translated = new SynthesizedExpressionTransformer().processExpression(expression);
			if (translated != null) {
				String translatedString = BoogiePrettyPrinter.print(translated);
				// its ugly, but the easiest way to backtranslate a synthesized boogie expression
				// we just replace operators that "look" different in C
				// TODO: We need a new BoogiePrettyPrinter for "FakeC" that takes care of quantifiers and such things
				// (using ACSL).
				translatedString = translatedString.replaceAll("old\\(", "\\\\old\\(")
						.replaceAll("(\\\\)*old", "\\\\old").replaceAll("exists", "\\\\exists");
				return new FakeExpression(translatedString);
			}
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": Expression "
					+ BoogiePrettyPrinter.print(expression) + " has no CACSLLocation");
			return null;
		}
	}

	private IASTExpression translateFunctionApplication(final CType cType, final FunctionApplication fun) {
		final Pair<String, CPrimitives> reversed = SFO.reverseBoogieFunctionName(fun.getIdentifier());
		if (reversed == null) {
			reportUnfinishedBacktranslation(
					UNFINISHED_BACKTRANSLATION + " cannot identify Boogie2SMT function " + fun.getIdentifier());
			return null;
		}
		final String smtFunction = reversed.getFirst();

		switch (smtFunction) {
		case "fp":
			// this function is used to construct floating points
			return translateFloatConstConstructor(cType, fun, reversed.getSecond());
		case "NaN":
			return translateFloatNaNConstructor(cType, fun, reversed.getSecond());
		default:
			reportUnfinishedBacktranslation(
					UNFINISHED_BACKTRANSLATION + " could not match function " + fun.getIdentifier());
			return null;
		}
	}

	private IASTExpression translateFloatConstConstructor(final CType cType, final FunctionApplication fun,
			final CPrimitives floatType) {
		switch (floatType) {
		case LONGDOUBLE:
			// ~fp~LONGDOUBLE(in0 : bv1, in1 : bv15, in2 : bv112)
			final BitvecLiteral sign = (BitvecLiteral) fun.getArguments()[0];
			final BitvecLiteral exponent = (BitvecLiteral) fun.getArguments()[1];
			final BitvecLiteral fraction = (BitvecLiteral) fun.getArguments()[2];
			return createFakeFloat(sign, exponent, fraction);
		case BOOL:
		case CHAR:
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
		case VOID:
			throw new IllegalArgumentException(floatType + " is not a float type");
		case COMPLEX_DOUBLE:
		case COMPLEX_FLOAT:
		case COMPLEX_LONGDOUBLE:
		case DOUBLE:
		case FLOAT:
		default:
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + " " + floatType + " is not yet converted ("
					+ fun.getIdentifier() + ")");
			return null;
		}
	}

	private IASTExpression translateFloatNaNConstructor(final CType cType, final FunctionApplication fun,
			final CPrimitives floatType) {
		switch (floatType) {
		case BOOL:
		case CHAR:
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
		case VOID:
			throw new IllegalArgumentException(floatType + " is not a float type");
		case COMPLEX_DOUBLE:
		case COMPLEX_FLOAT:
		case COMPLEX_LONGDOUBLE:
		case DOUBLE:
		case FLOAT:
		case LONGDOUBLE:
			// ~NaN~FLOAT() returns (out : C_FLOAT)
			return new FakeExpression(String.valueOf(Float.NaN));
		default:
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + " " + floatType + " is not yet converted ("
					+ fun.getIdentifier() + ")");
			return null;
		}
	}

	private static IASTExpression createFakeFloat(final BitvecLiteral sign, final BitvecLiteral exponent,
			final BitvecLiteral fraction) {
		final String bit = bitvecToString(sign) + bitvecToString(exponent) + bitvecToString(fraction);
		final BigDecimal f = getDecimalFromBinaryString(bit);
		return new FakeExpression(f.toPlainString());
	}

	private static BigDecimal getDecimalFromBinaryString(final String binary) {
		final int len = binary.length();
		if (len == 32) {
			final int intBits = Integer.parseUnsignedInt(binary, 2);
			final float floatValue = Float.intBitsToFloat(intBits);
			return BigDecimal.valueOf(floatValue);
		} else if (len == 64) {
			final long longBits = Long.parseUnsignedLong(binary, 2);
			final double doubleValue = Double.longBitsToDouble(longBits);
			return BigDecimal.valueOf(doubleValue);
		} else {
			throw new IllegalArgumentException("Unsupported length: " + len);
		}
	}

	private static String bitvecToString(final BitvecLiteral lit) {
		final String binStr = new BigInteger(lit.getValue()).toString(2);
		assert binStr.length() <= lit.getLength() : "Binary string cannot be longer than bitvector literal length";
		final int missingZeros = lit.getLength() - binStr.length();
		if (missingZeros > 0) {
			final String formatStr = "%" + lit.getLength() + "s";
			return String.format(formatStr, binStr).replace(' ', '0');
		}
		return binStr;
	}

	private IASTExpression translateIntegerLiteral(final CType cType, final IntegerLiteral lit) {
		final String value;
		if (cType == null) {
			value = lit.getValue();
		} else if (cType instanceof CPointer) {
			return translateIntegerLiteral(new CPrimitive(CPrimitives.INT), lit);
		} else if (cType instanceof CEnum) {
			return translateIntegerLiteral(new CPrimitive(CPrimitives.INT), lit);
		} else if (cType instanceof CNamed) {
			return translateIntegerLiteral(cType.getUnderlyingType(), lit);
		} else {
			final BigInteger extractedValue = mExpressionTranslation.extractIntegerValue(lit, cType);
			value = String.valueOf(extractedValue);
		}
		checkLiteral(cType, lit, value);
		return new FakeExpression(value);
	}

	private IASTExpression translateBitvecLiteral(final CType cType, final BitvecLiteral lit) {
		final String value;
		if (cType == null) {
			value = naiveBitvecLiteralValueExtraction(lit);
		} else if (cType instanceof CNamed) {
			if (cType.getUnderlyingType() != null) {
				return translateBitvecLiteral(cType.getUnderlyingType(), lit);
			}
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + " cannot tranlate BitvecLiteral "
					+ BoogiePrettyPrinter.print(lit) + " for unknown CNamed CType " + cType);
			return null;
		} else if (cType instanceof CPrimitive) {
			// literal C primitives that are represented as bitvectors have to be converted back according to their
			// translation, but it seems that AExpression is incomplete
			final CPrimitive primitive = (CPrimitive) cType.getUnderlyingType();
			if (primitive.isIntegerType()) {
				value = String.valueOf(mExpressionTranslation.extractIntegerValue(lit, cType));
			} else if (primitive.isFloatingType()) {
				value = naiveBitvecLiteralValueExtraction(lit);
				reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION
						+ " using integer-interpretation for bitvector literal with floating type because of unification failure: "
						+ BoogiePrettyPrinter.print(lit) + "=" + value);
			} else {
				reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + " cannot tranlate BitvecLiteral "
						+ BoogiePrettyPrinter.print(lit) + " representing " + primitive.getType());
				return null;
			}
		} else {
			final BigInteger extractedValue = mExpressionTranslation.extractIntegerValue(lit, cType);
			value = String.valueOf(extractedValue);
		}
		checkLiteral(cType, lit, value);
		return new FakeExpression(value);
	}

	private IASTExpression translateRealLiteral(final RealLiteral lit) {
		checkLiteral(null, lit, lit.getValue());
		return new FakeExpression(lit.getValue());
	}

	private IASTExpression translateBooleanLiteral(final BooleanLiteral lit) {
		final String value = lit.getValue() ? "1" : "0";
		checkLiteral(null, lit, value);
		return new FakeExpression(value);
	}

	private void checkLiteral(final CType cType, final Expression expr, final String value) {
		if (value == null || "null".equals(value)) {
			if (cType == null) {
				reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": " + expr.getClass().getSimpleName()
						+ " " + BoogiePrettyPrinter.print(expr) + " could not be translated");
			} else {
				reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": " + expr.getClass().getSimpleName()
						+ " " + BoogiePrettyPrinter.print(expr) + " could not be translated for associated CType "
						+ cType);
			}
		} else if (value.contains("~fp~LONGDOUBLE")) {
			reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": " + expr.getClass().getSimpleName() + " "
					+ BoogiePrettyPrinter.print(expr) + " could not be translated");

		}
	}

	private static String naiveBitvecLiteralValueExtraction(final BitvecLiteral lit) {
		final String value = lit.getValue();
		BigInteger decimalValue = new BigInteger(value);

		// this is only the isSigned case
		final BigInteger maxRepresentablePositiveValuePlusOne = new BigInteger("2").pow(lit.getLength() - 1);
		if (decimalValue.compareTo(maxRepresentablePositiveValuePlusOne) >= 0) {
			final BigInteger numberOfValues = new BigInteger("2").pow(lit.getLength());
			decimalValue = decimalValue.subtract(numberOfValues);
		}
		return String.valueOf(decimalValue);
	}

	private IASTExpression handleExpressionCASTSimpleDeclaration(final Expression expression,
			final CASTSimpleDeclaration decls) {
		// this should only happen for IdentifierExpressions
		if (!(expression instanceof IdentifierExpression)) {
			reportUnfinishedBacktranslation(
					UNFINISHED_BACKTRANSLATION + "Expression " + BoogiePrettyPrinter.print(expression)
							+ " is mapped to a declaration, but is no IdentifierExpression");
			return null;
		}

		if (decls.getDeclarators() == null || decls.getDeclarators().length == 0) {
			throw new IllegalArgumentException("Expression " + BoogiePrettyPrinter.print(expression)
					+ " is mapped to a declaration without declarators.");
		}

		if (decls.getDeclarators().length == 1) {
			final IdentifierExpression orgidexp = (IdentifierExpression) expression;
			final TranslatedVariable origName = translateIdentifierExpression(orgidexp);
			if (origName == null) {
				reportUnfinishedBacktranslation(UNFINISHED_BACKTRANSLATION + ": No BoogieVar found for "
						+ BoogiePrettyPrinter.print(expression));
				return null;
			}
			return new FakeExpression(decls, decls.getDeclarators()[0].getName().getRawSignature(),
					origName.getCType());
		}
		// ok, this is a declaration ala "int a,b;", so we use
		// our backtranslation map to get the real name
		final IdentifierExpression orgidexp = (IdentifierExpression) expression;
		final TranslatedVariable origName = translateIdentifierExpression(orgidexp);
		if (origName == null) {
			reportUnfinishedBacktranslation(
					UNFINISHED_BACKTRANSLATION + ": No BoogieVar found for " + BoogiePrettyPrinter.print(expression));
			return null;
		}
		for (final IASTDeclarator decl : decls.getDeclarators()) {
			if (origName.getName().indexOf(decl.getName().getRawSignature()) != -1) {
				return new FakeExpression(decl.getName().getRawSignature());
			}
		}
		reportUnfinishedBacktranslation(
				UNFINISHED_BACKTRANSLATION + ": IdentifierExpression " + BoogiePrettyPrinter.print(expression)
						+ " has a CASTSimpleDeclaration, but we were unable to determine the variable name from it: "
						+ decls.getRawSignature());
		return null;
	}

	private void reportUnfinishedBacktranslation(final String message) {
		mLogger.warn(message);
		if (mGenerateBacktranslationWarnings) {
			mServices.getResultService().reportResult(Activator.PLUGIN_ID,
					new GenericResult(Activator.PLUGIN_ID, UNFINISHED_BACKTRANSLATION, message, Severity.WARNING));
		}
	}

	private TranslatedVariable translateIdentifierExpression(final IdentifierExpression expr) {
		return translateBoogieIdentifier(expr, expr.getIdentifier());
	}

	private TranslatedVariable translateBoogieIdentifier(final IdentifierExpression expr, final String boogieId) {
		final TranslatedVariable result;
		if (boogieId.equals(SFO.RES)) {
			result = new TranslatedVariable(expr, "\\result", null, VariableType.RESULT);
		} else if (mBoogie2C.getVar2CVar().containsKey(boogieId)) {
			final Pair<String, CType> pair = mBoogie2C.getVar2CVar().get(boogieId);
			result = new TranslatedVariable(expr, pair.getFirst(), pair.getSecond(), VariableType.NORMAL);
		} else if (mBoogie2C.getInVar2CVar().containsKey(boogieId)) {
			// invars can only occur in expressions as part of synthetic expressions, and then they represent oldvars
			final Pair<String, CType> pair = mBoogie2C.getInVar2CVar().get(boogieId);
			result = new TranslatedVariable(expr, pair.getFirst(), pair.getSecond(), VariableType.INVAR);
		} else if (mBoogie2C.getTempVar2Obj().containsKey(boogieId)) {
			final SFO.AUXVAR purpose = mBoogie2C.getTempVar2Obj().get(boogieId);
			result = new TranslatedVariable(expr, boogieId, null, purpose);
		} else if (boogieId.equals(SFO.VALID)) {
			result = new TranslatedVariable(expr, "\\valid", null, VariableType.VALID);
		} else {
			// if its base or offset, try again with them stripped
			if (boogieId.endsWith(SFO.POINTER_BASE)) {
				final TranslatedVariable base = translateBoogieIdentifier(expr,
						boogieId.substring(0, boogieId.length() - SFO.POINTER_BASE.length() - 1));
				result = new TranslatedVariable(expr, base.getName(), base.getCType(), VariableType.POINTER_BASE);
			} else if (boogieId.endsWith(SFO.POINTER_OFFSET)) {
				final TranslatedVariable offset = translateBoogieIdentifier(expr,
						boogieId.substring(0, boogieId.length() - SFO.POINTER_OFFSET.length() - 1));
				result = new TranslatedVariable(expr, offset.getName(), offset.getCType(), VariableType.POINTER_OFFSET);
			} else {
				result = new TranslatedVariable(expr, boogieId, null, VariableType.UNKNOWN);
				reportUnfinishedBacktranslation("unknown boogie variable " + boogieId);
			}
		}
		return result;
	}

	void putFunction(final String boogieId, final String cId) {
		mBoogie2C.putFunction(boogieId, cId);
	}

	public void putVar(final String boogieId, final String cId, final CType cType) {
		mBoogie2C.putVar(boogieId, cId, cType);
	}

	public void putInVar(final String boogieId, final String cId, final CType cType) {
		mBoogie2C.putInVar(boogieId, cId, cType);
	}

	public void putTempVar(final String boogieId, final SFO.AUXVAR purpose, final CType cType) {
		mBoogie2C.putTempVar(boogieId, purpose, cType);
	}

	public boolean isTempVar(final String boogieId) {
		return mBoogie2C.getTempVar2Obj().containsKey(boogieId);
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
	 * A subtree check that sacrifices memory consumption for speed. It is about 20x faster, but uses a lookup table.
	 *
	 * A subtree check is used to determine if a trace element is actually a nesting of some later trace element in the
	 * error path (like in x = x++ + ++x, were x++ and ++x are nestings of +, and + is a nesting of the assignment).
	 *
	 * There may be a better solution to this (its rather expensive).
	 *
	 */
	protected static List<AtomicTraceElement<CACSLLocation>>
			checkForSubtreeInclusion(final List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements) {

		// first, compute lookup data structure
		final Map<AtomicTraceElement<CACSLLocation>, Set<IASTNode>> ateToParents = new HashMap<>();
		for (int i = 0; i < translatedAtomicTraceElements.size(); ++i) {
			final AtomicTraceElement<CACSLLocation> ate = translatedAtomicTraceElements.get(i);

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

			// TODO: Fix relevance information

			final IASTNode candidate = ((CLocation) current.getStep()).getNode();
			if (parents.contains(candidate)) {
				EnumSet<StepInfo> set = ate.getStepInfo();
				if (set.isEmpty() || set.contains(StepInfo.NONE)) {
					set = EnumSet.of(newSi);
				} else {
					set.add(newSi);
				}
				return new AtomicTraceElement<>(current.getStep(), ate.getStep(), set,
						mergeRelevaneInformation(ate.getRelevanceInformation(), current.getRelevanceInformation()),
						ate.getPrecedingProcedure(), ate.getSucceedingProcedure());
			}
		}
		return ate;
	}

	private class SynthesizedExpressionTransformer extends BoogieTransformer {

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression ident = (IdentifierExpression) expr;
				final ILocation loc = ident.getLocation();
				if (loc instanceof CACSLLocation) {
					final TranslatedVariable translated = translateIdentifierExpression(ident);
					if (translated != null) {
						return translated;
					}
				}
			}
			return super.processExpression(expr);
		}
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

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				mAllAreTemp = mAllAreTemp && isTempVar(((IdentifierExpression) expr).getIdentifier());
			}
			return super.processExpression(expr);
		}
	}

	/**
	 * Translates Boogie identifiers of variables and functions back to the identifiers of variables and operators in C.
	 *
	 * This class is in an immature state and translates Strings to Strings.
	 *
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	private static final class Boogie2C {

		private final Map<String, Pair<String, CType>> mInVar2CVar;
		private final Map<String, Pair<String, CType>> mVar2CVar;
		private final Map<String, SFO.AUXVAR> mTempVar2Obj;
		private final Map<String, String> mFunctionId2Operator;

		private Boogie2C() {
			mInVar2CVar = new HashMap<>();
			mVar2CVar = new HashMap<>();
			mTempVar2Obj = new HashMap<>();
			mFunctionId2Operator = new HashMap<>();
		}

		private Map<String, Pair<String, CType>> getInVar2CVar() {
			return mInVar2CVar;
		}

		private Map<String, Pair<String, CType>> getVar2CVar() {
			return mVar2CVar;
		}

		private Map<String, SFO.AUXVAR> getTempVar2Obj() {
			return mTempVar2Obj;
		}

		private void putFunction(final String boogieId, final String cId) {
			mFunctionId2Operator.put(boogieId, cId);
		}

		private void putVar(final String boogieId, final String cId, final CType cType) {
			mVar2CVar.put(boogieId, new Pair<>(cId, cType));
		}

		private void putInVar(final String boogieId, final String cId, final CType cType) {
			mInVar2CVar.put(boogieId, new Pair<>(cId, cType));
		}

		private void putTempVar(final String boogieId, final SFO.AUXVAR purpose, final CType cType) {
			mTempVar2Obj.put(boogieId, purpose);
		}
	}

	private class TemporaryPointerExpression extends Expression {

		private static final long serialVersionUID = 1L;
		private Expression mBase;
		private Expression mOffset;

		public TemporaryPointerExpression(final ILocation loc) {
			super(loc);
		}

		public IASTExpression translate() {
			if (mBase instanceof IdentifierExpression) {
				// its a declaration or an access
				return translateExpression(mBase);
			}
			// some kind of value
			final IASTExpression base = translateExpression(mBase);
			final IASTExpression offset = translateExpression(mOffset);
			return new FakeExpression(base, "{" + base.getRawSignature() + ":" + offset.getRawSignature() + "}", null);
		}

		public void setBase(final Expression expr) {
			mBase = expr;
		}

		public void setOffset(final Expression expr) {
			mOffset = expr;
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

	private static final class TranslatedVariable extends Expression {
		private static final long serialVersionUID = 1L;
		private final String mName;
		private final CType mCType;
		private final VariableType mVarType;
		private final SFO.AUXVAR mPurpose;
		private final IdentifierExpression mOriginalExpression;

		public TranslatedVariable(final IdentifierExpression originalExpression, final String name, final CType cType,
				final VariableType varType) {
			super(null);
			assert varType != VariableType.AUX : "You must supply a purpose for an auxvar";
			mOriginalExpression = originalExpression;
			mName = name;
			mCType = cType;
			mVarType = varType;
			mPurpose = null;

		}

		public TranslatedVariable(final IdentifierExpression originalExpression, final String name, final CType cType,
				final SFO.AUXVAR purpose) {
			super(null);
			mOriginalExpression = originalExpression;
			mCType = cType;
			mVarType = VariableType.AUX;
			// if the variable is an aux variable, we just use the C function for which it was introduced and hope for
			// the best
			mName = getRealName(originalExpression, name);
			mPurpose = purpose;
		}

		private static String getRealName(final IdentifierExpression originalExpression, final String name) {
			final ILocation loc = originalExpression.getLoc();
			if (loc instanceof CLocation) {
				final CLocation cloc = (CLocation) loc;
				return cloc.getNode().getRawSignature();
			}
			return name;
		}

		public String getName() {
			return mName;
		}

		public CType getCType() {
			return mCType;
		}

		public VariableType getVarType() {
			return mVarType;
		}

		public SFO.AUXVAR getPurpose() {
			return mPurpose;
		}

		public IdentifierExpression getOriginalExpression() {
			return mOriginalExpression;
		}

		@Override
		public void accept(final GeneratedBoogieAstVisitor visitor) {
			// nothing to accept here
		}

		@Override
		public Expression accept(final GeneratedBoogieAstTransformer visitor) {
			return null;
		}

		@Override
		public String toString() {
			switch (mVarType) {
			case OLD:
			case INVAR:
				return "\\old(" + mName + ")";
			case NORMAL:
			case POINTER_BASE:
			case POINTER_OFFSET:
				return mName;
			case RESULT:
				return "\\result";
			case VALID:
				return "\\valid";
			case AUX:
				return "aux-" + mName + "-aux";
			case UNKNOWN:
				return "unknown-" + mName + "-unknown";
			default:
				throw new UnsupportedOperationException("VariableType " + mVarType + " not yet implemented");
			}
		}
	}

}
