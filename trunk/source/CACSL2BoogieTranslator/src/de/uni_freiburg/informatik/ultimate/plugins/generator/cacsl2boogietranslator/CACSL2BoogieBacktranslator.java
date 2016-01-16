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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDoStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTForStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionCallExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDefinition;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIfStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTranslationUnit;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTWhileStatement;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * Translation from Boogie to C for traces and expressions.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */
public class CACSL2BoogieBacktranslator extends
		DefaultTranslator<BoogieASTNode, CACSLLocation, Expression, IASTExpression> {

	/*
	 * TODO Expression -> CACSLLocation CACSLProgramExecution bauen
	 */

	private Boogie2C mBoogie2C;
	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	private static final String sUnfinishedBacktranslation = "Unfinished Backtranslation";
	private AExpressionTranslation mExpressionTranslation;

	public CACSL2BoogieBacktranslator(IUltimateServiceProvider services) {
		super(BoogieASTNode.class, CACSLLocation.class, Expression.class, IASTExpression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mBoogie2C = new Boogie2C();
	}
	
	public void setExpressionTranslation(AExpressionTranslation expressionTranslation) {
		mExpressionTranslation = expressionTranslation;
	}

	@Override
	public List<CACSLLocation> translateTrace(List<BoogieASTNode> trace) {
		return super.translateTrace(trace);
	}

	@Override
	public IProgramExecution<CACSLLocation, IASTExpression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {

		// initial state
		ProgramState<IASTExpression> initialState = translateProgramState(programExecution.getInitialProgramState());

		// translate trace and program state in tandem
		List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements = new ArrayList<>();
		List<ProgramState<IASTExpression>> translatedProgramStates = new ArrayList<>();
		for (int i = 0; i < programExecution.getLength(); ++i) {

			AtomicTraceElement<BoogieASTNode> ate = programExecution.getTraceElement(i);
			ILocation loc = ate.getTraceElement().getLocation();

			if (loc instanceof CLocation) {
				// i = findMergeSequence(programExecution, i, loc);

				CLocation cloc = (CLocation) loc;
				if (cloc.ignoreDuringBacktranslation()) {
					// we skip all clocs that can be ignored, i.e. things that
					// belong to internal structures
					continue;

				}

				IASTNode cnode = cloc.getNode();

				if (cnode == null) {
					reportUnfinishedBacktranslation(sUnfinishedBacktranslation
							+ ": Skipping invalid CLocation because IASTNode is null");
					continue;
				}

				if (cnode instanceof CASTTranslationUnit) {
					// if it points to the TranslationUnit, it should be
					// Ultimate.init or Ultimate.start and we make our
					// initalstate right after them here
					// if we already have some explicit declarations, we just
					// skip the whole initial state business and use this as the
					// last
					// normal state
					i = findMergeSequence(programExecution, i, loc);
					if (cnode instanceof CASTTranslationUnit) {
						if (translatedAtomicTraceElements.size() > 0) {
							translatedProgramStates.remove(translatedProgramStates.size() - 1);
							translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));
						} else {
							initialState = translateProgramState(programExecution.getProgramState(i));
						}
					}
					continue;
				} else if (cnode instanceof CASTIfStatement) {
					// if its an if, we point to the condition
					CASTIfStatement ifstmt = (CASTIfStatement) cnode;
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, LocationFactory
							.createCLocation(ifstmt.getConditionExpression()), ate.getStepInfo()));
				} else if (cnode instanceof CASTWhileStatement) {
					// if its an while, we know that it is not ignored and that
					// it comes from the if(!cond)break; construct in Boogie.
					// we therefore invert the stepinfo, i.e. from condevaltrue
					// to condevalfalse
					EnumSet<StepInfo> newSi = invertConditionInStepInfo(ate.getStepInfo());
					if (newSi == null) {
						continue;
					}
					CASTWhileStatement whileStmt = (CASTWhileStatement) cnode;
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, LocationFactory
							.createCLocation(whileStmt.getCondition()), newSi));
				} else if (cnode instanceof CASTDoStatement) {
					// same as while
					CASTDoStatement doStmt = (CASTDoStatement) cnode;
					EnumSet<StepInfo> newSi = invertConditionInStepInfo(ate.getStepInfo());
					if (newSi == null) {
						continue;
					}
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, LocationFactory
							.createCLocation(doStmt.getCondition()), newSi));
				} else if (cnode instanceof CASTForStatement) {
					// same as while
					CASTForStatement forStmt = (CASTForStatement) cnode;
					EnumSet<StepInfo> newSi = invertConditionInStepInfo(ate.getStepInfo());
					if (newSi == null) {
						continue;
					}
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, LocationFactory
							.createCLocation(forStmt.getConditionExpression()), newSi));
				} else if (cnode instanceof CASTFunctionCallExpression) {
					// more complex, handled separately
					i = handleCASTFunctionCallExpression(programExecution, i, (CASTFunctionCallExpression) cnode, cloc,
							translatedAtomicTraceElements, translatedProgramStates);
					continue;
				} else {
					// just use as it, all special cases should have been
					// handled
					// we merge all things in a row that point to the same
					// location, as they only contain temporary stuff
					i = findMergeSequence(programExecution, i, loc);
					// String raw = cnode.getRawSignature(); // debug
					if (ate.getTraceElement() instanceof HavocStatement) {
						HavocStatement havoc = (HavocStatement) ate.getTraceElement();
						CheckForTempVars check = new CheckForTempVars();
						check.processStatement(havoc);
						if (check.areAllTemp()) {
							// we dont want to see no dirty temp havoc
							continue;
						}
					}
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc));
				}
				translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));

			} else if (loc instanceof ACSLLocation) {
				// for now, just use ACSL as-it
				translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>((ACSLLocation) loc));
				translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));

			} else {
				// invalid location
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation
						+ ": Invalid location (Location is no CACSLLocation)");
			}
		}

		// replace all expr eval occurences with the right atomictraceelements
		CheckForSubtreeInclusion check = new CheckForSubtreeInclusion();
		translatedAtomicTraceElements = check.check(translatedAtomicTraceElements);

		return new CACSLProgramExecution(initialState, translatedAtomicTraceElements, translatedProgramStates,mLogger);
	}

	private EnumSet<StepInfo> invertConditionInStepInfo(EnumSet<StepInfo> oldSiSet) {
		if (!oldSiSet.contains(StepInfo.CONDITION_EVAL_FALSE) && !oldSiSet.contains(StepInfo.CONDITION_EVAL_TRUE)) {
			reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Invalid StepInfo in Loop");
			return null;
		}
		EnumSet<StepInfo> set = EnumSet.noneOf(StepInfo.class);
		for (StepInfo oldSi : oldSiSet) {
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

	private int handleCASTFunctionCallExpression(IProgramExecution<BoogieASTNode, Expression> programExecution, int i,
			CASTFunctionCallExpression fcall, CLocation cloc,
			List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements,
			List<ProgramState<IASTExpression>> translatedProgramStates) {
		// directly after the functioncall expression we find
		// for each argument a CASTFunctionDefinition / AssignmentStatement that
		// maps the input variable to a new local one (because boogie function
		// params are immutable)
		// we throw them away
		AtomicTraceElement<BoogieASTNode> origFuncCall = programExecution.getTraceElement(i);

		if (!(origFuncCall.getTraceElement() instanceof CallStatement)) {
			// this is some special case, e.g. an assert false or an havoc
			if (origFuncCall.getTraceElement() instanceof AssertStatement) {
				translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc, origFuncCall
						.getStepInfo()));
				translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));
			} else if (origFuncCall.getTraceElement() instanceof HavocStatement) {
				HavocStatement havoc = (HavocStatement) origFuncCall.getTraceElement();
				CheckForTempVars check = new CheckForTempVars();
				check.processStatement(havoc);
				if (!check.areAllTemp()) {
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc, origFuncCall
							.getStepInfo()));
					translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));
				}
			}
			return i;
		}

		if (origFuncCall.hasStepInfo(StepInfo.NONE)) {
			// this is some temp var stuff; we can safely ignore it
			return i;
		}

		translatedAtomicTraceElements
				.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc, origFuncCall.getStepInfo()));
		translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));

		if (origFuncCall.hasStepInfo(StepInfo.PROC_RETURN)) {
			// if it is a return we are already finished.
			return i;
		}
		// The following code is not necessary anymore because Alex changed the
		// local var initialisation code s.t the assign statements at the
		// beginning of each function have their ignore flags set
		// We keep it for a couple of revisions and throw it out once we are
		// sure we dont need it

		// int j = i + 1;
		// for (int k = 0; k < fcall.getArguments().length && j <
		// programExecution.getLength(); ++j, ++k) {
		// AtomicTraceElement<BoogieASTNode> origFuncDef =
		// programExecution.getTraceElement(j);
		//
		// if (!(origFuncDef.getTraceElement() instanceof AssignmentStatement))
		// {
		// reportUnfinishedBacktranslation("CASTFunctionCallExpression is followed by "
		// + origFuncDef.getTraceElement().getClass().getSimpleName());
		// return i;
		// }
		//
		// if (!(origFuncDef.getTraceElement().getLocation() instanceof
		// CACSLLocation)) {
		// reportUnfinishedBacktranslation("CASTFunctionCallExpression is followed by some unknown location: "
		// +
		// origFuncDef.getTraceElement().getLocation().getClass().getSimpleName());
		// return i;
		// }
		// IASTNode cnode = ((CLocation)
		// origFuncDef.getTraceElement().getLocation()).getNode();
		// if (!(cnode instanceof CASTFunctionDefinition)) {
		// reportUnfinishedBacktranslation("After CASTFunctionCallExpression should follow a "
		// + "CASTFunctionDefinition for each argument, but was: " +
		// cnode.getClass().getSimpleName());
		// return i;
		// }
		//
		// // there is no backtranslation for this assign, but maybe we need it
		// // to track the body vars?
		// // AssignmentStatement assign = (AssignmentStatement)
		// // origFuncDef.getTraceElement();
		// // IdentifierExpression origInParam = new
		// // LHSIdentifierExtractor().extract(assign);
		// // IASTExpression inParam = translateExpression(origInParam);
		// //
		// // translatedAtomicTraceElements.add(new
		// // AtomicTraceElement<CACSLLocation>(cloc, new
		// // CACSLLocation(inParam),
		// // StepInfo.ARG_EVAL));
		// //
		// //
		// translatedProgramStates.add(translateProgramState(programExecution.getProgramState(j)));
		// }
		//
		// i = j - 1;
		return i;
	}

	/**
	 * Starts from some point in the programExecution i and finds a j >= i && j
	 * < programExecution.length s.t. all elements [i..j] have the same
	 * location.
	 * 
	 * If i is invalid (outside of [0..programExecution.length-1]), this method
	 * throws an IllegalArgumentException.
	 * 
	 * @param programExecution
	 * @param i
	 * @param loc
	 * @return
	 */
	private int findMergeSequence(IProgramExecution<BoogieASTNode, Expression> programExecution, int i, ILocation loc) {
		if (i >= programExecution.getLength() || i < 0) {
			throw new IllegalArgumentException("i has an invalid value");
		}
		int j = i;
		for (; j < programExecution.getLength(); ++j) {
			// suche nach weiteren knoten die diese loc haben, um sie in
			// einem neuen statement zusammenzufassen
			AtomicTraceElement<BoogieASTNode> lookahead = programExecution.getTraceElement(j);
			if (!lookahead.getTraceElement().getLocation().equals(loc)) {
				j--;
				break;
			}
		}
		// springe zu dem, das wir zusammenfassen können
		if (j < programExecution.getLength()) {
			i = j;
		} else {
			i = programExecution.getLength() - 1;
		}
		return i;
	}

	private ProgramState<IASTExpression> translateProgramState(ProgramState<Expression> programState) {
		if (programState != null) {
			Map<IASTExpression, Collection<IASTExpression>> map = new HashMap<>();

			programState = compressProgramState(programState);

			for (Expression varName : programState.getVariables()) {
				IASTExpression newVarName = translateExpression(varName);
				if (newVarName == null) {
					continue;
				}
				final CType cType;
				if (newVarName instanceof FakeExpression) {
					cType = ((FakeExpression) newVarName).getCType();
				} else {
					cType = null;
				}

				Collection<Expression> varValues = programState.getValues(varName);
				Collection<IASTExpression> newVarValues = new ArrayList<>();
				for (Expression varValue : varValues) {
					IASTExpression newVarValue = translateExpression(varValue, cType);
					if (newVarValue != null) {
						newVarValues.add(newVarValue);
					}
				}
				if (newVarValues.size() > 0) {
					Collection<IASTExpression> oldVarValues = map.put(newVarName, newVarValues);
					if (oldVarValues != null) {
						newVarValues.addAll(oldVarValues);
					}
				}
			}
			if (map.isEmpty()) {
				return null;
			}
			return new ProgramState<IASTExpression>(map);
		}
		return null;
	}

	/**
	 * Replace base and offset with one {@link TemporaryPointerExpression}
	 * 
	 * @param programState
	 *            May not be null
	 */
	private ProgramState<Expression> compressProgramState(ProgramState<Expression> programState) {
		List<Entry<Expression, Collection<Expression>>> oldEntries = new ArrayList<>();
		List<Entry<Expression, Collection<Expression>>> newEntries = new ArrayList<>();

		for (Expression var : programState.getVariables()) {
			MyEntry<Expression, Collection<Expression>> entry = new MyEntry<>();
			entry.Key = var;
			entry.Value = programState.getValues(var);
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
		Map<Expression, Collection<Expression>> map = new HashMap<>();
		for (Entry<Expression, Collection<Expression>> entry : newEntries) {
			Collection<Expression> newValues = entry.getValue();
			Collection<Expression> oldValues = map.put(entry.getKey(), entry.getValue());
			if (oldValues != null) {
				newValues.addAll(oldValues);
			}
		}

		return new ProgramState<>(map);
	}

	private void extractTemporaryPointerExpression(List<Entry<Expression, Collection<Expression>>> oldEntries,
			List<Entry<Expression, Collection<Expression>>> newEntries) {
		for (int i = oldEntries.size() - 1; i >= 0; i--) {
			Entry<Expression, Collection<Expression>> entry = oldEntries.get(i);
			String str = BoogiePrettyPrinter.print(entry.getKey());
			if (entry.getKey() instanceof IdentifierExpression && str.endsWith(SFO.POINTER_BASE)) {
				String name = str.substring(0, str.length() - SFO.POINTER_BASE.length());
				for (int j = oldEntries.size() - 1; j >= 0; j--) {
					Entry<Expression, Collection<Expression>> otherentry = oldEntries.get(j);
					String other = BoogiePrettyPrinter.print(otherentry.getKey());
					if (otherentry.getKey() instanceof IdentifierExpression && other.endsWith(SFO.POINTER_OFFSET)
							&& other.startsWith(name)) {
						TemporaryPointerExpression tmpPointerVar = new TemporaryPointerExpression(entry.getKey()
								.getLocation());
						tmpPointerVar.setBase(entry.getKey());
						tmpPointerVar.setOffset(otherentry.getKey());
						if (entry.getValue().size() != 1 || otherentry.getValue().size() != 1) {
							reportUnfinishedBacktranslation(sUnfinishedBacktranslation
									+ " Pointers with multiple values");
						}
						TemporaryPointerExpression tmpPointerValue = new TemporaryPointerExpression(entry.getKey()
								.getLocation());
						for (Expression baseValue : entry.getValue()) {
							tmpPointerValue.setBase(baseValue);
						}
						for (Expression offsetValue : otherentry.getValue()) {
							tmpPointerValue.setOffset(offsetValue);
						}
						MyEntry<Expression, Collection<Expression>> newEntry = new MyEntry<>();
						newEntry.Key = tmpPointerVar;
						newEntry.Value = new ArrayList<>();
						newEntry.Value.add(tmpPointerValue);
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
	public IASTExpression translateExpression(Expression expression) {
		return translateExpression(expression, null);
	}
	
	public IASTExpression translateExpression(Expression expression, CType cType) {
		if (expression instanceof UnaryExpression) {
			// handle old vars
			UnaryExpression uexp = (UnaryExpression) expression;
			if (uexp.getOperator() == Operator.OLD) {
				IASTExpression innerTrans = translateExpression(uexp.getExpr());
				if (innerTrans == null) {
					return null;
				}
				if (innerTrans instanceof FakeExpression) {
					cType = ((FakeExpression) innerTrans).getCType();
				}
				FakeExpression fexp = new FakeExpression(innerTrans, "\\old(" + innerTrans.getRawSignature() + ")", cType);
				return fexp;
			}
		}

		if (expression instanceof TemporaryPointerExpression) {
			return ((TemporaryPointerExpression) expression).translate();
		}

		ILocation loc = expression.getLocation();
		if (loc instanceof ACSLLocation) {
			reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
					+ BoogiePrettyPrinter.print(expression) + " has an ACSLNode, but we do not support it yet");
			return null;

		}

		if (loc instanceof CLocation) {
			CLocation cloc = (CLocation) loc;

			if (cloc.ignoreDuringBacktranslation()) {
				// this should lead to nothing
				return null;
			}

			IASTNode cnode = cloc.getNode();

			if (cnode == null) {
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
						+ BoogiePrettyPrinter.print(expression) + " has no C AST node");
				return null;
			}

			if (cnode instanceof IASTExpression) {
				// if (cnode instanceof IASTIdExpression) {
				// // a read
				// return new FakeExpression("\\read(" + cnode.getRawSignature()
				// + ")");
				// }
				return (IASTExpression) cnode;
			} else if (cnode instanceof CASTTranslationUnit) {
				// expressions that map to CASTTranslationUnit dont need to
				// be backtranslated
				return null;
			} else if (cnode instanceof CASTSimpleDeclaration) {
				return handleExpressionCASTSimpleDeclaration(expression, (CASTSimpleDeclaration) cnode);
			} else if (cnode instanceof CASTFunctionDefinition) {
				if (expression instanceof IdentifierExpression) {
					IdentifierExpression orgidexp = (IdentifierExpression) expression;
					Pair<String,CType> origName = translateIdentifierExpression(orgidexp);
					if (origName != null) {
						return new FakeExpression(cnode, origName.getFirst(), origName.getSecond());
					}
				}
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
						+ BoogiePrettyPrinter.print(expression)
						+ " has a CASTFunctionDefinition but is no IdentifierExpression: "
						+ expression.getClass().getSimpleName());
				return null;
			} else {
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
						+ BoogiePrettyPrinter.print(expression) + " has a C AST node but it is no IASTExpression: "
						+ cnode.getClass());
				return null;
			}
		} else if (expression instanceof IntegerLiteral) {
			final String value;
			if (cType == null) {
				value = ((IntegerLiteral) expression).getValue();
			} else {
				if (cType.getUnderlyingType() instanceof CEnum) {
					cType = new CPrimitive(PRIMITIVE.INT);
				}
				BigInteger extractedValue = 
						mExpressionTranslation.extractIntegerValue(expression, cType.getUnderlyingType());
				value = String.valueOf(extractedValue);
			}
			FakeExpression clit = new FakeExpression(value);
			return clit;
		} else if (expression instanceof BooleanLiteral) {
			// TODO: I am not sure if we should convert this to integer_constant
			// or IASTLiteralExpression.lk_false / lk_true
			BooleanLiteral lit = (BooleanLiteral) expression;
			int value = (lit.getValue() ? 1 : 0);
			FakeExpression clit = new FakeExpression(Integer.toString(value));
			return clit;
		} else if (expression instanceof RealLiteral) {
			RealLiteral lit = (RealLiteral) expression;
			FakeExpression clit = new FakeExpression(lit.getValue());
			return clit;
		} else if (expression instanceof BitvecLiteral) {
			final String value;
			if (cType == null) {
				value = naiveBitvecLiteralValueExtraction((BitvecLiteral) expression);
			} else {
				BigInteger extractedValue = 
						mExpressionTranslation.extractIntegerValue(expression, cType);
				value = String.valueOf(extractedValue);
			}
			FakeExpression clit = new FakeExpression(value);
			return clit;
		} else {
			// things that land here are typically synthesized contracts or
			// things like that
			Expression translated = new SynthesizedExpressionTransformer().processExpression(expression);
			if (translated != null) {
				return new FakeExpression(BoogiePrettyPrinter.print(translated));
			}
			reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
					+ BoogiePrettyPrinter.print(expression) + " has no CACSLLocation");
			return null;
		}

	}
	
	private String naiveBitvecLiteralValueExtraction(BitvecLiteral lit) {
		String value = lit.getValue();
		BigInteger decimalValue = new BigInteger(value);
		boolean isSigned = true;
		if (isSigned ) {
			BigInteger maxRepresentablePositiveValuePlusOne = (new BigInteger("2")).pow(lit.getLength() - 1);
			if (decimalValue.compareTo(maxRepresentablePositiveValuePlusOne) >= 0) {
				BigInteger numberOfValues = (new BigInteger("2")).pow(lit.getLength());
				decimalValue = decimalValue.subtract(numberOfValues);
			}
		}
		return String.valueOf(decimalValue);
	}

	private IASTExpression handleExpressionCASTSimpleDeclaration(Expression expression, CASTSimpleDeclaration decls) {
		// this should only happen for IdentifierExpressions
		if (!(expression instanceof IdentifierExpression)) {
			reportUnfinishedBacktranslation(sUnfinishedBacktranslation + "Expression "
					+ BoogiePrettyPrinter.print(expression)
					+ " is mapped to a declaration, but is no IdentifierExpression");
			return null;
		}

		if (decls.getDeclarators() == null || decls.getDeclarators().length == 0) {
			throw new IllegalArgumentException("Expression " + BoogiePrettyPrinter.print(expression)
					+ " is mapped to a declaration without declarators.");
		}

		if (decls.getDeclarators().length == 1) {
			IdentifierExpression orgidexp = (IdentifierExpression) expression;
			Pair<String,CType> origName = translateIdentifierExpression(orgidexp);
			if (origName == null) {
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": No BoogieVar found for "
						+ BoogiePrettyPrinter.print(expression));
				return null;
			}
			return new FakeExpression(decls, decls.getDeclarators()[0].getName().getRawSignature(), origName.getSecond());
		} else {
			// ok, this is a declaration ala "int a,b;", so we use
			// our backtranslation map to get the real name
			IdentifierExpression orgidexp = (IdentifierExpression) expression;
			Pair<String,CType> origName = translateIdentifierExpression(orgidexp);
			if (origName == null) {
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": No BoogieVar found for "
						+ BoogiePrettyPrinter.print(expression));
				return null;
			}
			for (IASTDeclarator decl : decls.getDeclarators()) {
				if (origName.getFirst().indexOf(decl.getName().getRawSignature()) != -1) {
					return new FakeExpression(decl.getName().getRawSignature());
				}
			}
		}
		reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": IdentifierExpression "
				+ BoogiePrettyPrinter.print(expression)
				+ " has a CASTSimpleDeclaration, but we were unable to determine the variable name from it: "
				+ decls.getRawSignature());
		return null;
	}

	private void reportUnfinishedBacktranslation(String message) {
		mLogger.warn(message);
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID,
				new GenericResult(Activator.s_PLUGIN_ID, sUnfinishedBacktranslation, message, Severity.WARNING));
	}

	private Pair<String,CType> translateIdentifierExpression(IdentifierExpression expr) {
		return translateBoogieIdentifier(expr.getIdentifier());
	}

	private Pair<String,CType> translateBoogieIdentifier(String boogieId) {
		final Pair<String,CType> result;
		if (boogieId.equals(SFO.RES)) {
			result = new Pair<String,CType>("\\result", null);
		} else if (mBoogie2C.getVar2CVar().containsKey(boogieId)) {
			result = mBoogie2C.getVar2CVar().get(boogieId);
		} else if (mBoogie2C.getInVar2CVar().containsKey(boogieId)) {
			Pair<String, CType> inVar = mBoogie2C.getInVar2CVar().get(boogieId);
			String cNameWithOld = "\\old(" + inVar.getFirst() + ")";
			result = new Pair<String,CType>(cNameWithOld, inVar.getSecond());
		} else if (mBoogie2C.getTempVar2Obj().containsKey(boogieId)) {
			result = null;
			reportUnfinishedBacktranslation("auxilliary boogie variable " + boogieId);
		} else if (boogieId.equals(SFO.VALID)) {
			result = new Pair<String,CType>("\\valid", null);
		} else {
			// if its base or offset, try again with them stripped
			if (boogieId.endsWith(SFO.POINTER_BASE)) {
				result = translateBoogieIdentifier(boogieId.substring(0, boogieId.length() - SFO.POINTER_BASE.length()
						- 1));
			} else if (boogieId.endsWith(SFO.POINTER_OFFSET)) {
				result = translateBoogieIdentifier(boogieId.substring(0, boogieId.length() - SFO.POINTER_OFFSET.length()
						- 1));
			} else {
				result = null;
				reportUnfinishedBacktranslation("unknown boogie variable " + boogieId);
			}
		}
		return result;
	}

	void putFunction(String boogieId, String cId) {
		mBoogie2C.putFunction(boogieId, cId);
	}

	public void putVar(String boogieId, String cId, CType cType) {
		mBoogie2C.putVar(boogieId, cId, cType);
	}

	public void putInVar(String boogieId, String cId, CType cType) {
		mBoogie2C.putInVar(boogieId, cId, cType);
	}

	public void putTempVar(String boogieId, SFO.AUXVAR purpose, CType cType) {
		mBoogie2C.putTempVar(boogieId, purpose, cType);
	}

	public boolean isTempVar(String boogieId) {
		return mBoogie2C.getTempVar2Obj().containsKey(boogieId);
	}

	/**
	 * A subtree check that sacrifices memory consumption for speed. It is about
	 * 20x faster, but uses a lookup table.
	 * 
	 * A subtree check is used to determine if a trace element is actually a
	 * nesting of some later trace element in the error path (like in x = x++ +
	 * ++x, were x++ and ++x are nestings of +, and + is a nesting of the
	 * assignment).
	 * 
	 * There may be a better solution to this (its rather expensive).
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 */
	private class CheckForSubtreeInclusion {

		protected List<AtomicTraceElement<CACSLLocation>> check(
				List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements) {

			// first, compute lookup data structure
			HashMap<AtomicTraceElement<CACSLLocation>, HashSet<IASTNode>> ateToParents = new HashMap<>();
			for (int i = 0; i < translatedAtomicTraceElements.size(); ++i) {
				AtomicTraceElement<CACSLLocation> ate = translatedAtomicTraceElements.get(i);

				if (!(ate.getStep() instanceof CLocation)) {
					continue;
				}
				IASTNode origNode = ((CLocation) ate.getStep()).getNode();
				HashSet<IASTNode> parents = new HashSet<>();

				IASTNode currentParent = origNode.getParent();
				while (currentParent != null) {
					parents.add(currentParent);
					currentParent = currentParent.getParent();
				}

				ateToParents.put(ate, parents);
			}

			// second, compute actual tree inclusion check
			List<AtomicTraceElement<CACSLLocation>> rtr = new ArrayList<>();
			for (int i = 0; i < translatedAtomicTraceElements.size(); ++i) {
				AtomicTraceElement<CACSLLocation> ate = translatedAtomicTraceElements.get(i);
				rtr.add(check(ate, translatedAtomicTraceElements, i + 1, StepInfo.EXPR_EVAL, ateToParents));
			}
			return rtr;
		}

		private AtomicTraceElement<CACSLLocation> check(AtomicTraceElement<CACSLLocation> ate,
				List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements, int start, StepInfo newSi,
				HashMap<AtomicTraceElement<CACSLLocation>, HashSet<IASTNode>> ateToParents) {

			HashSet<IASTNode> parents = ateToParents.get(ate);

			if (parents == null) {
				// not implemented for ACSL
				return ate;
			}
			IASTNode origNode = ((CLocation) ate.getStep()).getNode();

			if (!(origNode instanceof IASTExpression)) {
				// do nothing for statements
				return ate;
			}

			for (int j = start; j < translatedAtomicTraceElements.size(); ++j) {
				AtomicTraceElement<CACSLLocation> current = translatedAtomicTraceElements.get(j);
				if (!(current.getStep() instanceof CLocation)) {
					// skip acsl nodes
					continue;
				}
				IASTNode candidate = ((CLocation) current.getStep()).getNode();
				if (parents.contains(candidate)) {
					EnumSet<StepInfo> set = ate.getStepInfo();
					if (set.isEmpty() || set.contains(StepInfo.NONE)) {
						set = EnumSet.of(newSi);
					} else {
						set.add(newSi);
					}
					return new AtomicTraceElement<CACSLLocation>(current.getStep(), ate.getStep(), set);
				}
			}
			return ate;
		}
	}

	private class SynthesizedExpressionTransformer extends BoogieTransformer {

		@Override
		protected Expression processExpression(Expression expr) {
			if (expr instanceof IdentifierExpression) {
				IdentifierExpression ident = (IdentifierExpression) expr;
				ILocation loc = ident.getLocation();
				if (loc instanceof CACSLLocation) {
					IASTExpression translated = translateExpression(ident);
					if (translated != null) {
						return new IdentifierExpression(ident.getLocation(), ident.getType(),
								translated.getRawSignature(), ident.getDeclarationInformation());
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
		protected Statement processStatement(Statement statement) {
			return super.processStatement(statement);
		}

		@Override
		protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
			if (lhs instanceof VariableLHS) {
				mAllAreTemp = mAllAreTemp && isTempVar(((VariableLHS) lhs).getIdentifier());
			}
			return super.processLeftHandSide(lhs);
		}

		@Override
		protected Expression processExpression(Expression expr) {
			if (expr instanceof IdentifierExpression) {
				mAllAreTemp = mAllAreTemp && isTempVar(((IdentifierExpression) expr).getIdentifier());
			}
			return super.processExpression(expr);
		}
	}

	/**
	 * Translates Boogie identifiers of variables and functions back to the
	 * identifiers of variables and operators in C.
	 * 
	 * This class is in an immature state and translates Strings to Strings.
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 * 
	 */
	private static class Boogie2C {

		private final Map<String, Pair<String, CType>> mInVar2CVar;
		private final Map<String, Pair<String, CType>> mVar2CVar;
		private final Map<String, Object> mTempVar2Obj;
		private final Map<String, String> mFunctionId2Operator;

		private Boogie2C() {
			mInVar2CVar = new HashMap<String, Pair<String, CType>>();
			mVar2CVar = new HashMap<String, Pair<String, CType>>();
			mTempVar2Obj = new HashMap<String, Object>();
			mFunctionId2Operator = new HashMap<String, String>();
		}

		private Map<String, Pair<String, CType>> getInVar2CVar() {
			return mInVar2CVar;
		}

		private Map<String, Pair<String, CType>> getVar2CVar() {
			return mVar2CVar;
		}

		private Map<String, Object> getTempVar2Obj() {
			return mTempVar2Obj;
		}

		// private Map<String, String> getFunctionId2Operator() {
		// return mFunctionId2Operator;
		// }

		private void putFunction(String boogieId, String cId) {
			mFunctionId2Operator.put(boogieId, cId);
		}

		private void putVar(String boogieId, String cId, CType cType) {
			mVar2CVar.put(boogieId, new Pair<String, CType>(cId, cType));
		}

		private void putInVar(String boogieId, String cId, CType cType) {
			mInVar2CVar.put(boogieId, new Pair<String, CType>(cId, cType));
		}

		private void putTempVar(String boogieId, SFO.AUXVAR purpose, CType cType) {
			mTempVar2Obj.put(boogieId, purpose);
		}
	}

	private class TemporaryPointerExpression extends Expression {

		public TemporaryPointerExpression(ILocation loc) {
			super(loc);
		}

		public IASTExpression translate() {
			if (mBase instanceof IdentifierExpression) {
				// its a declaration or an access
				return translateExpression(mBase);
			} else {
				// some kind of value
				IASTExpression base = translateExpression(mBase);
				IASTExpression offset = translateExpression(mOffset);
				return new FakeExpression(base, "{" + base.getRawSignature() + ":" + offset.getRawSignature() + "}", null);
			}
		}

		private static final long serialVersionUID = 1L;
		private Expression mBase;
		private Expression mOffset;

		public void setBase(Expression expr) {
			mBase = expr;
		}

		public void setOffset(Expression expr) {
			mOffset = expr;
		}

		@Override
		public String toString() {
			return mBase.toString() + " " + mOffset.toString();
		}
	}

	private class MyEntry<K, T> implements Entry<K, T> {

		private K Key;
		private T Value;

		@Override
		public K getKey() {
			return Key;
		}

		@Override
		public T getValue() {
			return Value;
		}

		@Override
		public T setValue(T value) {
			T oldValue = Value;
			Value = value;
			return oldValue;
		}
	}



}
