package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionCallExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDefinition;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIfStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

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

	public CACSL2BoogieBacktranslator(IUltimateServiceProvider services) {
		super(BoogieASTNode.class, CACSLLocation.class, Expression.class, IASTExpression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mBoogie2C = new Boogie2C();
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

			if (loc instanceof CACSLLocation) {
				// i = findMergeSequence(programExecution, i, loc);

				CACSLLocation cloc = (CACSLLocation) loc;
				IASTNode cnode = cloc.getCNode();
				ACSLNode anode = cloc.getAcslNode();
				if (cnode != null) {
					// TODO: um while, if,call, return etc. kümmern
					if (cnode instanceof CASTTranslationUnit) {
						// we skip all CASTTranslationUnit locs because they
						// correspond to Ultimate.init() and Ultimate.start()
						// and we dont know how to backtranslate them meaningful

						// but we should make the initial state here
						i = findMergeSequence(programExecution, i, loc);
						initialState = translateProgramState(programExecution.getProgramState(i));
						continue;
					} else if (cnode instanceof CASTIfStatement) {
						// if its an if, we point to the condition
						CASTIfStatement ifstmt = (CASTIfStatement) cnode;
						IASTExpression expr = ifstmt.getConditionExpression();
						translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc,
								new CACSLLocation(expr), ate.getStepInfo()));
					} else if (cnode instanceof CASTFunctionCallExpression) {
						i = handleCASTFunctionCallExpression(programExecution, i, (CASTFunctionCallExpression) cnode,
								cloc, translatedAtomicTraceElements, translatedProgramStates);
						continue;
					} else {
						// for now, just use C as it
						i = findMergeSequence(programExecution, i, loc);
						String raw = cnode.getRawSignature();
						translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc));
					}
				} else if (anode != null) {
					// for now, just use ACSL as-it
					translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc));

				} else {
					reportUnfinishedBacktranslation(sUnfinishedBacktranslation
							+ ": Invalid location (neither IASTNode nor ACSLNode present)");
					// skip program state for this one
					continue;
				}
				translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));

			} else {
				// invalid location
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation
						+ ": Invalid location (Location is no CACSLLocation)");
			}
		}

		return new CACSLProgramExecution(initialState, translatedAtomicTraceElements, translatedProgramStates);

	}

	private int handleCASTFunctionCallExpression(IProgramExecution<BoogieASTNode, Expression> programExecution, int i,
			CASTFunctionCallExpression fcall, CACSLLocation cloc,
			List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements,
			List<ProgramState<IASTExpression>> translatedProgramStates) {
		// directly after the functioncall expression we find
		// for each argument a CASTFunctionDefinition / AssignmentStatement that
		// maps the input variable to a new local one (because boogie function
		// params are immutable)
		// we throw them away
		AtomicTraceElement<BoogieASTNode> origFuncCall = programExecution.getTraceElement(i);

		if (origFuncCall.getStepInfo() == StepInfo.NONE) {
			// this is some temp var stuff; we can safely ignore it
			return i;
		}

		translatedAtomicTraceElements
				.add(new AtomicTraceElement<CACSLLocation>(cloc, cloc, origFuncCall.getStepInfo()));
		translatedProgramStates.add(translateProgramState(programExecution.getProgramState(i)));

		if (origFuncCall.getStepInfo() == StepInfo.RETURN) {
			// if it is a return we are already finished.
			return i;
		}

		int j = i + 1;
		for (int k = 0; k < fcall.getArguments().length && j < programExecution.getLength(); ++j, ++k) {
			AtomicTraceElement<BoogieASTNode> origFuncDef = programExecution.getTraceElement(j);

			if (!(origFuncDef.getTraceElement() instanceof AssignmentStatement)) {
				reportUnfinishedBacktranslation("CASTFunctionCallExpression is followed by "
						+ origFuncDef.getTraceElement().getClass().getSimpleName());
				return i;
			}

			if (!(origFuncDef.getTraceElement().getLocation() instanceof CACSLLocation)) {
				reportUnfinishedBacktranslation("CASTFunctionCallExpression is followed by some unknown location: "
						+ origFuncDef.getTraceElement().getLocation().getClass().getSimpleName());
				return i;
			}
			IASTNode cnode = ((CACSLLocation) origFuncDef.getTraceElement().getLocation()).getCNode();
			if (!(cnode instanceof CASTFunctionDefinition)) {
				reportUnfinishedBacktranslation("After CASTFunctionCallExpression should follow a "
						+ "CASTFunctionDefinition for each argument, but was: " + cnode.getClass().getSimpleName());
				return i;
			}

			// there is no backtranslation for this assign, but maybe we need it
			// to track the body vars?
			// AssignmentStatement assign = (AssignmentStatement)
			// origFuncDef.getTraceElement();
			// IdentifierExpression origInParam = new
			// LHSIdentifierExtractor().extract(assign);
			// IASTExpression inParam = translateExpression(origInParam);
			//
			// translatedAtomicTraceElements.add(new
			// AtomicTraceElement<CACSLLocation>(cloc, new
			// CACSLLocation(inParam),
			// StepInfo.ARG_EVAL));
			//
			// translatedProgramStates.add(translateProgramState(programExecution.getProgramState(j)));
		}

		i = j;
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

			for (Expression varName : programState.getVariables()) {
				IASTExpression newVarName = translateExpression(varName);
				if (newVarName == null) {
					continue;
				}

				Collection<Expression> varValues = programState.getValues(varName);
				Collection<IASTExpression> newVarValues = new ArrayList<>();
				for (Expression varValue : varValues) {
					IASTExpression newVarValue = translateExpression(varValue);
					if (newVarValue != null) {
						newVarValues.add(newVarValue);
					}
				}
				if (newVarValues.size() > 0) {
					map.put(newVarName, newVarValues);
				}
			}
			if (map.isEmpty()) {
				return null;
			}
			return new ProgramState<IASTExpression>(map);
		}
		return null;
	}

	@Override
	public IASTExpression translateExpression(Expression expression) {
		if (expression instanceof UnaryExpression) {
			// handle old vars
			UnaryExpression uexp = (UnaryExpression) expression;
			if (uexp.getOperator() == Operator.OLD) {
				IASTExpression innerTrans = translateExpression(uexp.getExpr());
				if (innerTrans == null) {
					return null;
				}
				FakeExpression fexp = new FakeExpression("\\old(" + innerTrans.getRawSignature() + ")");
				return fexp;
			}
		}

		ILocation loc = expression.getLocation();
		if (loc instanceof CACSLLocation) {
			CACSLLocation cloc = (CACSLLocation) loc;
			IASTNode cnode = cloc.getCNode();
			if (cnode != null) {
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
						IdentifierExpression orgidexp = (IdentifierExpression) expression;
						String origName = translateIdentifierExpression(orgidexp);
						if (origName != null) {
							return new FakeExpression(origName);
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
			} else {
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
						+ BoogiePrettyPrinter.print(expression)
						+ " has no C AST node and ACSL nodes are not yet supported");
				return null;
			}

		} else if (expression instanceof IntegerLiteral) {
			IntegerLiteral lit = (IntegerLiteral) expression;
			FakeExpression clit = new FakeExpression(lit.getValue());
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
		} else {
			reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": Expression "
					+ BoogiePrettyPrinter.print(expression) + " has no CACSLLocation");
			return null;
		}

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

		FakeExpression idexp = new FakeExpression();
		if (decls.getDeclarators().length == 1) {
			idexp.setNameOrValue(decls.getDeclarators()[0].getName().getRawSignature());
			return idexp;
		} else {
			// ok, this is a declaration ala "int a,b;", so we use
			// our backtranslation map to get the real name
			IdentifierExpression orgidexp = (IdentifierExpression) expression;
			String origName = translateIdentifierExpression(orgidexp);
			if (origName == null) {
				reportUnfinishedBacktranslation(sUnfinishedBacktranslation + ": No BoogieVar found for "
						+ BoogiePrettyPrinter.print(expression));
				return null;
			}
			for (IASTDeclarator decl : decls.getDeclarators()) {
				if (origName.indexOf(decl.getName().getRawSignature()) != -1) {
					idexp.setNameOrValue(decl.getName().getRawSignature());
					return idexp;
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

	// private String translateBinExpOp(BinaryExpression.Operator op) {
	// switch (op) {
	// case ARITHDIV:
	// return "/";
	// case ARITHMINUS:
	// return "-";
	// case ARITHMOD:
	// return "%";
	// case ARITHMUL:
	// return "*";
	// case ARITHPLUS:
	// return "+";
	// case BITVECCONCAT:
	// throw new UnsupportedOperationException("Unsupported BITVECCONCAT");
	// case COMPEQ:
	// return "==";
	// case COMPGEQ:
	// return ">=";
	// case COMPGT:
	// return ">";
	// case COMPLEQ:
	// return "<=";
	// case COMPLT:
	// return "<";
	// case COMPNEQ:
	// return "!=";
	// case COMPPO:
	// throw new UnsupportedOperationException("Unsupported COMPPO");
	// case LOGICAND:
	// return "&&";
	// case LOGICIFF:
	// return "<==>";
	// case LOGICIMPLIES:
	// return "==>";
	// case LOGICOR:
	// return "||";
	// default:
	// throw new UnsupportedOperationException("Unknown binary operator");
	// }
	// }

	// private String translateUnExpOp(UnaryExpression.Operator op) {
	// switch (op) {
	// case ARITHNEGATIVE:
	// return "-";
	// case LOGICNEG:
	// return "!";
	// case OLD:
	// return "\\old";
	// default:
	// throw new UnsupportedOperationException("Unknown unary operator");
	// }
	// }

	private String translateIdentifierExpression(IdentifierExpression expr) {
		String boogieId = expr.getIdentifier();
		String cId = null;

		// TODO deal with base and offset

		if (boogieId.equals(SFO.RES)) {
			cId = "\\result";
		} else if (mBoogie2C.getVar2CVar().containsKey(boogieId)) {
			cId = mBoogie2C.getVar2CVar().get(boogieId);
		} else if (mBoogie2C.getInVar2CVar().containsKey(boogieId)) {
			cId = "\\old(" + mBoogie2C.getInVar2CVar().get(boogieId) + ")";
		} else if (mBoogie2C.getTempVar2Obj().containsKey(boogieId)) {
			reportUnfinishedBacktranslation("auxilliary boogie variable " + boogieId);
		} else if (boogieId.equals(SFO.VALID)) {
			cId = "\\valid";
		} else {
			reportUnfinishedBacktranslation("unknown boogie variable " + boogieId);
		}
		return cId;
	}

	// private String processExpression(Expression expr) {
	// if (expr instanceof BinaryExpression) {
	// BinaryExpression binexp = (BinaryExpression) expr;
	// String left = processExpression(binexp.getLeft());
	// String right = processExpression(binexp.getRight());
	// if (binexp.getOperator() == BinaryExpression.Operator.LOGICAND) {
	// return left + " " + translateBinExpOp(binexp.getOperator()) + " " +
	// right;
	// } else {
	// return "(" + left + translateBinExpOp(binexp.getOperator()) + right +
	// ")";
	// }
	// } else if (expr instanceof UnaryExpression) {
	// UnaryExpression unexp = (UnaryExpression) expr;
	// String subexpr = processExpression(unexp.getExpr());
	// String operator = translateUnExpOp(unexp.getOperator());
	// if (unexp.getOperator().equals(UnaryExpression.Operator.OLD)) {
	// return operator + "(" + subexpr + ")";
	// } else if (unexp.getOperator().equals(UnaryExpression.Operator.LOGICNEG))
	// {
	// if (!subexpr.startsWith("(")) {
	// subexpr = "(" + subexpr + ")";
	// }
	// return operator + subexpr;
	// } else if
	// (unexp.getOperator().equals(UnaryExpression.Operator.ARITHNEGATIVE)) {
	// return operator + subexpr;
	// } else {
	// throw new IllegalArgumentException("unknown unary operator");
	// }
	// } else if (expr instanceof ArrayAccessExpression) {
	// ArrayAccessExpression aae = (ArrayAccessExpression) expr;
	// String array = processExpression(aae.getArray());
	// String indices[] = new String[aae.getIndices().length];
	// for (int i = 0; i < indices.length; i++) {
	// indices[i] = processExpression(aae.getIndices()[i]);
	// }
	// return array + Arrays.toString(indices);
	// } else if (expr instanceof ArrayStoreExpression) {
	// throw new
	// UnsupportedOperationException("Unsupported ArrayStoreExpression");
	// } else if (expr instanceof BitVectorAccessExpression) {
	// throw new
	// UnsupportedOperationException("Unsupported BitVectorAccessExpression");
	// } else if (expr instanceof FunctionApplication) {
	// throw new
	// UnsupportedOperationException("Unsupported FunctionApplication");
	// } else if (expr instanceof IfThenElseExpression) {
	// IfThenElseExpression ite = (IfThenElseExpression) expr;
	// String cond = processExpression(ite.getCondition());
	// String thenPart = processExpression(ite.getThenPart());
	// String elsePart = processExpression(ite.getElsePart());
	// return "(" + cond + " ? " + thenPart + " : " + elsePart + ")";
	// } else if (expr instanceof QuantifierExpression) {
	// throw new
	// UnsupportedOperationException("Unsupported QuantifierExpression");
	// } else if (expr instanceof IdentifierExpression) {
	// return translateIdentifierExpression((IdentifierExpression) expr);
	// } else if (expr instanceof IntegerLiteral) {
	// IntegerLiteral intLit = (IntegerLiteral) expr;
	// return intLit.getValue();
	// } else if (expr instanceof BooleanLiteral) {
	// BooleanLiteral boolLit = (BooleanLiteral) expr;
	// if (boolLit.getValue()) {
	// return "\\true";
	// } else {
	// return "\\false";
	// }
	// } else if (expr instanceof RealLiteral) {
	// RealLiteral realLit = (RealLiteral) expr;
	// return realLit.getValue();
	// }
	// throw new UnsupportedOperationException("Unknown Expression");
	// }

	void putFunction(String boogieId, String cId) {
		mBoogie2C.putFunction(boogieId, cId);
	}

	public void putVar(String boogieId, String cId) {
		mBoogie2C.putVar(boogieId, cId);
	}

	public void putInVar(String boogieId, String cId) {
		mBoogie2C.putInVar(boogieId, cId);
	}

	public void putTempVar(String boogieId, Object obj) {
		mBoogie2C.putTempVar(boogieId, obj);
	}

	private class LHSIdentifierExtractor extends BoogieTransformer {
		private IdentifierExpression mResult;
		private int mCount;

		private IdentifierExpression extract(AssignmentStatement assign) {
			mCount = 0;
			processStatement(assign);
			if (mCount > 1) {
				throw new UnsupportedOperationException("Forgot one IdentifierExpression");
			}
			return mResult;
		}

		@Override
		protected Expression processExpression(Expression expr) {
			if (expr instanceof IdentifierExpression) {
				mResult = (IdentifierExpression) expr;
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

		private final Map<String, String> mInVar2CVar;
		private final Map<String, String> mVar2CVar;
		private final Map<String, Object> mTempVar2Obj;
		private final Map<String, String> mFunctionId2Operator;

		private Boogie2C() {
			mInVar2CVar = new HashMap<String, String>();
			mVar2CVar = new HashMap<String, String>();
			mTempVar2Obj = new HashMap<String, Object>();
			mFunctionId2Operator = new HashMap<String, String>();
		}

		private Map<String, String> getInVar2CVar() {
			return mInVar2CVar;
		}

		private Map<String, String> getVar2CVar() {
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

		private void putVar(String boogieId, String cId) {
			mVar2CVar.put(boogieId, cId);
		}

		private void putInVar(String boogieId, String cId) {
			mInVar2CVar.put(boogieId, cId);
		}

		private void putTempVar(String boogieId, Object obj) {
			mTempVar2Obj.put(boogieId, obj);
		}
	}

	public boolean isTempVar(String boogieId) {
		return mBoogie2C.getTempVar2Obj().containsKey(boogieId);
	}

}
