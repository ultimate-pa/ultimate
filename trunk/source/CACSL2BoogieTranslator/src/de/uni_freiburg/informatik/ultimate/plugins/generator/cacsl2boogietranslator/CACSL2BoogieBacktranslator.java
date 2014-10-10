package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionCallExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIfStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler.Boogie2C;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
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

		// trace and program state in tandem
		List<AtomicTraceElement<CACSLLocation>> translatedAtomicTraceElements = new ArrayList<>();
		List<ProgramState<IASTExpression>> translatedProgramStates = new ArrayList<>();
		for (int i = 0; i < programExecution.getLength(); ++i) {

			AtomicTraceElement<BoogieASTNode> ate = programExecution.getTraceElement(i);

			ILocation loc = ate.getTraceElement().getLocation();
			if (loc instanceof CACSLLocation) {
				// alles gut, damit machen wir weiter ...
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

				CACSLLocation cloc = (CACSLLocation) loc;
				IASTNode cnode = cloc.getCNode();
				ACSLNode anode = cloc.getAcslNode();
				if (cnode != null) {
					// TODO: um while, if,call, return etc. kümmern
					if (cnode instanceof CASTTranslationUnit) {
						// we skip all CASTTranslationUnit locs because they
						// correspond to Ultimate.init() and Ultimate.start()
						// and we dont know how to backtranslate them meaningful
						continue;
					} else if (cnode instanceof CASTIfStatement) {
						// if its an if, we point to the condition
						CASTIfStatement ifstmt = (CASTIfStatement) cnode;
						IASTExpression expr = ifstmt.getConditionExpression();
						translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc,
								new CACSLLocation(expr), ate.getStepInfo()));
					} else if (cnode instanceof CASTFunctionCallExpression) {
						// TODO: continue here 
						translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc));
					} else {
						// for now, just take it as it
						translatedAtomicTraceElements.add(new AtomicTraceElement<CACSLLocation>(cloc));
					}
				} else if (anode != null) {
					// for now, just use it as-it
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

		return new CProgramExecution(initialState, translatedAtomicTraceElements, translatedProgramStates);

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
					// this should only happen for IdentifierExpressions
					if (!(expression instanceof IdentifierExpression)) {
						throw new IllegalArgumentException("Expression " + BoogiePrettyPrinter.print(expression)
								+ " is mapped to a declaration, but is no IdentifierExpression");
					}

					CASTSimpleDeclaration decls = (CASTSimpleDeclaration) cnode;

					if (decls.getDeclarators() == null || decls.getDeclarators().length == 0) {
						throw new IllegalArgumentException("Expression " + BoogiePrettyPrinter.print(expression)
								+ " is mapped to a declaration without declarators.");
					}

					FakeExpression idexp = new FakeExpression();
					if (decls.getDeclarators().length == 1) {
						idexp.setNameOrValue(decls.getDeclarators()[0].getName().getRawSignature());
						return idexp;
					} else {
						// ok, this is a declaration ala "int a,b;", so we guess
						// the name
						IdentifierExpression orgidexp = (IdentifierExpression) expression;
						for (IASTDeclarator decl : decls.getDeclarators()) {
							if (orgidexp.getIdentifier().indexOf(decl.getName().getRawSignature()) != -1) {
								idexp.setNameOrValue(decl.getName().getRawSignature());
								return idexp;
							}
						}
					}
					reportUnfinishedBacktranslation(sUnfinishedBacktranslation
							+ ": IdentifierExpression "
							+ BoogiePrettyPrinter.print(expression)
							+ " has a CASTSimpleDeclaration, but we were unable to determine the variable name from it: "
							+ decls.getRawSignature());
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

	public void setBoogie2C(Boogie2C boogie2c) {
		mBoogie2C = boogie2c;
	}

	private void reportUnfinishedBacktranslation(String message) {
		mLogger.warn(message);
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID,
				new GenericResult(Activator.s_PLUGIN_ID, sUnfinishedBacktranslation, message, Severity.WARNING));
	}

	private String translateBinExpOp(BinaryExpression.Operator op) {
		switch (op) {
		case ARITHDIV:
			return "/";
		case ARITHMINUS:
			return "-";
		case ARITHMOD:
			return "%";
		case ARITHMUL:
			return "*";
		case ARITHPLUS:
			return "+";
		case BITVECCONCAT:
			throw new UnsupportedOperationException("Unsupported BITVECCONCAT");
		case COMPEQ:
			return "==";
		case COMPGEQ:
			return ">=";
		case COMPGT:
			return ">";
		case COMPLEQ:
			return "<=";
		case COMPLT:
			return "<";
		case COMPNEQ:
			return "!=";
		case COMPPO:
			throw new UnsupportedOperationException("Unsupported COMPPO");
		case LOGICAND:
			return "&&";
		case LOGICIFF:
			return "<==>";
		case LOGICIMPLIES:
			return "==>";
		case LOGICOR:
			return "||";
		default:
			throw new UnsupportedOperationException("Unknown binary operator");
		}
	}

	private String translateUnExpOp(UnaryExpression.Operator op) {
		switch (op) {
		case ARITHNEGATIVE:
			return "-";
		case LOGICNEG:
			return "!";
		case OLD:
			return "\\old";
		default:
			throw new UnsupportedOperationException("Unknown unary operator");
		}
	}

	private String translateIdentifierExpression(IdentifierExpression expr) {
		final String boogieId = ((IdentifierExpression) expr).getIdentifier();
		final String cId;
		if (boogieId.equals(SFO.RES)) {
			cId = "\\result";
		} else if (mBoogie2C.getVar2cvar().containsKey(boogieId)) {
			cId = mBoogie2C.getVar2cvar().get(boogieId);
		} else if (mBoogie2C.getInvar2cvar().containsKey(boogieId)) {
			cId = "\\old(" + mBoogie2C.getInvar2cvar().get(boogieId) + ")";
		} else if (mBoogie2C.getTempvar2obj().containsKey(boogieId)) {
			throw new UnsupportedOperationException("auxilliary boogie variable " + boogieId);
		} else if (boogieId.equals(SFO.VALID)) {
			cId = "\\valid";
		} else {
			// FIXME: handle unknown variables
			return boogieId;
			// throw new
			// UnsupportedOperationException("unknown boogie variable " +
			// boogieId);
		}
		return cId;
	}

	private String processExpression(Expression expr) {
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) expr;
			String left = processExpression(binexp.getLeft());
			String right = processExpression(binexp.getRight());
			if (binexp.getOperator() == BinaryExpression.Operator.LOGICAND) {
				return left + " " + translateBinExpOp(binexp.getOperator()) + " " + right;
			} else {
				return "(" + left + translateBinExpOp(binexp.getOperator()) + right + ")";
			}
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			String subexpr = processExpression(unexp.getExpr());
			String operator = translateUnExpOp(unexp.getOperator());
			if (unexp.getOperator().equals(UnaryExpression.Operator.OLD)) {
				return operator + "(" + subexpr + ")";
			} else if (unexp.getOperator().equals(UnaryExpression.Operator.LOGICNEG)) {
				if (!subexpr.startsWith("(")) {
					subexpr = "(" + subexpr + ")";
				}
				return operator + subexpr;
			} else if (unexp.getOperator().equals(UnaryExpression.Operator.ARITHNEGATIVE)) {
				return operator + subexpr;
			} else {
				throw new IllegalArgumentException("unknown unary operator");
			}
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression aae = (ArrayAccessExpression) expr;
			String array = processExpression(aae.getArray());
			String indices[] = new String[aae.getIndices().length];
			for (int i = 0; i < indices.length; i++) {
				indices[i] = processExpression(aae.getIndices()[i]);
			}
			return array + Arrays.toString(indices);
		} else if (expr instanceof ArrayStoreExpression) {
			throw new UnsupportedOperationException("Unsupported ArrayStoreExpression");
		} else if (expr instanceof BitVectorAccessExpression) {
			throw new UnsupportedOperationException("Unsupported BitVectorAccessExpression");
		} else if (expr instanceof FunctionApplication) {
			throw new UnsupportedOperationException("Unsupported FunctionApplication");
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			String cond = processExpression(ite.getCondition());
			String thenPart = processExpression(ite.getThenPart());
			String elsePart = processExpression(ite.getElsePart());
			return "(" + cond + " ? " + thenPart + " : " + elsePart + ")";
		} else if (expr instanceof QuantifierExpression) {
			throw new UnsupportedOperationException("Unsupported QuantifierExpression");
		} else if (expr instanceof IdentifierExpression) {
			return translateIdentifierExpression((IdentifierExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			IntegerLiteral intLit = (IntegerLiteral) expr;
			return intLit.getValue();
		} else if (expr instanceof BooleanLiteral) {
			BooleanLiteral boolLit = (BooleanLiteral) expr;
			if (boolLit.getValue()) {
				return "\\true";
			} else {
				return "\\false";
			}
		} else if (expr instanceof RealLiteral) {
			RealLiteral realLit = (RealLiteral) expr;
			return realLit.getValue();
		}
		throw new UnsupportedOperationException("Unknown Expression");
	}

}
