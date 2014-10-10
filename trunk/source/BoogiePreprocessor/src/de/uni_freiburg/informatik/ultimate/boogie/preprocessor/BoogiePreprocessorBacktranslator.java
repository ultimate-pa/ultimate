package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructType;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class BoogiePreprocessorBacktranslator extends
		DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression> {

	private final Logger mLogger;
	/**
	 * Mapping from target nodes to source nodes (i.e. output to input)
	 */
	private final HashMap<BoogieASTNode, BoogieASTNode> mMapping;
	private final IUltimateServiceProvider mServices;
	private BoogieSymbolTable mSymbolTable;

	protected BoogiePreprocessorBacktranslator(IUltimateServiceProvider services) {
		super(BoogieASTNode.class, BoogieASTNode.class, Expression.class, Expression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMapping = new HashMap<>();
	}

	public BoogieSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public void setSymbolTable(BoogieSymbolTable symbolTable) {
		mSymbolTable = symbolTable;
	}

	protected void addMapping(BoogieASTNode inputNode, BoogieASTNode outputNode) {
		BoogieASTNode realInputNode = mMapping.get(inputNode);
		if (realInputNode == null) {
			realInputNode = inputNode;
		}
		mMapping.put(outputNode, realInputNode);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Create mapping between");
			mLogger.debug("\tOutput " + printDebug(outputNode));
			mLogger.debug("\tInput  " + printDebug(realInputNode));
		}
	}

	@Override
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {

		List<BoogieASTNode> newTrace = new ArrayList<>();
		Map<Integer, ProgramState<Expression>> newPartialProgramStateMapping = new HashMap<>();

		newPartialProgramStateMapping.put(-1, backtranslateProgramState(programExecution.getInitialProgramState()));

		int length = programExecution.getLength();
		for (int i = 0; i < length; ++i) {
			BoogieASTNode elem = programExecution.getTraceElement(i).getTraceElement();
			// the call to backtranslateTraceElements may produce null values,
			// but we keep them anyways s.t. the indices between newTrace and
			// programExecution match
			newTrace.add(backtranslateTraceElement(elem));

			newPartialProgramStateMapping.put(i, backtranslateProgramState(programExecution.getProgramState(i)));
		}

		// return super.translateProgramExecution(programExecution);
		return createProgramExecutionFromTrace(newTrace, newPartialProgramStateMapping, programExecution);
	}

	private ProgramState<Expression> backtranslateProgramState(ProgramState<Expression> state) {
		if (state == null) {
			return null;
		} else {
			Map<Expression, Collection<Expression>> newVariable2Values = new HashMap<>();
			for (Expression var : state.getVariables()) {
				Expression newVar = translateExpression(var);
				Collection<Expression> newValues = new ArrayList<>();
				for (Expression value : state.getValues(var)) {
					newValues.add(translateExpression(value));
				}
				newVariable2Values.put(newVar, newValues);
			}
			return new ProgramState<>(newVariable2Values);
		}
	}

	private BoogieASTNode backtranslateTraceElement(BoogieASTNode elem) {
		BoogieASTNode newElem = mMapping.get(elem);

		if (newElem == null) {
			if (elem instanceof EnsuresSpecification) {
				EnsuresSpecification spec = (EnsuresSpecification) elem;
				Expression formula = spec.getFormula();
				if (formula instanceof BooleanLiteral) {
					if (((BooleanLiteral) formula).getValue()) {
						// we come to this place because this
						// EnuresSpecification was inserted by RCFG Builder and
						// does not provide any additional information. We
						// safely exclude it from the error path.
						return null;
					}
				}
				// if we reach this point, we have an EnuresSpecification that
				// was not inserted by the user (probably by RCFGBuilder),
				// because there is no mapping, and that this spec is
				// unexpected. If this happens, we have to find a strategy for
				// that, so we throw an exception here.
				throw new UnsupportedOperationException("Generated EnsuresSpecification "
						+ BoogiePrettyPrinter.print(spec) + " is not ensure(true)");
			}
			// if there is no mapping, we return the identity (we do not change
			// everything, so this may be right)
			return elem;
		} else if (newElem instanceof Statement) {
			return newElem;
		} else {
			reportUnfinishedBacktranslation("Unfinished backtranslation: Ignored translation of "
					+ newElem.getClass().getSimpleName());
			return null;
		}

	}

	private IProgramExecution<BoogieASTNode, Expression> createProgramExecutionFromTrace(
			List<BoogieASTNode> translatedTrace, Map<Integer, ProgramState<Expression>> partialProgramStateMapping,
			IProgramExecution<BoogieASTNode, Expression> programExecution) {

		List<AtomicTraceElement<BoogieASTNode>> atomicTrace = new ArrayList<>();

		for (int i = 0; i < translatedTrace.size(); ++i) {
			BoogieASTNode elem = translatedTrace.get(i);

			if (elem == null) {
				// we kept the null values so that indices match between trace
				// and inputProgramExecution
				continue;
			}

			if (elem instanceof WhileStatement) {
				// check if the next statement in the error trace is part of the
				// body of the WhileStatement. If so, the condition evaluated to
				// true; if not or if the trace ends, the condition evaluated to
				// false
				WhileStatement stmt = (WhileStatement) elem;
				boolean condEval = false;
				int nxt = i + 1;
				if (nxt < translatedTrace.size()) {
					BoogieASTNode nextStmt = translatedTrace.get(nxt);
					for (Statement bodyStmt : stmt.getBody()) {
						if (nextStmt == bodyStmt) {
							condEval = true;
						}
					}
				}
				atomicTrace.add(new AtomicTraceElement<BoogieASTNode>(stmt, stmt.getCondition(),
						condEval ? StepInfo.CONDITION_EVAL_TRUE : StepInfo.CONDITION_EVAL_FALSE));

			} else if (elem instanceof IfStatement) {
				// check if the next statement in the error trace is part of the
				// then-part of the IfStatement. If so, the condition evaluated
				// to true; if not or if the trace ends, the condition evaluated
				// to false
				IfStatement stmt = (IfStatement) elem;
				boolean condEval = false;
				int nxt = i + 1;
				if (nxt < translatedTrace.size()) {
					BoogieASTNode nextStmt = translatedTrace.get(nxt);
					for (Statement bodyStmt : stmt.getThenPart()) {
						if (nextStmt == bodyStmt) {
							condEval = true;
						}
					}
				}
				atomicTrace.add(new AtomicTraceElement<BoogieASTNode>(stmt, stmt.getCondition(),
						condEval ? StepInfo.CONDITION_EVAL_TRUE : StepInfo.CONDITION_EVAL_FALSE));

			} else if (elem instanceof CallStatement) {
				// for call statements, we simply rely on the stepinfo of our
				// input
				atomicTrace.add(new AtomicTraceElement<BoogieASTNode>(elem, elem, programExecution.getTraceElement(i)
						.getStepInfo()));

			} else {
				// it could be that we missed some cases... revisit this if you
				// suspect errors in the backtranslation
				atomicTrace.add(new AtomicTraceElement<BoogieASTNode>(elem));
			}
		}

		// we need to clear the null values before creating the final
		// BoogieProgramExecution
		List<AtomicTraceElement<BoogieASTNode>> actualAtomicTrace = new ArrayList<>();
		for (AtomicTraceElement<BoogieASTNode> possibleNullElem : atomicTrace) {
			if (possibleNullElem != null) {
				actualAtomicTrace.add(possibleNullElem);
			}
		}
		return new BoogieProgramExecution(partialProgramStateMapping, actualAtomicTrace);
	}

	@Override
	public List<BoogieASTNode> translateTrace(List<BoogieASTNode> trace) {
		return super.translateTrace(trace);
	}

	@Override
	public Expression translateExpression(Expression expression) {
		return new ExpressionTranslator().processExpression(expression);
	}

	@Override
	public String targetExpressionToString(Expression expression) {
		return BoogiePrettyPrinter.print(expression);
	}

	@Override
	public List<String> targetTraceToString(List<BoogieASTNode> trace) {
		List<String> rtr = new ArrayList<>();
		for (BoogieASTNode node : trace) {
			if (node instanceof Statement) {
				rtr.add(BoogiePrettyPrinter.print((Statement) node));
			} else {
				return super.targetTraceToString(trace);
			}
		}
		return rtr;
	}

	private void reportUnfinishedBacktranslation(String message) {
		mLogger.warn(message);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new GenericResult(Activator.PLUGIN_ID, "Unfinished Backtranslation", message, Severity.WARNING));
	}

	private String printDebug(BoogieASTNode node) {
		if (node instanceof Statement) {
			return BoogiePrettyPrinter.print((Statement) node);
		}

		if (node instanceof Expression) {
			return BoogiePrettyPrinter.print((Expression) node);
		}

		if (node instanceof Procedure) {
			return BoogiePrettyPrinter.printSignature((Procedure) node);
		}

		if (node instanceof VarList) {
			return BoogiePrettyPrinter.print((VarList) node);
		}

		StringBuilder output = new StringBuilder();
		output.append(node.getClass().getSimpleName());
		ILocation loc = node.getLocation();

		if (loc != null) {
			int start = loc.getStartLine();
			int end = loc.getEndLine();

			output.append(" L");
			output.append(start);
			if (start != end) {
				output.append(":");
				output.append(end);
			}

			int startC = loc.getStartColumn();
			int endC = loc.getEndColumn();
			output.append(" C");
			output.append(startC);

			if (startC != endC) {
				output.append(":");
				output.append(endC);
			}
		}
		return output.toString();
	}

	private class ExpressionTranslator extends BoogieTransformer {

		@Override
		protected Expression processExpression(Expression expr) {
			if (mSymbolTable == null) {
				reportUnfinishedBacktranslation("No symboltable available, using identity as back-translation of "
						+ expr);
				return expr;
			}

			if (expr instanceof IdentifierExpression) {
				IdentifierExpression ident = (IdentifierExpression) expr;
				if (((IdentifierExpression) expr).getDeclarationInformation() == null) {
					reportUnfinishedBacktranslation("Identifier has no declaration information, using identity as back-translation of "
							+ expr);
					return expr;
				}
				Declaration decl = mSymbolTable.getDeclaration(ident);

				if (decl == null) {
					reportUnfinishedBacktranslation("No declaration in symboltable, using identity as back-translation of "
							+ expr);
					return expr;
				}
				BoogieASTNode newDecl = mMapping.get(decl);
				if (newDecl instanceof Declaration) {
					return extractIdentifier((Declaration) newDecl, ident);
				} else {
					// this is ok
					return expr;
				}
			}
			// descend
			return super.processExpression(expr);
		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, IdentifierExpression inputExp) {
			IdentifierExpression rtr = inputExp;
			if (mappedDecl instanceof VariableDeclaration) {
				VariableDeclaration mappedVarDecl = (VariableDeclaration) mappedDecl;
				rtr = extractIdentifier(mappedVarDecl, mappedVarDecl.getVariables(), inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
				reportUnfinishedBacktranslation("Unfinished backtranslation: Name guessing unsuccessful for VarDecl "
						+ BoogiePrettyPrinter.print(mappedVarDecl) + " and expression "
						+ BoogiePrettyPrinter.print(inputExp));

			} else if (mappedDecl instanceof Procedure) {
				Procedure proc = (Procedure) mappedDecl;
				rtr = extractIdentifier(proc, proc.getInParams(), inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
				rtr = extractIdentifier(proc, proc.getOutParams(), inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
				reportUnfinishedBacktranslation("Unfinished backtranslation: Name guessing unsuccessful for Procedure "
						+ BoogiePrettyPrinter.printSignature(proc) + " and expression "
						+ BoogiePrettyPrinter.print(inputExp));
			} else {
				reportUnfinishedBacktranslation("Unfinished backtranslation: Declaration "
						+ mappedDecl.getClass().getSimpleName() + " not handled for expression "
						+ BoogiePrettyPrinter.print(inputExp));
			}

			return rtr;
		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, VarList[] list,
				IdentifierExpression inputExp) {
			if (list == null || list.length == 0) {
				return inputExp;
			}
			IdentifierExpression rtr = inputExp;
			for (VarList lil : list) {
				rtr = extractIdentifier(mappedDecl, lil, inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
			}
			return rtr;
		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, VarList list,
				IdentifierExpression inputExp) {
			if (list == null) {
				return inputExp;
			}
			IType bplType = list.getType().getBoogieType();
			if (!(bplType instanceof BoogieType)) {
				throw new UnsupportedOperationException("The BoogiePreprocessorBacktranslator cannot handle "
						+ bplType.getClass().getSimpleName() + " as type of VarList");
			}
			BoogieType type = (BoogieType) bplType;
			return extractIdentifier(mappedDecl, list, inputExp, type);

		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, VarList list,
				IdentifierExpression inputExp, BoogieType type) {
			if (type instanceof StructType) {
				StructType st = (StructType) type;
				String[] inputNames = inputExp.getIdentifier().split("\\.");
				if (inputNames.length == 1) {
					// its the struct itself
					String inputName = inputExp.getIdentifier();
					for (String name : list.getIdentifiers()) {
						if (inputName.contains(name)) {
							return new IdentifierExpression(mappedDecl.getLocation(), type, name,
									inputExp.getDeclarationInformation());
						}
					}

				} else if (inputNames.length == 2) {
					// its a struct field access
					// first, find the name of the struct
					String structName = null;
					String inputStructName = inputNames[0];
					for (String name : list.getIdentifiers()) {
						if (inputStructName.contains(name)) {
							structName = name;
							break;
						}
					}
					if (structName != null) {
						// if this worked, lets get the field name
						for (String fieldName : st.getFieldIds()) {
							if (inputNames[1].contains(fieldName)) {
								return new IdentifierExpression(mappedDecl.getLocation(), type, structName + "!"
										+ fieldName, inputExp.getDeclarationInformation());
							}
						}
					}
				} else {
					// its a nested struct field access (this sucks)
					reportUnfinishedBacktranslation("Unfinished Backtranslation: Nested struct field access of VarList "
							+ BoogiePrettyPrinter.print(list) + " not handled");
				}
			} else if (type instanceof ConstructedType) {
				ConstructedType ct = (ConstructedType) type;
				return extractIdentifier(mappedDecl, list, inputExp, ct.getUnderlyingType());
			} else if (type instanceof PrimitiveType) {
				String inputName = inputExp.getIdentifier();
				for (String name : list.getIdentifiers()) {
					if (inputName.contains(name)) {
						return new IdentifierExpression(mappedDecl.getLocation(), list.getType().getBoogieType(), name,
								inputExp.getDeclarationInformation());
					}
				}
			} else {
				reportUnfinishedBacktranslation("Unfinished Backtranslation: Type" + type + " of VarList "
						+ BoogiePrettyPrinter.print(list) + " not handled");
			}
			return inputExp;
		}
	}

}
