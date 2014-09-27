package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

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
	private BoogieSymbolTable mSymbolTable;

	protected BoogiePreprocessorBacktranslator(Logger logger) {
		super(BoogieASTNode.class, BoogieASTNode.class, Expression.class, Expression.class);
		mLogger = logger;
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

	@Override
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {

		List<Statement> newTrace = new ArrayList<>();
		Map<Integer, ProgramState<Expression>> newPartialProgramStateMapping = new HashMap<>();

		int length = programExecution.getLength();
		for (int i = 0; i < length; ++i) {
			BoogieASTNode elem = programExecution.getTraceElement(i);
			BoogieASTNode newElem = mMapping.get(elem);

			if (newElem == null) {
				mLogger.warn("Unfinished backtranslation: No mapping for " + elem.toString());
			} else {
				if (newElem instanceof Statement) {
					newTrace.add((Statement) newElem);
				} else {
					mLogger.warn("Unfinished backtranslation: Ignored translation of "
							+ newElem.getClass().getSimpleName());
				}
			}

			ProgramState<Expression> initialState = programExecution.getInitialProgramState();
			if (initialState != null) {
				// was macht man damit?
				mLogger.warn("Unfinished backtranslation: Ignored initial programstate " + initialState);
			}

			ProgramState<Expression> state = programExecution.getProgramState(i);
			if (state == null) {
				newPartialProgramStateMapping.put(i, null);
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
				newPartialProgramStateMapping.put(i, new ProgramState<>(newVariable2Values));
			}
		}
		//TODO: During development, I switch these comments to have a "clean" boogie translation 
		 return super.translateProgramExecution(programExecution);
//		return new BoogieProgramExecution(newTrace, newPartialProgramStateMapping);
	}

	@Override
	public List<BoogieASTNode> translateTrace(List<BoogieASTNode> trace) {
		// TODO Auto-generated method stub
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

	private class ExpressionTranslator extends BoogieTransformer {

		@Override
		protected Expression processExpression(Expression expr) {
			if (mSymbolTable == null) {
				mLogger.warn("No symboltable available, using identity as back-translation of " + expr);
				return expr;
			}

			if (expr instanceof IdentifierExpression) {
				IdentifierExpression ident = (IdentifierExpression) expr;
				if (((IdentifierExpression) expr).getDeclarationInformation() == null) {
					mLogger.warn("Identifier has no declaration information, using identity as back-translation of "
							+ expr);
					return expr;
				}
				Declaration decl = mSymbolTable.getDeclaration(ident);

				if (decl == null) {
					mLogger.warn("No declaration in symboltable, using identity as back-translation of " + expr);
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
			if (mappedDecl instanceof VariableDeclaration) {
				VariableDeclaration mappedVarDecl = (VariableDeclaration) mappedDecl;
				String inputName = inputExp.getIdentifier();
				for (VarList lil : mappedVarDecl.getVariables()) {
					for (String name : lil.getIdentifiers()) {
						if (inputName.contains(name)) {
							// TODO: The declaration info of this expression is
							// not backtranslated -- procedure names may need to
							// be translated
							return new IdentifierExpression(mappedDecl.getLocation(), lil.getType().getBoogieType(),
									name, inputExp.getDeclarationInformation());

						}
					}
				}
				mLogger.warn("Unfinished backtranslation: Name guessing unsuccessful for VarDecl "
						+ BoogiePrettyPrinter.print(mappedVarDecl) + " and expression "
						+ BoogiePrettyPrinter.print(inputExp));

			} else {
				mLogger.warn("Unfinished backtranslation: Declaration " + mappedDecl.getClass().getSimpleName()
						+ " not handled for expression " + BoogiePrettyPrinter.print(inputExp));
			}
			return inputExp;
		}
	}

}
