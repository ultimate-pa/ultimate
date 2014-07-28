/**
 * CHandler variation for the SV-COMP 2014.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompArrayHandler;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ConvExpr;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

/**
 * @author Markus Lindenmann
 * @date 12.6.2012
 */
public class SvComp14CHandler extends CHandler {
	/**
	 * The string representing SV-Comp's error method.
	 */
	private static final String ERROR_STRING = "__VERIFIER_error";
	/**
	 * The string representing SV-Comp's havoc method.
	 */
	private static final String NONDET_STRING = "__VERIFIER_nondet_";
	/**
	 * Nondet_X | X in {int, float, char, short, long, pointer}
	 */
	private static final String[] NONDET_TYPE_STRINGS = { "int", "long", "float", "char", "short", "pointer" };
	/**
	 * The string representing SV-Comp's assert method.
	 */
	private static final String ASSUME_STRING = "__VERIFIER_assume";

	/**
	 * Constructor.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 */
	public SvComp14CHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, Logger logger) {
		super(main, backtranslator, false, logger);
		super.arrayHandler = new SVCompArrayHandler();
	}

	//
	// __VERIFIER_assume(EXPR) && skip VERIFIER_nondet_X()
	//

	@Override
	public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
		ILocation loc = new CACSLLocation(node);
		assert (node.getFunctionNameExpression() instanceof IASTIdExpression) : "we assumed that getFunctionNameExpression is IASTIdExpression, this might be wrong for function pointers";
		IASTIdExpression astIdExpression = (IASTIdExpression) node.getFunctionNameExpression();
		String methodName = astIdExpression.getName().toString();

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new HashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
		LRValue returnValue = null;

		if (methodName.equals(ERROR_STRING)) {
			Check check = new Check(Spec.ERROR_Function);
			AssertStatement assertStmt = new AssertStatement(loc, new BooleanLiteral(loc,
					new InferredType(Type.Boolean), false));
			check.addToNodeAnnot(assertStmt);
			// We do not add the assert(false) directly, but add an
			// nondeterministic if that contains this assert.
			// Adding the assert(false) directly would leads to an unsound
			// nontermination analysis.
			IfStatement ifStatement = new IfStatement(loc, new WildcardExpression(loc), new Statement[] { assertStmt },
					new Statement[0]);
			stmt.add(ifStatement);
			return new ResultExpression(stmt, returnValue, decl, auxVars, overappr);
		}
		if (methodName.equals(ASSUME_STRING)) {
			ArrayList<Expression> args = new ArrayList<Expression>();
			for (IASTInitializerClause inParam : node.getArguments()) {
				ResultExpression in = ((ResultExpression) main.dispatch(inParam)).switchToRValueIfNecessary(main,
						memoryHandler, structHandler, loc);
				if (in.lrVal.getValue() == null) {
					String msg = "Incorrect or invalid in-parameter! " + loc.toString();
					throw new IncorrectSyntaxException(loc, msg);
				}
				args.add(in.lrVal.getValue());
				stmt.addAll(in.stmt);
				decl.addAll(in.decl);
				auxVars.putAll(in.auxVars);
				overappr.addAll(in.overappr);
			}
			assert args.size() == 1; // according to SV-Comp specification!
			stmt.add(new AssumeStatement(loc, ConvExpr.toBoolean(loc,
					new RValue(args.get(0), new CPrimitive(PRIMITIVE.INT))).getValue()));
			assert (main.isAuxVarMapcomplete(decl, auxVars));
			return new ResultExpression(stmt, returnValue, decl, auxVars, overappr);
		}
		for (String t : NONDET_TYPE_STRINGS)
			if (methodName.equals(NONDET_STRING + t)) {
				// final InferredType type;
				final ASTType type;
				CType cType;
				if (t.equals("float")) {
					// type = new InferredType(Type.Real);
					type = new PrimitiveType(loc, SFO.REAL);
					cType = new CPrimitive(PRIMITIVE.FLOAT);
				} else if (t.equals("pointer")) {
					// type = new InferredType(Type.Pointer);
					NamedType boogiePointerType = new NamedType(null, new InferredType(Type.Struct), SFO.POINTER,
							new ASTType[0]);
					type = boogiePointerType;
					cType = new CPointer(new CPrimitive(PRIMITIVE.VOID));
				} else {
					// type = new InferredType(Type.Integer);
					type = new PrimitiveType(loc, SFO.INT);
					cType = new CPrimitive(PRIMITIVE.INT);
				}
				String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
				VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, type, loc);
				decl.add(tVarDecl);
				auxVars.put(tVarDecl, loc);
				// returnValue = new RValue(new IdentifierExpression(loc, type,
				// tmpName), cType);
				returnValue = new RValue(new IdentifierExpression(loc, tmpName), cType);
				assert (main.isAuxVarMapcomplete(decl, auxVars));
				return new ResultExpression(stmt, returnValue, decl, auxVars, overappr);
			}
		if (methodName.equals("printf")) {
			// skip if parent of parent is CompoundStatement
			// otherwise, replace by havoced variable
			if (node.getParent().getParent() instanceof IASTCompoundStatement) {
				return new ResultSkip();
			}
			InferredType type = new InferredType(Type.Integer);
			ASTType tempType = new PrimitiveType(loc, type, type.toString());
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, tempType) });
			auxVars.put(tVarDecl, loc);
			decl.add(tVarDecl);
			stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId) }));
			returnValue = new RValue(new IdentifierExpression(loc, type, tId, null), null);
			assert (main.isAuxVarMapcomplete(decl, auxVars));
			return new ResultExpression(stmt, returnValue, decl, auxVars, overappr);
		}
		return super.visit(main, node);
	}

	//
	// VERIFIER_nondet_X()
	//
	@Override
	public Result visit(Dispatcher main, IASTBinaryExpression node) {
		Result r = super.visit(main, node);
		if (node.getOperator() == IASTBinaryExpression.op_divide
				|| node.getOperator() == IASTBinaryExpression.op_divideAssign) {
			// remove division by zero asserts
			assert r instanceof ResultExpression;
			ResultExpression rex = (ResultExpression) r;
			Iterator<Statement> it = rex.stmt.iterator();
			while (it.hasNext())
				if (it.next() instanceof AssertStatement)
					it.remove();
		}
		return r;
	}

}