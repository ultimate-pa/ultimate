package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultVarList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * Class that handles translation of functions.
 * 
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class FunctionHandler {
	/**
	 * A map from procedure name to procedure declaration.
	 */
	private HashMap<String, Procedure> procedures;
	/**
	 * The currently handled procedure.
	 */
	private Procedure currentProcedure;
	/**
	 * Whether the modified globals is user defined or not. If it is in this
	 * set, then it is a modifies clause defined by the user.
	 */
	private HashSet<String> modifiedGlobalsIsUserDefined;
	/**
	 * A map from method name to all called methods of the specified one.
	 */
	private HashMap<String, HashSet<String>> callGraph;
	/**
	 * Whether the current procedure is declared to return void.
	 */
	private boolean currentProcedureIsVoid;
	/**
	 * Modified global variables of the current function.
	 */
	private HashMap<String, HashSet<String>> modifiedGlobals;
	/**
	 * Methods that have been called before they were declared. These methods
	 * need a special treatment, as they are assumed to be returning int!
	 */
	private HashSet<String> methodsCalledBeforeDeclared;
	
	private HashMap<String, CType> procedureToReturnCType;
	
	private final static boolean m_CheckMemoryLeakAtEndOfMain = false;

	/**
	 * Constructor.
	 */
	public FunctionHandler() {
		this.callGraph = new HashMap<String, HashSet<String>>();
		this.currentProcedureIsVoid = false;
		this.modifiedGlobals = new HashMap<String, HashSet<String>>();
		this.methodsCalledBeforeDeclared = new HashSet<String>();
		this.procedures = new HashMap<String, Procedure>();
		this.procedureToReturnCType = new HashMap<String, CType>();
		this.modifiedGlobalsIsUserDefined = new HashSet<String>();
	}

	/**
	 * Adds searchString to modifiedGlobals iff searchString is a global
	 * variable and the user has not defined a modifies clause.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * 
	 * @param searchString
	 *            = boogieVarName!
	 * @param errLoc
	 *            the location for possible errors!
	 */
	public void checkIfModifiedGlobal(Dispatcher main, String searchString,
			ILocation errLoc) {
		String cName;
		if (!main.cHandler.getSymbolTable().containsBoogieSymbol(searchString)) {
			return; // temp variable!
		}
		cName = main.cHandler.getSymbolTable().getCID4BoogieID(searchString,
				errLoc);
		String cId = currentProcedure.getIdentifier();
		CType cvar = main.cHandler.getSymbolTable().get(cName, errLoc)
				.getCVariable();
		if (cvar != null && cvar.isStatic()) {
			modifiedGlobals.get(cId).add(searchString);
			return;
		}
		if (modifiedGlobalsIsUserDefined.contains(cId))
			return;
		boolean isLocal = false;
		if (searchString.equals(SFO.RES)) {
			// this variable is reserved for the return variable and
			// therefore local!
			isLocal = true;
		} else {
			isLocal = !main.cHandler.getSymbolTable().get(cName, errLoc)
					.isGlobalVar();
		}
		if (!isLocal) {
			// the variable is not local but could be a formal parameter
			if (!searchString.startsWith(SFO.IN_PARAM)) { // variable is global!
				modifiedGlobals.get(cId).add(searchString);
			} else {
				assert false;
			}
		}
	}

	/**
	 * Extracted method to handle IASTSimpleDeclaration holding a
	 * FunctionDeclarator.
	 * 
	 * @param main
	 *            the main dispatcher reference.
	 * @param contract
	 *            the function contract - can be null.
	 * @param node
	 *            the node to translate. the simple declaration holding the
	 *            function.
	 * @return the handled Result.
	 */
	public Result handleFunctionDeclaration(Dispatcher main,
			List<ACSLNode> contract, IASTSimpleDeclaration node) {
		return handleFunctionDeclaration(main, contract, node, 0);
	}
	
	/**
	 * Has additional index.
	 * 
	 * @see handleFunctionDeclaration()
	 * @param index index of the declaration list
	 */
	public Result handleFunctionDeclaration(Dispatcher main,
			List<ACSLNode> contract, IASTSimpleDeclaration node,
			int index) {
		CACSLLocation loc = new CACSLLocation(node);
		assert (index >= 0 && index < node.getDeclarators().length);
        IASTDeclarator cDecl = node.getDeclarators()[index];
		assert cDecl instanceof IASTFunctionDeclarator;
		String methodName = cDecl.getName().getRawSignature();
		// begin new scope for retranslation of ACSL specification
		main.cHandler.getSymbolTable().beginScope();
		ResultVarList res = ((ResultVarList) main.dispatch(cDecl));
		VarList[] in = res.varList;
		if (in == null) {
			in = new VarList[0];
		}
		Attribute[] attr = new Attribute[0];
		String[] typeParams = new String[0];
		Specification[] spec;
		if (contract == null) {
			spec = new Specification[0];
		} else {
			List<Specification> specList = new ArrayList<Specification>();
			for (int i = 0; i<contract.size(); i++) {
					// retranslate ACSL specification needed e.g., in cases
					// where ids of function parameters differ from is in ACSL
					// expression
//					ACSLNode acslNode = ((CACSLLocation) spec[i].getLocation()
//							.getOrigin()).getAcslNode();
					Result retranslateRes = main.dispatch(contract.get(i));
					assert (retranslateRes instanceof ResultContract);
					ResultContract resContr = (ResultContract) retranslateRes;
					specList.addAll(Arrays.asList(resContr.specs));
			}
			spec = specList.toArray(new Specification[0]);
			for (int i = 0; i<spec.length; i++) {
				if (spec[i] instanceof ModifiesSpecification) {
					modifiedGlobalsIsUserDefined.add(methodName);
					ModifiesSpecification ms = (ModifiesSpecification) spec[i];
					HashSet<String> modifiedSet = new HashSet<String>();
					for (VariableLHS var : ms.getIdentifiers()) 
						modifiedSet.add(var.getIdentifier());
					modifiedGlobals.put(methodName, modifiedSet);
				}
			}

			main.cHandler.clearContract(); // take care for behavior and
												// completeness
		}
		// OUT VARLIST : only one out param in C
		VarList[] out = new VarList[1];
		// we check the type via typeHandler
		ResultTypes returnType = (ResultTypes) main.dispatch(node
				.getDeclSpecifier());
		if (returnType.isVoid) {
			if (methodsCalledBeforeDeclared.contains(methodName)) {
				// this method was assumed to return int -> return int
				out[0] = new VarList(loc, new String[] { SFO.RES },
						new PrimitiveType(loc, new InferredType(Type.Integer),
								SFO.INT));
			} else {
				// void, so there are no out vars
				out = new VarList[0];
			}
		} else {
			// we found a type, so node is type ASTType
			ResultTypes checkedType = main.cHandler.checkForPointer(main,
					node.getDeclarators()[0].getPointerOperators(), returnType, false);
			ASTType type = checkedType.getType();
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		}
		if (!modifiedGlobals.containsKey(methodName)) {
			modifiedGlobals.put(methodName, new HashSet<String>());
		}
		if (!callGraph.containsKey(methodName)) {
			callGraph.put(methodName, new HashSet<String>());
		}
		Procedure proc = new Procedure(loc, attr, methodName, typeParams, in,
				out, spec, null);
		procedures.put(methodName, proc);
		procedureToReturnCType.put(methodName, returnType.cvar);
		// end scope for retranslation of ACSL specification
		main.cHandler.getSymbolTable().endScope();
		return new ResultSkip();
	}

	// private Specification[] retranslateACSL(ACSLNode acslNode,
	// VarList[] inParams, Dispatcher main) {
	// main.cHandler.getSymbolTable().beginScope();
	// for (VarList varList : inParams) {
	// for (String id : varList.getIdentifiers()) {
	// new SymbolTableValue(id, null, false, null);
	//
	// main.cHandler.getSymbolTable().put(cId, value);
	// }
	// }
	//
	//
	// }

	/**
	 * Creates local variables for in parameters.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * 
	 * @param loc
	 *            the location
	 * @param decl
	 *            the declaration list to append to.
	 * @param stmt
	 *            the statement list to append to.
	 * @param parent
	 */
	public void handleFunctionsInParams(Dispatcher main, ILocation loc,
			ArrayList<Declaration> decl, ArrayList<Statement> stmt,
			IASTNode parent) {
		for (VarList varList : currentProcedure.getInParams()) {
			for (final String bId : varList.getIdentifiers()) {
				final String cId = main.cHandler.getSymbolTable()
						.getCID4BoogieID(bId, loc);
				// Copy of inparam that is writeable
				String auxInvar = main.nameHandler.getUniqueIdentifier(parent,
						cId, 0, false);
				VarList var = new VarList(loc, new String[] { auxInvar },
						varList.getType());
				VariableDeclaration inVarDecl = new VariableDeclaration(loc,
						new Attribute[0], new VarList[] { var });
				decl.add(inVarDecl);
				VariableLHS tempLHS = new VariableLHS(loc,
						var.getIdentifiers()[0]);
				stmt.add(new AssignmentStatement(loc,
						new LeftHandSide[] { tempLHS },
						new Expression[] { new IdentifierExpression(loc, bId) }));

				assert main.cHandler.getSymbolTable().containsCSymbol(cId);
				CType cvar = main.cHandler.getSymbolTable().get(cId, loc)
						.getCVariable();
				// Overwrite the information in the symbolTable for cId, s.t. it
				// points to the locally declared variable.
				main.cHandler.getSymbolTable().put(cId,
						new SymbolTableValue(auxInvar, inVarDecl, false, cvar));
			}
		}
	}

	/**
	 * Checkes, whether all procedures that are beeing called in C, were
	 * eventually declared within the C program.
	 * 
	 * @return true iff all called procedures were declared.
	 */
	public boolean isEveryCalledProcedureDeclared() {
		for (String s : methodsCalledBeforeDeclared) {
			if (!procedures.containsKey(s)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Calculates transitive modifies clauses for all procedure declarations
	 * linear in time to (|procedures| + |procedure calls|).
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @return procedure declarations
	 */
	public ArrayList<Declaration> calculateTransitiveModifiesClause(
			Dispatcher main) {
		assert isEveryCalledProcedureDeclared();
		// calculate SCCs and a mapping for each methodId to its SCC
		// O(|edges| + |calls|)
		HashSet<HashSet<String>> sccs = new TarjanSCC().getSCCs(callGraph);
		HashMap<String, HashSet<String>> mapping = new HashMap<String, HashSet<String>>();
		for (HashSet<String> scc : sccs) { // O(|proc|)
			for (String s : scc) {
				mapping.put(s, scc);
			}
		}
		HashMap<HashSet<String>, Integer> incomingEdges = new HashMap<HashSet<String>, Integer>();
		for (HashSet<String> scc : sccs) {
			incomingEdges.put(scc, 0);
		}
		// calculate the SCC update graph without loops and dead ends
		Queue<HashSet<String>> deadEnds = new LinkedList<HashSet<String>>();
		deadEnds.addAll(sccs);
		HashMap<HashSet<String>, HashSet<HashSet<String>>> updateGraph = new HashMap<HashSet<String>, HashSet<HashSet<String>>>();
		for (String p : callGraph.keySet()) { // O(|calls|)
			for (String s : callGraph.get(p)) { // foreach s : succ(p)
				// edge (p, s), means p calls s
				HashSet<String> sccP = mapping.get(p);
				HashSet<String> sccS = mapping.get(s);
				if (sccP == sccS)
					continue; // skip self loops
				if (updateGraph.containsKey(sccS)) {
					updateGraph.get(sccS).add(sccP);
				} else {
					HashSet<HashSet<String>> predSCCs = new HashSet<HashSet<String>>();
					predSCCs.add(sccP);
					updateGraph.put(sccS, predSCCs);
				}
				incomingEdges.put(sccP, incomingEdges.get(sccP) + 1);
				deadEnds.remove(sccP);
			}
		}
		// This graph might not be complete! It is i.e. missing all procedures,
		// that do not have incoming or outgoing edges!
		// But: They don't need an update anyway!

		// calculate transitive modifies clause
		HashMap<HashSet<String>, HashSet<String>> modGlobals = new HashMap<HashSet<String>, HashSet<String>>();
		while (!deadEnds.isEmpty()) {
			// O (|proc| + |edges in updateGraph|), where
			// |edges in updateGraph| <= |calls|
			HashSet<String> d = deadEnds.poll();
			for (String p : d) {
				if (!modGlobals.containsKey(d)) {
					HashSet<String> n = new HashSet<String>();
					n.addAll(modifiedGlobals.get(p));
					modGlobals.put(d, n);
				} else {
					modGlobals.get(d).addAll(modifiedGlobals.get(p));
				}
			}
			if (updateGraph.get(d) == null)
				continue;
			for (HashSet<String> next : updateGraph.get(d)) {
				if (!modGlobals.containsKey(next)) {
					HashSet<String> n = new HashSet<String>();
					n.addAll(modGlobals.get(d));
					modGlobals.put(next, n);
				} else {
					modGlobals.get(next).addAll(modGlobals.get(d));
				}
				int remainingUpdates = incomingEdges.get(next) - 1;
				if (remainingUpdates == 0) {
					deadEnds.add(next);
				}
				incomingEdges.put(next, remainingUpdates);
			}
		}
		// update the modifies clauses!
		ArrayList<Declaration> declarations = new ArrayList<Declaration>();
		for (Procedure procDecl : procedures.values()) { // O(|proc|)
			String mId = procDecl.getIdentifier();
			Specification[] spec = procDecl.getSpecification();
			CACSLLocation loc = (CACSLLocation) procDecl.getLocation();
			if (!modifiedGlobalsIsUserDefined.contains(mId)) {
				assert mapping.get(mId) != null;
				HashSet<String> currModClause = modGlobals
						.get(mapping.get(mId));
				assert currModClause != null : "No modifies clause proc " + mId;
				modifiedGlobals.put(mId, currModClause);
				int nrSpec = spec.length;
				spec = Arrays.copyOf(spec, nrSpec + 1);
				VariableLHS[] modifyList = new VariableLHS[currModClause.size()];
				int i = 0;
				for (String var: currModClause) {
					modifyList[i++] = new VariableLHS(loc, var);
				}
				spec[nrSpec] = new ModifiesSpecification(loc, false, modifyList);
			}
			if (main.isMMRequired()
					&& (main.getCheckedMethod() == SFO.EMPTY || main
							.getCheckedMethod().equals(mId))) {
				if(m_CheckMemoryLeakAtEndOfMain) {
					// add a specification to check for memory leaks
					Expression vIe = new IdentifierExpression(loc, SFO.VALID);
					int nrSpec = spec.length;
					Check check = new Check(Check.Spec.MEMORY_LEAK);
					ILocation ensLoc = new CACSLLocation(loc, check);
					spec = Arrays.copyOf(spec, nrSpec + 1);
					spec[nrSpec] = new EnsuresSpecification(ensLoc, false,
							new BinaryExpression(loc, Operator.COMPEQ, vIe,
									new UnaryExpression(loc,
											UnaryExpression.Operator.OLD, vIe)));
					check.addToNodeAnnot(spec[nrSpec]);
				}
			}
			declarations.add(new Procedure(loc, procDecl.getAttributes(), mId,
					procDecl.getTypeParams(), procDecl.getInParams(), procDecl
							.getOutParams(), spec, null));
		}
		return declarations;
	}

	/**
	 * Handles translation of IASTFunctionDefinition.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleFunctionDefinition(Dispatcher main,
			IASTFunctionDefinition node) {
		main.cHandler.getSymbolTable().beginScope();
		ILocation loc = new CACSLLocation(node);
		String methodName = node.getDeclarator().getName().toString();
		VarList[] in = ((ResultVarList) main.dispatch(node.getDeclarator())).varList;
		VarList[] out = new VarList[0]; // at most one out param in C
		// we check the type via typeHandler
		ResultTypes resType = (ResultTypes) main.dispatch(node
				.getDeclSpecifier());
		procedureToReturnCType.put(methodName, resType.cvar);
		ResultTypes checkedType = main.cHandler.checkForPointer(main, node
				.getDeclarator().getPointerOperators(), resType, false);
		ASTType type = checkedType.getType();
		if (!checkedType.isVoid) { // void, so there are no out vars
			out = new VarList[1];
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		} else if (methodsCalledBeforeDeclared.contains(methodName)) {
			out = new VarList[1];
			out[0] = new VarList(loc, new String[] { SFO.RES },
					new PrimitiveType(loc, new InferredType(Type.Integer),
							SFO.INT));
		}
		Procedure decl = procedures.get(methodName);
		if (decl == null) {
			Attribute[] attr = new Attribute[0];
			String[] typeParams = new String[0];
			Specification[] spec = new Specification[0];
			if (isInParamVoid(in)) {
				in = new VarList[0]; // in parameter is "void"
			}
			decl = new Procedure(loc, attr, methodName, typeParams, in, out,
					spec, null);
			if (procedures.containsKey(methodName)) {
				String msg = "Duplicated method identifier: " + methodName
						+ ". C does not support function overloading!";
				Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
				throw new IncorrectSyntaxException(msg);
			}
			procedures.put(methodName, decl);
		} else { // check declaration against its implementation
			VarList[] declIn = decl.getInParams();
			boolean checkInParams = true;
			if (in.length != decl.getInParams().length
					|| out.length != decl.getOutParams().length
					|| isInParamVoid(decl.getInParams())) {
				if (decl.getInParams().length == 0) {
					// the implementation can have 0 to n in parameters!
					// do not check, but use the in params of the implementation
					// as we will take the ones of the implementation anyway
					checkInParams = false;
					declIn = in;
				} else if (isInParamVoid(decl.getInParams())
						&& (in.length == 0 || isInParamVoid(in))) {
					// decl(void) && [impl() || impl(void)]
					declIn = new VarList[0];
					in = new VarList[0];
					checkInParams = false;
				} else {
					String msg = "Implementation does not match declaration!";
					Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
					throw new IncorrectSyntaxException(msg);
				}
			}
			if (checkInParams) {
				for (int i = 0; i < in.length; i++) {
					if (!(in[i].getType().toString()
							.equals(decl.getInParams()[i].getType().toString()))) {
						String msg = "Implementation does not match declaration!"
								+ "Type missmatch on in-parameters!";
						Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax,
								msg);
						throw new IncorrectSyntaxException(msg);
					}
				}
			}
			decl = new Procedure(decl.getLocation(), decl.getAttributes(),
					decl.getIdentifier(), decl.getTypeParams(), declIn,
					decl.getOutParams(), decl.getSpecification(), null);
			procedures.put(methodName, decl);
		}
		Procedure declWithCorrectlyNamedInParams = new Procedure(
				decl.getLocation(), decl.getAttributes(), decl.getIdentifier(),
				decl.getTypeParams(), in, decl.getOutParams(),
				decl.getSpecification(), null);
		currentProcedure = declWithCorrectlyNamedInParams;
		currentProcedureIsVoid = resType.isVoid;
		if (!modifiedGlobals.containsKey(currentProcedure.getIdentifier())) {
			modifiedGlobals.put(currentProcedure.getIdentifier(),
					new HashSet<String>());
		}
		if (!callGraph.containsKey(currentProcedure.getIdentifier())) {
			callGraph.put(currentProcedure.getIdentifier(),
					new HashSet<String>());
		}
		Body body = ((Body) main.dispatch(node.getBody()).node);
		decl = currentProcedure;
		// Implementation -> Specification always null!
		Procedure impl = new Procedure(loc, decl.getAttributes(), methodName,
				decl.getTypeParams(), in, decl.getOutParams(), null, body);
		currentProcedure = null;
		currentProcedureIsVoid = false;
		main.cHandler.getSymbolTable().endScope();
		return new Result(impl);
	}

	/**
	 * Handles translation of IASTFunctionCallExpression.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param memoryHandler
	 *            a reference to the memory Handler.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleFunctionCallExpression(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler, 
			IASTFunctionCallExpression node) {
	    // TODO Christian: no node to add, right?
	    Check check = new Check(Check.Spec.PRE_CONDITION);
		CACSLLocation loc = new CACSLLocation(node, check);
		IASTExpression functionName = node.getFunctionNameExpression(); 
		if (!(functionName instanceof IASTIdExpression)) {
			String msg = "Function pointer or similar is not supported. "
					+ loc.toString();
			Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
			throw new IncorrectSyntaxException(msg);
		}
		//don't use getRawSignature because it refers to the code before preprocessing 
		// f.i. we get a wrong methodname here in defineFunction.c, because of a #define in the original code
		String methodName = ((IASTIdExpression) functionName).getName().toString();
		
		if (methodName.equals("malloc")) {
			assert node.getArguments().length == 1;
			Result sizeRes = main.dispatch(node.getArguments()[0]);
			assert sizeRes instanceof ResultExpression;
			ResultExpression sizeRex = ((ResultExpression) sizeRes)
					.switchToRValue(main, memoryHandler, structHandler, loc);
//			return memoryHandler.getMallocCall(main, this, sizeRex.expr, loc);
			return memoryHandler.getMallocCall(main, this, sizeRex.lrVal.getValue(), loc);
		}
		if (methodName.equals("free")) {
			assert node.getArguments().length == 1;
			Result pRes = main.dispatch(node.getArguments()[0]);
			assert pRes instanceof ResultExpression;
			ResultExpression pRex = ((ResultExpression) pRes)
					.switchToRValue(main, memoryHandler, structHandler, loc);
//			return memoryHandler.getFreeCall(main, this, pRex.expr, loc);
			return memoryHandler.getFreeCall(main, this, pRex.lrVal.getValue(), loc);
		}

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, CACSLLocation> auxVars = 
				new HashMap<VariableDeclaration, CACSLLocation>();
		Expression expr = null;

		callGraph.get(currentProcedure.getIdentifier()).add(methodName);

		ArrayList<Expression> args = new ArrayList<Expression>();
		if (procedures.containsKey(methodName)
				&& node.getArguments().length != procedures.get(methodName)
						.getInParams().length) {
			if (!(procedures.get(methodName).getInParams().length == 1
					&& procedures.get(methodName).getInParams()[0].getType() == null && node
						.getArguments().length == 0)) {
				String msg = "Function call has incorrect number of in-params!";
				Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
				throw new IncorrectSyntaxException(msg);
			} // else: this means param of declaration is void and parameter
				// list of call is empty! --> OK
		}
		for (int i = 0; i < node.getArguments().length; i++) {
			IASTInitializerClause inParam = node.getArguments()[i];
			ResultExpression in = ((ResultExpression) main.dispatch(inParam))
					.switchToRValue(main, memoryHandler, structHandler, loc);
			if (in.lrVal.getValue() == null) {
				String msg = "Incorrect or invalid in-parameter! "
						+ loc.toString();
				Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
				throw new IncorrectSyntaxException(msg);
			}
			Expression arg = in.lrVal.getValue();
			if (procedures.containsKey(methodName)
					&& procedures.get(methodName).getInParams() != null
					&& i < procedures.get(methodName).getInParams().length) {
				arg = main.typeHandler.convertArith2Boolean(loc,
						procedures.get(methodName).getInParams()[i].getType(),
						in.lrVal.getValue());
			} 
//			else {
//				throw new UnsupportedSyntaxException("procedure not found in procedure list, " +
//						"maybe not declared at call position?");
//			}
			args.add(arg);
			stmt.addAll(in.stmt);
			decl.addAll(in.decl);
			auxVars.putAll(in.auxVars);
		}

		Statement call;
		if (procedures.containsKey(methodName)) {
			VarList[] type = procedures.get(methodName).getOutParams();
			if (type.length == 0) { // void
				// C has only one return statement -> no need for forall
				call = new CallStatement(loc, false, new VariableLHS[0], methodName,
						args.toArray(new Expression[0]));
			} else if (type.length == 1) { // one return value
				String tmpId = main.nameHandler
						.getTempVarUID(SFO.AUXVAR.RETURNED);
				InferredType tmpIType = new InferredType(type[0].getType());
				expr = new IdentifierExpression(loc, tmpIType, tmpId);
				VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpId, tmpIType, loc); 
				auxVars.put(tmpVar, loc);
				decl.add(tmpVar);
				VariableLHS tmpLhs = new VariableLHS(loc, tmpId);
				call = new CallStatement(loc, false, new VariableLHS[] { tmpLhs },
						methodName, args.toArray(new Expression[0]));
			} else { // unsupported!
				String msg = "Cannot handle multiple out params! "
						+ loc.toString();
				Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
				throw new IncorrectSyntaxException(msg);
			}
		} else {
			methodsCalledBeforeDeclared.add(methodName);
			String longDescription = "Return value of method '"
					+ methodName
					+ "' unknown! Methods should be declared, before they are used! Return value assumed to be int ...";
			Dispatcher.warn(loc, "Unsoundness Warning", longDescription);
			String ident = main.nameHandler.getTempVarUID(SFO.AUXVAR.RETURNED);
			expr = new IdentifierExpression(loc,
					new InferredType(Type.Integer), ident);
			VarList tempVar = new VarList(loc, new String[] { ident },
					new PrimitiveType(loc, SFO.INT));
			VariableDeclaration tmpVar = new VariableDeclaration(loc,
					new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, ident);
			call = new CallStatement(loc, false, new VariableLHS[] { lhs },
					methodName, args.toArray(new Expression[0]));
		}
		stmt.add(call);
		CType returnCType = methodsCalledBeforeDeclared.contains(methodName) ? 
				new CPrimitive(PRIMITIVE.INT) : 
					procedureToReturnCType.get(methodName);
		assert (main.isAuxVarMapcomplete(decl, auxVars));
		return new ResultExpression(stmt, new RValue(expr, returnCType), decl, auxVars);
	}

	/**
	 * Handles translation of return statements.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleReturnStatement(Dispatcher main, MemoryHandler memoryHandler,
			StructHandler structHandler, IASTReturnStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
		// The ReturnValue could be empty!
		CACSLLocation loc = new CACSLLocation(node);
		VarList[] outParams = this.currentProcedure.getOutParams();
		if (methodsCalledBeforeDeclared.contains(currentProcedure
				.getIdentifier()) && currentProcedureIsVoid) {
			// void method that was assumed to be returning int! -> return int
			String id = outParams[0].getIdentifiers()[0];
			VariableLHS lhs = new VariableLHS(loc, id);
			Statement havoc = new HavocStatement(loc, new VariableLHS[] { lhs });
			stmt.add(havoc);
		} else if (node.getReturnValue() != null) {
			ResultExpression exprResult = ((ResultExpression) main.dispatch(node
					.getReturnValue())).switchToRValue(main, memoryHandler, structHandler, loc);
			Expression rhs = (Expression) exprResult.lrVal.getValue();
			stmt.addAll(exprResult.stmt);
			decl.addAll(exprResult.decl);
			auxVars.putAll(exprResult.auxVars);
			if (outParams.length == 0) {
				// void method which is returning something! We remove the
				// return value!
				String msg = "This method is declared to be void, but returning a value!";
				Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
			} else if (outParams.length != 1) {
				String msg = "We do not support several output parameters for functions";
				Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
				throw new UnsupportedSyntaxException(msg);
			} else {
				String id = outParams[0].getIdentifiers()[0];
				VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(loc, id) };
				rhs = main.typeHandler.convertArith2Boolean(loc,
						outParams[0].getType(), rhs);
				stmt.add(new AssignmentStatement(loc, lhs,
						new Expression[] { rhs }));
			}
		}
		stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
		stmt.add(new ReturnStatement(loc));
		Map<VariableDeclaration, CACSLLocation> emptyAuxVars = new HashMap<VariableDeclaration, CACSLLocation>(
				0);
		return new ResultExpression(stmt, null, decl, emptyAuxVars);
	}

	/**
	 * Checks a VarList for a specific pattern, that represents "void".
	 * 
	 * @param in
	 *            the methods in-parameter list.
	 * @return true iff in represents void.
	 */
	private static final boolean isInParamVoid(VarList[] in) {
		if (in.length > 0 && in[0] == null)
			throw new IllegalArgumentException("In-param cannot be null!");
		return ((in.length == 1 && in[0].getType() == null));
	}

	/**
	 * Handles the translation of IASTFunctionDeclarator.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node to translate.
	 * @return the translation result.
	 */
	public Result handleFunctionDeclarator(Dispatcher main,
			IASTFunctionDeclarator node) {
		ILocation loc = new CACSLLocation(node);
		ArrayList<VarList> list = new ArrayList<VarList>();
		for (IASTParameterDeclaration dec : ((CASTFunctionDeclarator) node)
				.getParameters()) {
			ResultTypes rt = (ResultTypes) main
					.dispatch(dec.getDeclSpecifier());
			IASTDeclarator d = dec.getDeclarator();
			ResultTypes checkedType = main.cHandler.checkForPointer(main,
					d.getPointerOperators(), rt, false);
			CType cvar = checkedType.cvar;
			ASTType type = checkedType.getType();
			if (!(checkedType.isVoid && !(cvar instanceof CPointer))) {
//				String cId = dec.getDeclarator().getName().getRawSignature();
				String cId = dec.getDeclarator().getName().toString();
				if (cId.equals(SFO.EMPTY)) {
					cId = SFO.UNNAMED
							+ dec.getDeclarator().getName().hashCode();
				}
				String boogieId = main.nameHandler.getInParamIdentifier(cId);
				if (cvar instanceof CPointer && checkedType.isVoid) {
					// FIXME : Well the type seems to be void * in C ... we will
					// represent this with a int in Boogie.
					// should be changed to a real "void pointer" in the MM!
					rt.node = new PrimitiveType(loc, SFO.INT);
				}
				VarList vl = new VarList(loc, new String[] { boogieId }, type);
				VariableDeclaration decl = new VariableDeclaration(loc,
						new Attribute[0], new VarList[] { vl });
				main.cHandler.getSymbolTable().put(cId,
						new SymbolTableValue(boogieId, decl, false, cvar));
				list.add(vl);
			}
		}
		return new ResultVarList(list.toArray(new VarList[0]));
	}

	/**
	 * Getter for modified globals.
	 * 
	 * @return modified globals.
	 */
	public HashMap<String, HashSet<String>> getModifiedGlobals() {
		return this.modifiedGlobals;
	}

	/**
	 * Getter for procedures.
	 * 
	 * @return procedures.
	 */
	public HashMap<String, Procedure> getProcedures() {
		return this.procedures;
	}

	/**
	 * Returns the identifier of the current procedure.
	 * 
	 * @return the identifier of the current procedure.
	 */
	public String getCurrentProcedureID() {
		return this.currentProcedure.getIdentifier();
	}

	public boolean noCurrentProcedure() {
		return this.currentProcedure == null;
	}
	
	/**
	 * Getter for the call graph.
	 * 
	 * @return the call graph.
	 */
	public HashMap<String, HashSet<String>> getCallGraph() {
		return this.callGraph;
	}
}
