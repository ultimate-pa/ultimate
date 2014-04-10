package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue.StorageClass;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultVarList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
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
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.util.LinkedScopedHashMap;

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
	private LinkedHashMap<String, Procedure> procedures;
	/**
	 * The currently handled procedure.
	 */
	private Procedure currentProcedure;
	/**
	 * Whether the modified globals is user defined or not. If it is in this
	 * set, then it is a modifies clause defined by the user.
	 */
	private LinkedHashSet<String> modifiedGlobalsIsUserDefined;
	/**
	 * A map from method name to all called methods of the specified one.
	 */
	private LinkedHashMap<String, LinkedHashSet<String>> callGraph;
	/**
	 * Whether the current procedure is declared to return void.
	 */
	private boolean currentProcedureIsVoid;
	/**
	 * Modified global variables of the current function.
	 */
	private LinkedHashMap<String, LinkedHashSet<String>> modifiedGlobals;
	/**
	 * Methods that have been called before they were declared. These methods
	 * need a special treatment, as they are assumed to be returning int!
	 */
	private LinkedHashSet<String> methodsCalledBeforeDeclared;
	
	/**
	 * This set contains those pointers that we have to malloc at the beginning
	 * and free at the end of the current procedure;
	 */
	LinkedScopedHashMap<LocalLValue, Integer> mallocedAuxPointers;
	/**
	 * map that is used to communicate the returned CType of a procedure from 
	 * its declaration to its definition.
	 */
	private LinkedHashMap<String, CType> procedureToReturnCType;
	private LinkedHashMap<String, ArrayList<CType>> procedureToParamCType;
	
	private final boolean m_CheckMemoryLeakAtEndOfMain;

	/**
	 * Constructor.
	 */
	public FunctionHandler() {
		this.callGraph = new LinkedHashMap<String, LinkedHashSet<String>>();
		this.currentProcedureIsVoid = false;
		this.modifiedGlobals = new LinkedHashMap<String, LinkedHashSet<String>>();
		this.methodsCalledBeforeDeclared = new LinkedHashSet<String>();
		this.procedures = new LinkedHashMap<String, Procedure>();
		this.procedureToReturnCType = new LinkedHashMap<String, CType>();
		this.procedureToParamCType = new LinkedHashMap<String, ArrayList<CType>>(); 
		this.modifiedGlobalsIsUserDefined = new LinkedHashSet<String>();
		this.mallocedAuxPointers = new LinkedScopedHashMap<LocalLValue, Integer>();
		m_CheckMemoryLeakAtEndOfMain = 
				(new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).
				getBoolean(PreferenceInitializer.LABEL_CHECK_MemoryLeakInMain);
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
		SymbolTableValue stValue = main.cHandler.getSymbolTable().get(cName, errLoc);
		CType cvar = stValue.getCVariable();
		if (cvar != null && stValue.isStatic()) {
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
	 * Has additional index.
	 * @param cDec 
	 * 
	 * @see handleFunctionDeclaration()
	 * @param index index of the declaration list
	 */
	public Result handleFunctionDeclarator(Dispatcher main,
			List<ACSLNode> contract, IASTFunctionDeclarator cFuncDeclarator, CDeclaration cDec, ResultTypes returnType) {
		CACSLLocation loc = new CACSLLocation(cFuncDeclarator);
		String methodName = cFuncDeclarator.getName().toString();
//		CFunction funcType = (CFunction) cDec.getType();
		// begin new scope for retranslation of ACSL specification
		main.cHandler.beginScope();
		
		VarList[] in = processInParams(main, loc, cDec, methodName);
		
		// OUT VARLIST : only one out param in C
		VarList[] out = new VarList[1];
		
		Attribute[] attr = new Attribute[0];
		String[] typeParams = new String[0];
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract,
				methodName);

		// we check the type via typeHandler
//		ResultTypes returnType = (ResultTypes) main.dispatch(node
//				.getDeclSpecifier());
		ResultTypes checkedType = main.cHandler.checkForPointer(main,
//                node.getDeclarators()[0].getPointerOperators(), returnType, false);
                cFuncDeclarator.getPointerOperators(), returnType, false);
        if (returnType.isVoid &&
                !(checkedType.cType instanceof CPointer)) {
			if (methodsCalledBeforeDeclared.contains(methodName)) {
				// this method was assumed to return int -> return int
				out[0] = new VarList(loc, new String[] { SFO.RES },
						new PrimitiveType(loc, /*new InferredType(Type.Integer),*/
								SFO.INT));
			} else {
				// void, so there are no out vars
				out = new VarList[0];
			}
		} else {
			// we found a type, so node is type ASTType
			ASTType type = main.typeHandler.ctype2asttype(loc, checkedType.cType);
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		}
		if (!modifiedGlobals.containsKey(methodName)) {
			modifiedGlobals.put(methodName, new LinkedHashSet<String>());
		}
		if (!callGraph.containsKey(methodName)) {
			callGraph.put(methodName, new LinkedHashSet<String>());
		}
		

		Procedure proc = procedures.get(methodName);
		if (proc != null) {
			//combine the specification from the definition with the one from the declaration
			List<Specification> specFromDef = Arrays.asList(proc.getSpecification());
			ArrayList<Specification> newSpecs = new ArrayList<Specification>(Arrays.asList(spec));
			newSpecs.addAll(specFromDef);
			spec = newSpecs.toArray(new Specification[0]);
			//TODO something else to take over for a declaration after the definition?
		}
		proc = new Procedure(loc, attr, methodName, typeParams, in,
				out, spec, null);
					
		procedures.put(methodName, proc);
		procedureToReturnCType.put(methodName, returnType.cType);
		
		// fill map of parameter types
		ArrayList<CType> paramTypes =
		        new ArrayList<CType>(proc.getInParams().length);
		
		// end scope for retranslation of ACSL specification
		main.cHandler.endScope();
		return new ResultSkip();
	}

	/**
	 * takes the contract (we got from CHandler) and translates it into an array of Boogie
	 * specifications
	 * (this needs to be called after the procedure parameters have been added to the symboltable)
	 * @param main
	 * @param contract
	 * @param methodName
	 * @return
	 */
	private Specification[] makeBoogieSpecFromACSLContract(Dispatcher main,
			List<ACSLNode> contract, String methodName) {
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
					LinkedHashSet<String> modifiedSet = new LinkedHashSet<String>();
					for (VariableLHS var : ms.getIdentifiers()) 
						modifiedSet.add(var.getIdentifier());
					modifiedGlobals.put(methodName, modifiedSet);
				}
			}

			main.cHandler.clearContract(); // take care for behavior and
												// completeness
		}
		return spec;
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
			IASTFunctionDefinition parent) {
	    VarList[] varListArray = currentProcedure.getInParams();
	    IASTParameterDeclaration[] paramDecs;
	    if (varListArray.length == 0) {
	        /*
	         * In C it is possible to write
	         *    func(void) {
	         *       ...
	         *    }
	         * This results in the empty name.
	         */
	        assert ((CASTFunctionDeclarator)parent.getDeclarator()).getParameters().length == 0 ||
	                (((CASTFunctionDeclarator)parent.getDeclarator()).getParameters().length == 1 &&
	                ((CASTFunctionDeclarator)parent.getDeclarator()).getParameters()[0].getDeclarator().getName().toString().equals(""));
	        paramDecs = new IASTParameterDeclaration[0];
	    }
	    else {
	        paramDecs = ((CASTFunctionDeclarator)parent.getDeclarator()).
	                getParameters();
	    }
	    assert varListArray.length == paramDecs.length;
		for (int i = 0; i < paramDecs.length; ++i) {
		    VarList varList  = varListArray[i];
		    IASTParameterDeclaration paramDec  = paramDecs[i];
			for (final String bId : varList.getIdentifiers()) {
				final String cId = main.cHandler.getSymbolTable()
						.getCID4BoogieID(bId, loc);
				final boolean isOnHeap = ((MainDispatcher) main).
				        getVariablesForHeap().contains(paramDec);
				// Copy of inparam that is writeable
				String auxInvar = main.nameHandler.getUniqueIdentifier(parent,
						cId, 0, isOnHeap);
				ASTType type = varList.getType();
				if (isOnHeap) {
				    type = MemoryHandler.POINTER_TYPE;
	                ((CHandler)main.cHandler).addBoogieIdsOfHeapVars(
	                        auxInvar);
				}
				VarList var = new VarList(loc, new String[] { auxInvar }, type);
				VariableDeclaration inVarDecl = new VariableDeclaration(loc,
						new Attribute[0], new VarList[] { var });
				
                CType cvar = main.cHandler.getSymbolTable().get(cId, loc)
                        .getCVariable();
                if (isOnHeap) {
                    cvar = new CPointer(cvar);
                }
                
				VariableLHS tempLHS = new VariableLHS(loc, auxInvar);
				IdentifierExpression rhsId = new IdentifierExpression(loc, bId);
				if (isOnHeap) {
				    LocalLValue llv = new LocalLValue(tempLHS, cvar);
				    // malloc
				    addMallocedAuxPointer(main, llv);
				    // dereference
                    HeapLValue hlv = new HeapLValue(llv.getValue(), cvar);
                    ArrayList<Declaration> decls = new ArrayList<Declaration>();
                    ResultExpression assign = ((CHandler) main.cHandler).
                        makeAssignment(main, loc, stmt, hlv,
                            new RValue(rhsId, ((CPointer)cvar).pointsToType),
                            decls,
                            new LinkedHashMap<VariableDeclaration, ILocation>(),
                            new ArrayList<Overapprox>());
                    stmt = assign.stmt;
                } else {
        			stmt.add(new AssignmentStatement(loc,
        					new LeftHandSide[] { tempLHS },
        					new Expression[] { rhsId }));
                }
				assert main.cHandler.getSymbolTable().containsCSymbol(cId);
				// Overwrite the information in the symbolTable for cId, s.t. it
				// points to the locally declared variable.
				main.cHandler.getSymbolTable().put(cId,
						new SymbolTableValue(auxInvar, inVarDecl, 
								new CDeclaration(cvar, cId), false, 
								StorageClass.UNSPECIFIED));
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
		LinkedHashSet<LinkedHashSet<String>> sccs = new TarjanSCC().getSCCs(callGraph);
		LinkedHashMap<String, LinkedHashSet<String>> mapping = new LinkedHashMap<String, LinkedHashSet<String>>();
		for (LinkedHashSet<String> scc : sccs) { // O(|proc|)
			for (String s : scc) {
				mapping.put(s, scc);
			}
		}
		LinkedHashMap<LinkedHashSet<String>, Integer> incomingEdges = new LinkedHashMap<LinkedHashSet<String>, Integer>();
		for (LinkedHashSet<String> scc : sccs) {
			incomingEdges.put(scc, 0);
		}
		// calculate the SCC update graph without loops and dead ends
		Queue<LinkedHashSet<String>> deadEnds = new LinkedList<LinkedHashSet<String>>();
		deadEnds.addAll(sccs);
		LinkedHashMap<LinkedHashSet<String>, LinkedHashSet<LinkedHashSet<String>>> updateGraph = new LinkedHashMap<LinkedHashSet<String>, LinkedHashSet<LinkedHashSet<String>>>();
		for (String p : callGraph.keySet()) { // O(|calls|)
			for (String s : callGraph.get(p)) { // foreach s : succ(p)
				// edge (p, s), means p calls s
				LinkedHashSet<String> sccP = mapping.get(p);
				LinkedHashSet<String> sccS = mapping.get(s);
				if (sccP == sccS)
					continue; // skip self loops
				if (updateGraph.containsKey(sccS)) {
					updateGraph.get(sccS).add(sccP);
				} else {
					LinkedHashSet<LinkedHashSet<String>> predSCCs = new LinkedHashSet<LinkedHashSet<String>>();
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
		LinkedHashMap<LinkedHashSet<String>, LinkedHashSet<String>> modGlobals = new LinkedHashMap<LinkedHashSet<String>, LinkedHashSet<String>>();
		while (!deadEnds.isEmpty()) {
			// O (|proc| + |edges in updateGraph|), where
			// |edges in updateGraph| <= |calls|
			LinkedHashSet<String> d = deadEnds.poll();
			for (String p : d) {
				if (!modGlobals.containsKey(d)) {
					LinkedHashSet<String> n = new LinkedHashSet<String>();
					n.addAll(modifiedGlobals.get(p));
					modGlobals.put(d, n);
				} else {
					modGlobals.get(d).addAll(modifiedGlobals.get(p));
				}
			}
			if (updateGraph.get(d) == null)
				continue;
			for (LinkedHashSet<String> next : updateGraph.get(d)) {
				if (!modGlobals.containsKey(next)) {
					LinkedHashSet<String> n = new LinkedHashSet<String>();
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
				LinkedHashSet<String> currModClause = modGlobals
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
	 * @param contract 
	 * @return the translation result.
	 */
	public Result handleFunctionDefinition(Dispatcher main, MemoryHandler memoryHandler,
			IASTFunctionDefinition node, ResultDeclaration funcDecl, List<ACSLNode> contract) {
		main.cHandler.beginScope();
		
		ILocation loc = new CACSLLocation(node);
		CDeclaration decl = funcDecl.getDeclarations().get(0);
        String methodName = decl.getName();
		// we check the type via typeHandler
		ResultTypes resType = (ResultTypes) main.dispatch(node
				.getDeclSpecifier());
		procedureToReturnCType.put(methodName, resType.cType);
		
		VarList[] in = processInParams(main, loc, decl, methodName);
        
		VarList[] out = new VarList[0]; // at most one out param in C
		
		ResultTypes checkedType = main.cHandler.checkForPointer(main, node//FIXME -- is this call still necessary??
				.getDeclarator().getPointerOperators(), resType, false);
		ASTType type = main.typeHandler.ctype2asttype(loc, checkedType.cType);
		if (!checkedType.isVoid) { // void, so there are no out vars
			out = new VarList[1];
			out[0] = new VarList(loc, new String[] { SFO.RES }, type);
		} else if (methodsCalledBeforeDeclared.contains(methodName)) {
			out = new VarList[1];
			out[0] = new VarList(loc, new String[] { SFO.RES },
					new PrimitiveType(loc, /*new InferredType(Type.Integer),*/
							SFO.INT));
		}
		
		Specification[] spec = makeBoogieSpecFromACSLContract(main, contract, methodName);
		
		Procedure proc = procedures.get(methodName);
		if (proc == null) {
			Attribute[] attr = new Attribute[0];
			String[] typeParams = new String[0];
			if (isInParamVoid(in)) {
				in = new VarList[0]; // in parameter is "void"
			}
			proc = new Procedure(loc, attr, methodName, typeParams, in, out,
					spec, null);
			if (procedures.containsKey(methodName)) {
				String msg = "Duplicated method identifier: " + methodName
						+ ". C does not support function overloading!";
				throw new IncorrectSyntaxException(loc, msg);
			}
			procedures.put(methodName, proc);
		} else { // check declaration against its implementation
			VarList[] declIn = proc.getInParams();
			boolean checkInParams = true;
			if (in.length != proc.getInParams().length
					|| out.length != proc.getOutParams().length
					|| isInParamVoid(proc.getInParams())) {
				if (proc.getInParams().length == 0) {
					// the implementation can have 0 to n in parameters!
					// do not check, but use the in params of the implementation
					// as we will take the ones of the implementation anyway
					checkInParams = false;
					declIn = in;
				} else if (isInParamVoid(proc.getInParams())
						&& (in.length == 0 || isInParamVoid(in))) {
					// decl(void) && [impl() || impl(void)]
					declIn = new VarList[0];
					in = new VarList[0];
					checkInParams = false;
				} else {
					String msg = "Implementation does not match declaration!";
					throw new IncorrectSyntaxException(loc, msg);
				}
			}
			if (checkInParams) {
				for (int i = 0; i < in.length; i++) {
					if (!(in[i].getType().toString()
							.equals(proc.getInParams()[i].getType().toString()))) {
						String msg = "Implementation does not match declaration!"
								+ "Type missmatch on in-parameters!";
						throw new IncorrectSyntaxException(loc,msg);
					}
				}
			}
			
			//combine the specification from the definition with the one from the declaration
			List<Specification> specFromDec = Arrays.asList(proc.getSpecification());
			ArrayList<Specification> newSpecs = new ArrayList<Specification>(Arrays.asList(spec));
			newSpecs.addAll(specFromDec);
			spec = newSpecs.toArray(new Specification[0]);
			
			proc = new Procedure(proc.getLocation(), proc.getAttributes(),
					proc.getIdentifier(), proc.getTypeParams(), declIn,
					proc.getOutParams(), spec, null);
			procedures.put(methodName, proc);
		}
		Procedure declWithCorrectlyNamedInParams = new Procedure(
				proc.getLocation(), proc.getAttributes(), proc.getIdentifier(),
				proc.getTypeParams(), in, proc.getOutParams(),
				proc.getSpecification(), null);
		currentProcedure = declWithCorrectlyNamedInParams;
		currentProcedureIsVoid = resType.isVoid;
		if (!modifiedGlobals.containsKey(currentProcedure.getIdentifier())) {
			modifiedGlobals.put(currentProcedure.getIdentifier(),
					new LinkedHashSet<String>());
		}
		if (!callGraph.containsKey(currentProcedure.getIdentifier())) {
			callGraph.put(currentProcedure.getIdentifier(),
					new LinkedHashSet<String>());
		}
		
		/*
		 * The structure is as follows:
		 * 1) Preprocessing of the method body:
		 *    - add new variables for parameters
		 *    - havoc them
		 *    - etc.
		 * 2) dispatch body
		 * 3) handle mallocs
         * 4) add statements and declarations to new body
		 */
		ArrayList<Statement> stmts = new ArrayList<Statement>();
		ArrayList<Declaration> decls = new ArrayList<Declaration>();
		// 1)
		handleFunctionsInParams(main, loc, decls, stmts, node);
		// 2)
		Body body = ((Body) main.dispatch(node.getBody()).node);
		// 3)
		stmts.addAll(insertMallocs(main, loc, memoryHandler,
		        new ArrayList<Statement>(Arrays.asList(body.getBlock()))));
		// 4)
		for (SymbolTableValue stv : main.cHandler.getSymbolTable().currentScopeValues())
			if (!stv.isGlobalVar() && stv.getBoogieDecl() != null) { //there may be a null declaration in case of foo(void)
				decls.add(stv.getBoogieDecl());
				
			}
        for (VariableDeclaration declaration : body.getLocalVars()) {
            decls.add(declaration);
        }
        
		body = new Body(loc, decls.toArray(new VariableDeclaration[0]),
		        stmts.toArray(new Statement[0]));
		
		proc = currentProcedure;
		// Implementation -> Specification always null!
		Procedure impl = new Procedure(loc, proc.getAttributes(), methodName,
				proc.getTypeParams(), in, proc.getOutParams(), null, body);
		currentProcedure = null;
		currentProcedureIsVoid = false;
		main.cHandler.endScope();
		return new Result(impl);
	}

	/**
	 * take the parameter information from the CDeclaration. Make a Varlist from it.
	 * Add the parameters to the symboltable. Also update procedureToParamCType member.
	 * @param main
	 * @param loc
	 * @param decl
	 * @param methodName
	 * @return
	 */
	private VarList[] processInParams(Dispatcher main, ILocation loc,
			CDeclaration decl, String methodName) {
		// fill map of parameter types
        ArrayList<CType> paramTypes = new ArrayList<CType>();
        CDeclaration[] paramDecs =
                ((CFunction) decl.getType()).getParameterTypes();
		VarList[] in  = new VarList[paramDecs.length];
        for (int i = 0; i < paramDecs.length; ++i) {
        	CDeclaration paramDec = paramDecs[i];
        	
        	ASTType type = ((TypeHandler) main.typeHandler).ctype2asttype(loc, paramDec.getType());
        	String paramId = main.nameHandler.getInParamIdentifier(paramDec.getName());
        	in[i] = new VarList(loc, new String[] { paramId}, type);
//            FIXME: boolean isOnHeap = ((MainDispatcher) main).getVariablesForHeap().
//                    contains(paramDec);
            paramTypes.add(i, paramDec.getType());
            main.cHandler.getSymbolTable().put(paramDec.getName(), 
            		new SymbolTableValue(paramId, null, paramDec, false, null));
        }
        procedureToParamCType.put(methodName, paramTypes);
		return in;
	}
	
	public ArrayList<Statement> insertMallocs(Dispatcher main, ILocation loc, MemoryHandler memoryHandler, ArrayList<Statement> block) {
		ArrayList<Statement> mallocs = new ArrayList<Statement>();
		for (LocalLValue llv : this.mallocedAuxPointers.currentScopeKeys()) 
			mallocs.addAll(memoryHandler.getMallocCall(main, this, memoryHandler.calculateSizeOf(llv.cType, loc), llv, loc).stmt);
		ArrayList<Statement> frees = new ArrayList<Statement>();
		for (LocalLValue llv : this.mallocedAuxPointers.currentScopeKeys())  //frees are inserted in handleReturnStm
			frees.addAll(memoryHandler.getFreeCall(main, this, llv.getValue(), loc).stmt);
		ArrayList<Statement> newBlockAL = new ArrayList<Statement>();
		newBlockAL.addAll(mallocs);
		newBlockAL.addAll(block);
		newBlockAL.addAll(frees);
		return newBlockAL;
	}

	void beginUltimateInit(Dispatcher main, ILocation loc, String startOrInit) {
		main.cHandler.beginScope();
		callGraph.put(startOrInit, new LinkedHashSet<String>());
		currentProcedure = new Procedure(loc, new Attribute[0], startOrInit, new String[0], new VarList[0], new VarList[0], new Specification[0], null);
		procedures.put(startOrInit, currentProcedure);
		modifiedGlobals.put(currentProcedure.getIdentifier(),
				new LinkedHashSet<String>());
	}
	
	void endUltimateInit(Dispatcher main, Procedure initDecl, String startOrInit) {
		procedures.put(startOrInit, initDecl);
		main.cHandler.endScope();
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
	    Check check = new Check(Check.Spec.PRE_CONDITION);
		CACSLLocation loc = new CACSLLocation(node, check);
		IASTExpression functionName = node.getFunctionNameExpression(); 
		if (!(functionName instanceof IASTIdExpression)) {
			String msg = "Function pointer or similar is not supported. "
					+ loc.toString();
			throw new IncorrectSyntaxException(loc, msg);
		}
		//don't use getRawSignature because it refers to the code before preprocessing 
		// f.i. we get a wrong methodname here in defineFunction.c, because of a #define in the original code
		String methodName = ((IASTIdExpression) functionName).getName().toString();
		
		if (methodName.equals("malloc")) {
			assert node.getArguments().length == 1;
			Result sizeRes = main.dispatch(node.getArguments()[0]);
			assert sizeRes instanceof ResultExpression;
			ResultExpression sizeRex = ((ResultExpression) sizeRes)
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			return memoryHandler.getMallocCall(main, this, sizeRex.lrVal.getValue(), loc);
		}
		if (methodName.equals("free")) {
			assert node.getArguments().length == 1;
			Result pRes = main.dispatch(node.getArguments()[0]);
			assert pRes instanceof ResultExpression;
			ResultExpression pRex = ((ResultExpression) pRes)
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			return memoryHandler.getFreeCall(main, this, pRex.lrVal.getValue(), loc);
		}

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new LinkedHashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
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
				throw new IncorrectSyntaxException(loc, msg);
			} // else: this means param of declaration is void and parameter
				// list of call is empty! --> OK
		}
		for (int i = 0; i < node.getArguments().length; i++) {
			IASTInitializerClause inParam = node.getArguments()[i];
			ResultExpression in = ((ResultExpression) main.dispatch(inParam))
					.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			if (in.lrVal.getValue() == null) {
				String msg = "Incorrect or invalid in-parameter! "
						+ loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			Expression arg = in.lrVal.getValue();
			
			if (in.lrVal.cType instanceof CPrimitive &&
			        ((CPrimitive)in.lrVal.cType).getType() == PRIMITIVE.INT) {
			    if (procedureToParamCType.containsKey(methodName) &&
			            (procedureToParamCType.get(methodName).get(i) instanceof
			            CPointer)) {
			        arg = MemoryHandler.constructPointerFromBaseAndOffset(
			                new IntegerLiteral(loc, "0"), arg, loc);
			    }
			} 
			args.add(arg);
			stmt.addAll(in.stmt);
			decl.addAll(in.decl);
			auxVars.putAll(in.auxVars);
			overappr.addAll(in.overappr);
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
				expr = new IdentifierExpression(loc, tmpId);
				VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpId, (PrimitiveType) type[0].getType(), loc); 
				auxVars.put(tmpVar, loc);
				decl.add(tmpVar);
				VariableLHS tmpLhs = new VariableLHS(loc, tmpId);
				call = new CallStatement(loc, false, new VariableLHS[] { tmpLhs },
						methodName, args.toArray(new Expression[0]));
			} else { // unsupported!
				String msg = "Cannot handle multiple out params! "
						+ loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
		} else {
			methodsCalledBeforeDeclared.add(methodName);
			String longDescription = "Return value of method '"
					+ methodName
					+ "' unknown! Methods should be declared, before they are used! Return value assumed to be int ...";
			Dispatcher.warn(loc, longDescription);
			String ident = main.nameHandler.getTempVarUID(SFO.AUXVAR.RETURNED);
			expr = new IdentifierExpression(loc,
					/*new InferredType(Type.Integer),*/ ident);
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
		return new ResultExpression(stmt, new RValue(expr, returnCType), decl,
		        auxVars, overappr);
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
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
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
					.getReturnValue())).switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			Expression rhs = (Expression) exprResult.lrVal.getValue();
			stmt.addAll(exprResult.stmt);
			decl.addAll(exprResult.decl);
			auxVars.putAll(exprResult.auxVars);
			if (outParams.length == 0) {
				// void method which is returning something! We remove the
				// return value!
				String msg = "This method is declared to be void, but returning a value!";
				Dispatcher.syntaxError(loc, msg);
			} else if (outParams.length != 1) {
				String msg = "We do not support several output parameters for functions";
				throw new UnsupportedSyntaxException(loc, msg);
			} else {
				String id = outParams[0].getIdentifiers()[0];
				VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(loc, id) };
				stmt.add(new AssignmentStatement(loc, lhs,
						new Expression[] { rhs }));
			}
		}
		stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
	
		// we need to insert a free for each malloc of an auxvar before each return
		for (Entry<LocalLValue, Integer> entry : this.mallocedAuxPointers.entrySet())  //frees are inserted in handleReturnStm
			if (entry.getValue() >= 1)
				stmt.addAll(memoryHandler.getFreeCall(main, this, entry.getKey().getValue(), loc).stmt);
		
		stmt.add(new ReturnStatement(loc));
		Map<VariableDeclaration, ILocation> emptyAuxVars =
		        new LinkedHashMap<VariableDeclaration, ILocation>(0);
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
		// convention (necessary probably only because of here):
		// typeHandler.ctype2boogietype yields "null" for CPrimitive(PRIMITIVE.VOID)
		return (in.length == 1 && in[0].getType() == null);
	}

	/**
	 * Getter for modified globals.
	 * 
	 * @return modified globals.
	 */
	public LinkedHashMap<String, LinkedHashSet<String>> getModifiedGlobals() {
		return this.modifiedGlobals;
	}

	/**
	 * Getter for procedures.
	 * 
	 * @return procedures.
	 */
	public LinkedHashMap<String, Procedure> getProcedures() {
		return this.procedures;
	}

	/**
	 * Returns the identifier of the current procedure.
	 * 
	 * @return the identifier of the current procedure.
	 */
	public String getCurrentProcedureID() {
		if (currentProcedure == null)
			return null;
		else
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
	public LinkedHashMap<String, LinkedHashSet<String>> getCallGraph() {
		return this.callGraph;
	}
	
	public void addMallocedAuxPointer(Dispatcher main, LocalLValue thisLVal) {
		if (!main.typeHandler.isStructDeclaration())
			this.mallocedAuxPointers.put(thisLVal, mallocedAuxPointers.getActiveScopeNum());
	}
	
	public LinkedScopedHashMap<LocalLValue, Integer> getMallocedAuxPointers() {
		return mallocedAuxPointers;
	}
}
