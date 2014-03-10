package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.SmtIdentifierProvider;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

public class Boogie2SMT implements SmtIdentifierProvider {
	private Script m_Script;

	// private ArrayList<FunctionSymbol> selectStores = new
	// ArrayList<FunctionSymbol>();
	// private Sort intSort, realSort;
	
	
	private final VariableManager m_VariableManager;
	
	private enum InternalState {
		INIT,
		TYPES_DECLARED,
		CONSTS_DECLARED,
		FUNCTIONS_DECLARED,
		AXIOMS_DECLARED,
		GLOBALVARS_DECLARED,
		PROCEDURES_DECLARED
	}

//	private Stack<TermVariable> typeStack = new Stack<TermVariable>();
	private Stack<HashMap<String, Term>> identStack = new Stack<HashMap<String, Term>>();
	// private HashMap<String, FunctionSymbol> typeSymbols = new HashMap<String,
	// FunctionSymbol>();
	// private final Map<String, Sort> type2sort = new HashMap<String, Sort>();
	// private HashMap<String, FunctionSymbol> functions = new HashMap<String,
	// FunctionSymbol>();
//	private HashMap<String, Term> globalConsts = new HashMap<String, Term>();
//	private HashMap<String, BoogieVar> globals = new HashMap<String, BoogieVar>();
//	private HashMap<String, BoogieVar> m_CurrentLocals = new HashMap<String, BoogieVar>();
//	private HashMap<String, BoogieVar> oldGlobals = new HashMap<String, BoogieVar>();
//	private Map<String, Map<String, BoogieVar>> m_Proc2Locals = new HashMap<String, Map<String, BoogieVar>>();



	/**
	 * Maps procedure identifier to procedure specification
	 */
	private HashMap<String, Procedure> m_Id2Specification = new HashMap<String, Procedure>();
	// private HashSet<String> itefunctions = new HashSet<String>();
	// private FunctionSymbol partOrder, leqInt, ltInt, geqInt, gtInt;
	// private FunctionSymbol leqReal, ltReal, geqReal, gtReal;


	// private int generation = 0;
	private VariableSSAManager m_VariableSSAManager = null;

	private HashSet<TermVariable> allVars;
	private HashMap<BoogieVar, TermVariable> outVars;
	private HashMap<BoogieVar, TermVariable> inVars;

	/**
	 * Auxilliary variables. TermVariables that occur neither as inVar nor as
	 * outVar. If you use the assumes or asserts to encode a transition the
	 * auxilliary variables are existentially quantified.
	 */
	private HashSet<TermVariable> auxVars;

	// private HashMap<BoogieVar, TermVariable> oldVars = new HashMap<BoogieVar,
	// TermVariable>();

	private Map<BoogieVar, TermVariable> m_CalleesModifiedGlobalsIn;
	private Map<BoogieVar, TermVariable> m_CalleesModifiedGlobalsOut;

	// used in backtranslation
	// private Map<Sort,IType> m_SmtSort2BoogieType = new HashMap<Sort,IType>();
	// private Map<IType,Sort> m_BoogieType2SmtSort = new HashMap<IType,Sort>();

	private static Logger s_Logger = UltimateServices.getInstance().getLogger("Boogie2SMT");
	Smt2Boogie m_Smt2Boogie;

	/**
	 * if set to true array access returns arbitrary values array store returns
	 * arbitrary arrays
	 */
	private final boolean m_BlackHoleArrays;

	/**
	 * True if we are translation a requires clause of the specification. In
	 * this case, a global variable g refers to the instance of the variable
	 * before the procedure call (the same instance as old(g)).
	 */
	private boolean m_TranslatingRequires = false;
	
	private InternalState m_InternalState = InternalState.INIT;

	private final TypeSortTranslator m_TypeSortTranslator;
	private final Expression2Term m_Expression2Term;
	private final Boogie2SmtSymbolTable m_Boogie2SmtSymbolTable;

	private String m_CurrentProcedure;

	public void incGeneration() {
		VariableSSAManager.incAllIndices();
		// generation++;
	}

	public Boogie2SMT(Script script, boolean blackHoleArrays) {
		m_BlackHoleArrays = blackHoleArrays;
		this.m_Script = script;
		m_VariableManager = new VariableManager(m_Script);
		m_TypeSortTranslator = new TypeSortTranslator(m_Script, m_BlackHoleArrays);
		m_VariableSSAManager = new VariableSSAManager(m_Script);
		m_Boogie2SmtSymbolTable = new Boogie2SmtSymbolTable(m_Script, m_TypeSortTranslator);
		m_Expression2Term = new Expression2Term(m_Script, m_TypeSortTranslator, this);
		m_VariableSSAManager.reset();
		// intSort = script.sort("Int");
		// realSort = script.sort("Real");

		m_Smt2Boogie = new Smt2Boogie(m_Script, m_TypeSortTranslator, m_Boogie2SmtSymbolTable);
		//

		// ONE = script.numeral("1");
		// ZERO = script.numeral("0");
		// partOrder = script.createPredicate("po_", new Sort[] {intSort,
		// intSort});

		// leqInt = script.getTheory().getFunction("<=", new Sort[] {intSort,
		// intSort});
		// ltInt = script.getTheory().getFunction("<", new Sort[] {intSort,
		// intSort});
		// geqInt = script.getTheory().getFunction(">=", new Sort[] {intSort,
		// intSort});
		// gtInt = script.getTheory().getFunction(">", new Sort[] {intSort,
		// intSort});
		//
		// leqReal = script.getTheory().getFunction("<=", new Sort[] {realSort,
		// realSort});
		// ltReal = script.getTheory().getFunction("<", new Sort[] {realSort,
		// realSort});
		// geqReal = script.getTheory().getFunction(">=", new Sort[] {realSort,
		// realSort});
		// gtReal = script.getTheory().getFunction(">", new Sort[] {realSort,
		// realSort});
		//
		// script.createFunction("mod", new Sort[] {intSort, intSort}, intSort);
		// script.createFunction("div", new Sort[] {intSort, intSort}, intSort);

		/* TODO: axioms for mod, div and mul ??? */

	}
	
	public VariableManager getVariableManager() {
		return m_VariableManager;
	}

	public Script getScript() {
		return m_Script;
	}

	public Smt2Boogie getSmt2Boogie() {
		return m_Smt2Boogie;
	}
	
	static String quoteId(String id) {
		// return Term.quoteId(id);
		return id;
	}
	
	public Boogie2SmtSymbolTable getBoogie2SmtSymbolTable() {
		return m_Boogie2SmtSymbolTable;
	}
	
	
	
	public TypeSortTranslator getTypeSortTranslator() {
		return m_TypeSortTranslator;
	}

	public void declareTypes(Collection<TypeDeclaration> declarations) {
		assert m_InternalState == InternalState.INIT : "declared in wrong order";
		for (TypeDeclaration decl : declarations) {
			m_TypeSortTranslator.declareType(decl);
		}
		m_InternalState = InternalState.TYPES_DECLARED;
	}
	
	public void declareConstants(Collection<ConstDeclaration> declarations) {
		assert m_InternalState == InternalState.TYPES_DECLARED : "declared in wrong order";
		for (ConstDeclaration decl : declarations) {
			m_Boogie2SmtSymbolTable.declareConstants(decl);
		}
		m_InternalState = InternalState.CONSTS_DECLARED;
	}
	
	public void declareFunctions(Collection<FunctionDeclaration> declarations) {
		assert m_InternalState == InternalState.CONSTS_DECLARED : "declared in wrong order";
		for (FunctionDeclaration decl : declarations) {
			this.declareFunction(decl);
		}
		m_InternalState = InternalState.FUNCTIONS_DECLARED;
	}
	
	public void declareAxioms(Collection<Axiom> declarations) {
		assert m_InternalState == InternalState.FUNCTIONS_DECLARED : "declared in wrong order";
		for (Axiom decl : declarations) {
			this.declareAxiom(decl);
		}
		m_InternalState = InternalState.AXIOMS_DECLARED;
	}
	
	public void declareGlobalVariables(Collection<VariableDeclaration> declarations) {
		assert m_InternalState == InternalState.AXIOMS_DECLARED : "declared in wrong order";
		for (VariableDeclaration decl : declarations) {
			m_Boogie2SmtSymbolTable.declareGlobalVariables(decl);
		}
		m_InternalState = InternalState.GLOBALVARS_DECLARED;
	}
	
	public void declareProcedures(Map<String, Procedure> specs, Map<String, Procedure> impls) {
		assert m_InternalState == InternalState.GLOBALVARS_DECLARED : "declared in wrong order";
		m_Boogie2SmtSymbolTable.declareProcedures(specs, impls);
		m_InternalState = InternalState.PROCEDURES_DECLARED;
	}
	

	
	
	
	
	private Sort getSort(IType itype, BoogieASTNode astNode) {
		return m_TypeSortTranslator.getSort(itype, astNode);
	}
	
	
	


//	public BoogieVar getLocalBoogieVar(String procedure, String identifier) {
//		Map<String, BoogieVar> locals = m_Proc2Locals.get(procedure);
//		if (locals == null) {
//			return null;
//		} else {
//			return locals.get(identifier);
//		}
//	}

	/**
	 * Get SMT variable for boogieVar and add it to inVars.
	 */
	private TermVariable createInVar(BoogieVar boogieVar, BoogieASTNode BoogieASTNode) {
		TermVariable tv;
		Sort sort = getSort(boogieVar.getIType(), BoogieASTNode);
		if (boogieVar.isOldvar()) {
			tv = boogieVar.getTermVariable();
		} else {
			// String name =
			// "v_"+quoteId(boogieVar.getIdentifier())+"_"+generation;
			tv = VariableSSAManager.getFreshTermVariable(boogieVar, sort);
		}
		inVars.put(boogieVar, tv);
		allVars.add(tv);
		return tv;
	}

	/**
	 * construct SmtVariable for id. If inVars does not contain such a variable,
	 * construct it an add it to invars and outvars.
	 */
	public Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext, BoogieASTNode BoogieASTNode) {
		if (declInfo.getStorageClass() == StorageClass.GLOBAL) {
			BoogieConst boogieConst = m_Boogie2SmtSymbolTable.getBoogieConst(id);
			if (boogieConst != null) {
				return boogieConst.getSmtConstant();
			}
		}
		
		if (declInfo.getStorageClass() == StorageClass.PROCEDURE_INPARAM || declInfo.getStorageClass() == StorageClass.PROCEDURE_OUTPARAM) {
			if (!identStack.isEmpty()) {
				ListIterator<HashMap<String, Term>> it = identStack.listIterator(identStack.size());
				while (it.hasPrevious()) {
					s_Logger.debug("Has previous!!");
					HashMap<String, Term> map = it.previous();
					if (map.containsKey(id)) {
						s_Logger.debug("Returning map entry of " + id + "!");
						return map.get(id);
					}
				}
			}
		}

		if (m_Boogie2SmtSymbolTable.getGlobals().containsKey(id) && m_CalleesModifiedGlobalsIn != null) {
			// case where we process specification of a called procedure.
			// boogieVar represents the global var of the caller before the call
			// and the oldvar of the callee. If the boogieVar is in the set of
			// modified variables we want to use a TermVariable with a different
			// index
			// than for the non-old variable.
			BoogieVar boogieVar = m_Boogie2SmtSymbolTable.getGlobals().get(id);
			if (m_CalleesModifiedGlobalsIn.containsKey(boogieVar)) {
				if (isOldContext || m_TranslatingRequires) {
					return m_CalleesModifiedGlobalsIn.get(boogieVar);
				} else {
					return m_CalleesModifiedGlobalsOut.get(boogieVar);
				}
			} else {
				if (!inVars.containsKey(boogieVar)) {
					s_Logger.debug(id + " is not in inVars!");
					TermVariable tv = createInVar(boogieVar, BoogieASTNode);
					if (!outVars.containsKey(boogieVar)) {
						s_Logger.debug(id + " is not in outVars!");
						outVars.put(boogieVar, tv);
					}
				}
				return inVars.get(boogieVar);
			}
		}

		if ( declInfo.getProcedure() != null|| m_Boogie2SmtSymbolTable.getGlobals().containsKey(id)) {
			BoogieVar boogieVar;
			if (declInfo.getProcedure() != null) {
				boogieVar = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, isOldContext);
				assert boogieVar != null;
//				boogieVar = m_Proc2Locals.get(declInfo.getProcedure()).get(id); 
			} else {
				if (isOldContext) {
					boogieVar = m_Boogie2SmtSymbolTable.getOldGlobals().get(id);
				} else {
					boogieVar = m_Boogie2SmtSymbolTable.getGlobals().get(id);
				}
			}
			s_Logger.debug(id + " is either local or global variable!");

			if (!inVars.containsKey(boogieVar)) {
				s_Logger.debug(id + " is not in inVars!");
				TermVariable tv = createInVar(boogieVar, BoogieASTNode);
				if (!outVars.containsKey(boogieVar)) {
					s_Logger.debug(id + " is not in outVars!");
					outVars.put(boogieVar, tv);
				}
			}
			s_Logger.debug("Returning inVars entry of " + id + " as Term");
			return inVars.get(boogieVar);
		}


		throw new AssertionError(String.format("Identifier %s was not declared.", id));
	}

	// @SuppressWarnings("unused")
	// private Formula generateLabel(Statement stmt) {
	// String label = "l_" + quoteId(stmt.getFilename()) + "_" +
	// stmt.getLineNr();
	// PredicateSymbol symb = script.createPredicate(label, new Sort[0]);
	// return script.atom(symb);
	// }

	// public void declareType(TypeDeclaration typedecl) {
	// if (typedecl.getSynonym() != null)
	// return;
	// String id = typedecl.getIdentifier();
	// Sort[] argSorts = new Sort[typedecl.getTypeParams().length];
	// for (int i = 0; i < argSorts.length; i++)
	// argSorts[i] = intSort;
	// FunctionSymbol func = script.createFunction("t_"+quoteId(id), argSorts,
	// intSort);
	// typeSymbols.put(id, func);
	// }


	private void declareFunction(FunctionDeclaration funcdecl) {
		// for (Attribute attr : funcdecl.getAttributes()) {
		// if (attr instanceof NamedAttribute) {
		// NamedAttribute nattr = (NamedAttribute) attr;
		// if (nattr.getName().equals("bvint")
		// && nattr.getValues().length == 1
		// && nattr.getValues()[0] instanceof StringLiteral
		// && ((StringLiteral)nattr.getValues()[0]).getValue().equals("ITE")) {
		// /* TODO: make sanity check of parameter types ?? */
		// itefunctions.add(funcdecl.getIdentifier());
		// return;
		// }
		// }
		// }
		String id = funcdecl.getIdentifier();
		// String smtID = "f_"+quoteId(id);
		String smtID = quoteId(id);
		int numParams = 0;
		for (VarList vl : funcdecl.getInParams()) {
			int ids = vl.getIdentifiers().length;
			numParams += ids == 0 ? 1 : ids;
		}

		Sort[] paramSorts = new Sort[numParams];
		int paramNr = 0;
		for (VarList vl : funcdecl.getInParams()) {
			int ids = vl.getIdentifiers().length;
			if (ids == 0)
				ids = 1;
			Sort sort = getSort(vl.getType().getBoogieType(), funcdecl);
			for (int i = 0; i < ids; i++) {
				paramSorts[paramNr++] = sort;
			}
		}
		Sort resultSort = getSort(funcdecl.getOutParam().getType().getBoogieType(), funcdecl);
		m_Script.declareFun(smtID, paramSorts, resultSort);
		m_Smt2Boogie.m_BoogieFunction2SmtFunction.put(id, smtID);
		m_Smt2Boogie.m_SmtFunction2BoogieFunction.put(smtID, id);
	}

	// public void declareConstants(ConstDeclaration constdecl) {
	// VarList varlist = constdecl.getVarList();
	// Sort[] paramTypes = new Sort[0];
	//
	// if (varlist.getType().equals(PrimitiveType.boolType)) {
	// for (String id : varlist.getIdentifiers()) {
	// PredicateSymbol sym = script.createPredicate("c_"+quoteId(id),
	// paramTypes);
	// globalConsts.put(id, script.atom(sym));
	// }
	// } else {
	// Sort sort = m_Smt2Boogie.getSort(varlist.getType().getBoogieType());
	// for (String id : varlist.getIdentifiers()) {
	// FunctionSymbol sym = script.createFunction("c_"+quoteId(id), paramTypes,
	// sort);
	// globalConsts.put(id, script.term(sym));
	// }
	// }
	// }


	private void declareAxiom(Axiom ax) {
		m_Script.assertTerm(m_Expression2Term.translateTerm(ax.getFormula()));
	}

	public void declareProcedure(Procedure proc) {
		m_Id2Specification.put(proc.getIdentifier(), proc);
	}

//	public Specification[] getProcedureSpecs(Procedure procImpl) {
//		if (debugMessages)
//			s_Logger.info("Starting to build specs for procedure " + procImpl.getIdentifier());
//
//		Procedure procDecl = this.m_Id2Specification.get(procImpl.getIdentifier());
//		if (procDecl == procImpl)
//			return procDecl.getSpecification();
//		return new RenameProcedureSpec().renameSpecs(procDecl, procImpl);
//	}

//	public void removeLocals(Procedure proc) {
//		assert m_CurrentProcedure != null;
//		m_CurrentProcedure = null;
//		// identStack.pop();
////		for (int i = 0; i < proc.getTypeParams().length; i++)
////			typeStack.pop();
////		m_CurrentLocals.clear();
//	}

	// private void createArrayFunc(int numArgs) {
	// Sort[] storeargs = new Sort[numArgs+2];
	// for (int i = 0; i < numArgs+2; i++)
	// storeargs[i] = intSort;
	// Sort[] selargs = new Sort[numArgs+1];
	// for (int i = 0; i < numArgs+1; i++)
	// selargs[i] = intSort;
	// FunctionSymbol store = script.createFunction("sstore", storeargs,
	// intSort);
	// FunctionSymbol select = script.createFunction("sselect", selargs,
	// intSort);
	//
	// Term[] storevec = new Term[numArgs+2];
	// Term[] selvec = new Term[numArgs+1];
	// Term[] selstorevec = new Term[numArgs+1];
	// Term[] selstore1vec = new Term[numArgs+1];
	// TermVariable[] vars1 = new TermVariable[numArgs+2];
	// TermVariable[] vars = new TermVariable[2*numArgs+2];
	// Formula xyeq = Atom.TRUE;
	// vars1[0] = vars[0] = script.createTermVariable("a", intSort);
	// vars1[numArgs+1] = vars[2*numArgs+1] = script.createTermVariable("v",
	// intSort);
	// storevec[0] = selvec[0] = script.term(vars[0]);
	// storevec[numArgs+1] = script.term(vars[2*numArgs+1]);
	// for (int i = 0; i < numArgs; i++) {
	// vars1[i+1] = vars[2*i+1] = script.createTermVariable("x"+i, intSort);
	// vars[2*i+2] = script.createTermVariable("y"+i, intSort);
	// selstore1vec[i+1] = storevec[i+1] = script.term(vars[2*i+1]);
	// selstorevec[i+1] = selvec[i+1] = script.term(vars[2*i+2]);
	// }
	// selstore1vec[0] = selstorevec[0] = script.term(store, storevec);
	// for (int i = numArgs-1; i>= 0; i--)
	// xyeq = script.and(script.equals(storevec[i+1], selvec[i+1]), xyeq);
	// Term selstore1 = script.term(select, selstore1vec);
	// Term selstore = script.term(select, selstorevec);
	// Term sel = script.term(select, selvec);
	// Formula f1 = script.equals(selstore1, storevec[numArgs+1]);
	// Formula qf1 = script.forall(vars1, f1, new Term[][] { {selstore1} });
	// Formula f = script.or(xyeq, script.equals(selstore, sel));
	// Formula qf = script.forall(vars, f, new Term[][] { {selstore} });
	// script.createAxiom(qf1);
	// script.createAxiom(qf);
	// s_Logger.debug("Sel/store "+numArgs+" axiom: "+qf);
	// selectStores.add(select);
	// selectStores.add(store);
	// }
	//
	// private FunctionSymbol getArrayFunc(int numArgs, boolean isStore) {
	// while (2*numArgs > selectStores.size()) {
	// createArrayFunc(selectStores.size() / 2 + 1);
	// }
	// return selectStores.get(2*(numArgs-1) + (isStore ? 1 : 0));
	// }
	//
	// private Term translateType(BoogieType type) {
	// if (type instanceof PlaceholderType) {
	// int depth = ((PlaceholderType)type).getDepth();
	// return script.term(typeStack.get(typeStack.size() - depth - 1));
	// } else if (type instanceof PrimitiveType) {
	// String id = "pt"+((PrimitiveType)type).getTypeCode();
	// FunctionSymbol func = script.getFunction(id);
	// if (func == null)
	// func = script.createFunction(id, new Sort[0], intSort);
	// return script.term(func);
	// } else if (type instanceof ConstructedType) {
	// ConstructedType ctype = (ConstructedType) type;
	// Term[] args = new Term[ctype.getConstr().getParamCount()];
	// for (int i = 0; i < args.length; i++)
	// args[i] = translateType(ctype.getParameter(i));
	// return script.term(typeSymbols.get(ctype.getConstr().getName()), args);
	// } else {
	// ArrayType atype = (ArrayType) type;
	// int numIndices = atype.getIndexCount();
	// Sort[] argSort = new Sort[numIndices+1];
	// for (int i = 0; i < argSort.length; i++)
	// argSort[i] = intSort;
	// FunctionSymbol afunc = script.getFunction("ptarr", argSort);
	// if (afunc == null)
	// afunc = script.createFunction("ptarr", argSort, intSort);
	// Term[] indTypes = new Term[numIndices+1];
	// for (int i = 0; i < numIndices; i++)
	// indTypes[i] = translateType(atype.getIndexType(i));
	// indTypes[numIndices] = translateType(atype.getValueType());
	// return script.term(afunc, indTypes);
	// }
	// }
	//
	// private Term createArrayTerm(Expression arr, Expression[] indices,
	// Expression value) {
	// BoogieType arrayType = (BoogieType) arr.getType();
	// ArrayType arrType = (ArrayType) arrayType.getUnderlyingType();
	// int placeholders = arrType.getNumPlaceholders();
	// BoogieType[] subst = new BoogieType[arrType.getNumPlaceholders()];
	// for (int i = 0; i < indices.length; i++) {
	// arrType.getIndexType(i).unify((BoogieType) indices[i].getType(), subst);
	// }
	//
	// int numArgs = placeholders + indices.length;
	// int termArgs = numArgs + (value != null ? 2 : 1);
	// Term[] result = new Term[termArgs];
	// result[0] = translateTerm(arr);
	// for (int i = 0; i < placeholders; i++)
	// result[i+1] = translateType(subst[i]);
	// for (int i = 0; i < indices.length; i++)
	// result[placeholders+i+1] = translateTerm(indices[i]);
	// if (value != null)
	// result[numArgs+1] = translateTerm(value);
	// FunctionSymbol selstore = getArrayFunc(numArgs, value != null);
	// return script.term(selstore, result);
	// }



	// private Formula translateFormula(Expression exp) {
	// assert exp.getType().equals(PrimitiveType.boolType) :
	// "Not a boolean expression: "+exp;
	//
	//
	// } else if (exp instanceof IdentifierExpression){
	// IdentifierExpression var = (IdentifierExpression)exp;
	// Term ident = getSmtIdentifier(var.getIdentifier());
	// if (ident instanceof Term)
	// return script.distinct((Term) ident, ZERO);
	//
	//
	//
	// } else if (exp instanceof ArrayAccessExpression
	// || exp instanceof ArrayStoreExpression) {
	// return script.distinct(translateTerm(exp), ZERO);
	//
	//
	//
	// else {
	// throw new AssertionError("Unsupported boolean Boogie expression "+exp);
	// }
	// }

	private Term assumes;
	private Term asserts;

//	private int m_freshConstantCounter = 0;

	public void startBlock() {
		outVars = new HashMap<BoogieVar, TermVariable>();
		inVars = new HashMap<BoogieVar, TermVariable>();
		allVars = new HashSet<TermVariable>();
		auxVars = new HashSet<TermVariable>();
		assumes = m_Script.term("true");
		asserts = m_Script.term("true");
	}
	
	private BoogieVar getModifiableBoogieVar(String id, DeclarationInformation declInfo) {
		StorageClass storageClass = declInfo.getStorageClass();
//		assert (declInfo.getProcedure() == null || declInfo.getProcedure().equals(m_CurrentProcedure));
		BoogieVar result;
		switch (storageClass) {
		case GLOBAL:
			result = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
			break;
		case LOCAL:
			result = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
			break;
		case IMPLEMENTATION_OUTPARAM:
			result = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
			break;
		case IMPLEMENTATION_INPARAM:
		case PROCEDURE_INPARAM:
		case PROCEDURE_OUTPARAM:
			throw new AssertionError("not modifiable");
		case IMPLEMENTATION:
		case PROCEDURE:
		case QUANTIFIED:
		default:
			throw new AssertionError("no appropriate variable ");
		}
		return result;
	}

	/**
	 * Let assign be a statement of the form v_i:=expr_i Remove v_i from the
	 * inVars (if contained). If neccessary v_i is put to outVars (possibly by
	 * getSmtIdentifier).
	 */
	public void addAssignment(AssignmentStatement assign) {
		LeftHandSide[] lhs = assign.getLhs();
		Expression[] rhs = assign.getRhs();
		Map<TermVariable, Expression> addedEqualities = new HashMap<TermVariable, Expression>();
		for (int i = 0; i < lhs.length; i++) {
			/* ArrayLHS are removed by preprocessor */
			VariableLHS vlhs = (VariableLHS) lhs[i];
			assert vlhs.getDeclarationInformation() != null : " no declaration information";
			String name = vlhs.getIdentifier();
			DeclarationInformation declInfo = vlhs.getDeclarationInformation();
			BoogieVar boogieVar = getModifiableBoogieVar(name, declInfo);
			assert (boogieVar != null);
			if (!inVars.containsKey(boogieVar)) {
				if (!outVars.containsKey(boogieVar)) {
					TermVariable tv = createInVar(boogieVar, vlhs);
					outVars.put(boogieVar, tv);
				}
			}
			if (inVars.containsKey(boogieVar)) {
				TermVariable tv = inVars.get(boogieVar);
				addedEqualities.put(tv, rhs[i]);
				removeInVar(boogieVar);
			}
		}
		// generation++;
		for (TermVariable tv : addedEqualities.keySet()) {
			Term rhsTerm = m_Expression2Term.translateTerm(addedEqualities.get(tv));
			Term eq = m_Script.term("=", tv, rhsTerm);
//			if (m_addBoogieInformation) {
//				Annotation locationAnnotation = new Annotation(":location", assign.getPayload().getLocation());
//				Annotation statementAnnotation = new Annotation(":statement", assign);
//				eq = m_Script.annotate(eq, new Annotation[] { locationAnnotation, statementAnnotation });
//			}
			assumes = Util.and(m_Script, eq, assumes);
			asserts = Util.implies(m_Script, eq, asserts);
			assert (assumes.toString() instanceof Object);
		}
	}

	public void addHavoc(HavocStatement havoc) {
		// ArrayList<TermVariable> vars = new ArrayList<TermVariable>();
		for (VariableLHS lhs : havoc.getIdentifiers()) {
			assert lhs.getDeclarationInformation() != null : " no declaration information";
			String name = lhs.getIdentifier();
			DeclarationInformation declInfo = lhs.getDeclarationInformation();
			BoogieVar boogieVar = getModifiableBoogieVar(name, declInfo);
			assert (boogieVar != null);
			if (!inVars.containsKey(boogieVar)) {
				if (!outVars.containsKey(boogieVar)) {
					TermVariable tv = createInVar(boogieVar, havoc);
					outVars.put(boogieVar, tv);
				}
			}
			if (inVars.containsKey(boogieVar)) {
				// vars.add(inVars.get(id));
				removeInVar(boogieVar);
			}
		}
		/*
		 * if (vars.size() > 0) { TermVariable[] tvs = vars.toArray(new
		 * TermVariable[vars.size()]); assumes = script.exists(tvs, assumes);
		 * asserts = script.forall(tvs, asserts); }
		 */
		// generation++;
		assert (assumes.toString() instanceof Object);
	}

	public void addAssume(AssumeStatement assume) {
		Term f = m_Expression2Term.translateTerm(assume.getFormula());
//		if (m_addBoogieInformation) {
//			Annotation locationAnnotation = new Annotation(":location", assume.getPayload().getLocation());
//			Annotation statementAnnotation = new Annotation(":statement", assume);
//			f = m_Script.annotate(f, new Annotation[] { locationAnnotation, statementAnnotation });
//		}
		assumes = Util.and(m_Script, f, assumes);
		asserts = Util.implies(m_Script, f, asserts);
		assert (assumes.toString() instanceof Object);
	}

	public void addAssert(AssertStatement assertstmt) {
		Term f = m_Expression2Term.translateTerm(assertstmt.getFormula());
//		if (m_addBoogieInformation) {
//			Annotation locationAnnotation = new Annotation(":location", assertstmt.getPayload().getLocation());
//			Annotation statementAnnotation = new Annotation(":statement", assertstmt);
//			f = m_Script.annotate(f, new Annotation[] { locationAnnotation, statementAnnotation });
//		}
		// Formula label = generateLabel(assertstmt);
		assumes = Util.and(m_Script, f, assumes);
		asserts = Util.and(m_Script, f, asserts);
		// asserts = script.and(script.implies(label, f), asserts);
		assert (assumes.toString() instanceof Object);
	}

	public void addProcedureCall(CallStatement call) {
		assert (assumes.toString() instanceof Object);
		Procedure procedure = this.m_Id2Specification.get(call.getMethodName());

		HashMap<String, Term> substitution = new HashMap<String, Term>();
		Expression[] arguments = call.getArguments();
		int offset;
		VariableLHS[] lhs = call.getLhs();
		offset = 0;
		ArrayList<BoogieVar> havocVars = new ArrayList<BoogieVar>();
		for (VarList vl : procedure.getOutParams()) {
			for (String id : vl.getIdentifiers()) {
				// BoogieVar outParam = locals.get(id);
				// assert (outParam != null);
				String name = lhs[offset].getIdentifier();
				DeclarationInformation declInfo = lhs[offset].getDeclarationInformation();
				BoogieVar boogieVar = getModifiableBoogieVar(name, declInfo);
				assert (boogieVar != null);

				substitution.put(id, getSmtIdentifier(name, lhs[offset].getDeclarationInformation(), false, vl));
				havocVars.add(boogieVar);
				offset++;
			}
		}

		for (BoogieVar boogieVar : havocVars) {
			removeInVar(boogieVar);
		}

		m_CalleesModifiedGlobalsIn = new HashMap<BoogieVar, TermVariable>();
		m_CalleesModifiedGlobalsOut = new HashMap<BoogieVar, TermVariable>();

		for (Specification spec : procedure.getSpecification()) {
			if (spec instanceof ModifiesSpecification) {
				for (VariableLHS var : ((ModifiesSpecification) spec).getIdentifiers()) {
					String id = var.getIdentifier();
					BoogieVar boogieVar = m_Boogie2SmtSymbolTable.getBoogieVar(id, var.getDeclarationInformation(), false);
					assert boogieVar != null;
					Sort sort = getSort(boogieVar.getIType(), spec);
					// String inName =
					// "v_"+quoteId(boogieVar.getIdentifier())+"_"+
					// VariableSSAManager.getNextVariableIndex(boogieVar);
					if (inVars.containsKey(boogieVar)) {
						m_CalleesModifiedGlobalsOut.put(boogieVar, inVars.get(boogieVar));
					} else {
						// Sort sort =
						// m_Smt2Boogie.getSort(boogieVar.getIType());
						// String outName =
						// "v_"+quoteId(boogieVar.getIdentifier())+"_"+
						// VariableSSAManager.getFreshTermVariable(boogieVar);
						// String name =
						// "v_"+quoteId(boogieVar.getIdentifier())+"_"+generation;
						TermVariable tv = VariableSSAManager.getFreshTermVariable(boogieVar, sort);
						m_CalleesModifiedGlobalsOut.put(boogieVar, tv);
						outVars.put(boogieVar, tv);
					}
					// Sort sort = m_Smt2Boogie.getSort(boogieVar.getIType());
					// String name =
					// "v_"+quoteId(boogieVar.getIdentifier())+"_"+(generation+1);
					TermVariable tv = VariableSSAManager.getFutureTermVariable(boogieVar, sort);
					inVars.put(boogieVar, tv);
					m_CalleesModifiedGlobalsIn.put(boogieVar, tv);
				}
			}
		}

		// generation++;

		offset = 0;
		for (VarList vl : procedure.getInParams()) {
			for (String id : vl.getIdentifiers()) {
				substitution.put(id, m_Expression2Term.translateTerm(arguments[offset++]));
			}
		}

		// HashMap<BoogieVar, TermVariable> callerOldGlobals = inVarsOldGlobals;
//		HashMap<String, BoogieVar> oldLocals = m_CurrentLocals;
//		m_CurrentLocals = new HashMap<String, BoogieVar>();

		identStack.push(substitution);
		for (Specification spec : procedure.getSpecification()) {
			if (spec instanceof EnsuresSpecification) {
				Expression post = ((EnsuresSpecification) spec).getFormula();
				Term f = m_Expression2Term.translateTerm(post);
				assumes = Util.and(m_Script, f, assumes);
				if (spec.isFree()) {
					asserts = Util.implies(m_Script, f, asserts);
				} else {
					asserts = Util.and(m_Script, f, asserts);
				}
			}
		}

		m_TranslatingRequires = true;
		for (Specification spec : procedure.getSpecification()) {
			if (spec instanceof RequiresSpecification) {
				Expression pre = ((RequiresSpecification) spec).getFormula();
				Term f = m_Expression2Term.translateTerm(pre);
				assumes = Util.and(m_Script, f, assumes);
				if (spec.isFree()) {
					asserts = Util.implies(m_Script, f, asserts);
				} else {
					asserts = Util.and(m_Script, f, asserts);
				}
			}
		}
		m_TranslatingRequires = false;

		m_CalleesModifiedGlobalsIn = null;
		m_CalleesModifiedGlobalsOut = null;
		identStack.pop();
		// inVarsOldGlobals = callerOldGlobals;
//		m_CurrentLocals = oldLocals;
		assert (assumes.toString() instanceof Object);
	}

	/**
	 * Remove boogieVars from inVars mapping, if the inVar is not an outVar, add
	 * it to he auxilliary variables auxVar.
	 */
	private void removeInVar(BoogieVar boogieVar) {
		TermVariable tv = inVars.remove(boogieVar);
		if (outVars.get(boogieVar) != tv) {
			auxVars.add(tv);
		}
	}

	public HashMap<BoogieVar, TermVariable> getInVars() {
		return inVars;
	}

	public HashMap<BoogieVar, TermVariable> getOutVars() {
		return outVars;
	}

	public HashSet<TermVariable> getAllVars() {
		return allVars;
	}

	public Set<TermVariable> getAuxVars() {
		return auxVars;
	}

	public Term getAssumes() {
		assert (assumes.toString() instanceof Object);
		return assumes;
	}

	public Term getAsserts() {
		return asserts;
	}

	public void endBlock() {
		outVars = null;
		inVars = null;
		auxVars = null;
		allVars = null;
	}

	// public Map<Sort, IType> getSmtSort2BoogieType() {
	// return m_SmtSort2BoogieType;
	// }
	//
	// public Map<IType, Sort> getBoogieType2SmtSort() {
	// return m_BoogieType2SmtSort;
	// }

	/**
	 * Translate an array of expressions. Variables occurring in expressions
	 * will be added to inVars. May not be called while a block is translated.
	 */
	public Term[] expressions2terms(Expression[] exps, Map<BoogieVar, TermVariable> inVars, Set<TermVariable> allVars) {
		if (this.outVars != null || this.inVars != null) {
			throw new AssertionError("unable to translate single expression" + " while translating block");
		}
		startBlock();
		Term[] terms = new Term[exps.length];
		for (int i = 0; i < exps.length; i++) {
			terms[i] = m_Expression2Term.translateTerm(exps[i]);
		}
		inVars.putAll(this.inVars);
		allVars.addAll(this.allVars);
		endBlock();
		return terms;
	}

//	public Term getFreshConstant(TermVariable tv) {
//		String name = "c_" + tv.getName() + "_" + m_freshConstantCounter++;
//		Sort sort = tv.getSort();
//		m_Script.declareFun(name, new Sort[0], sort);
//		return m_Script.term(name);
//	}
	
	public static void reportUnsupportedSyntax(BoogieASTNode BoogieASTNode, String longDescription) {
		UnsupportedSyntaxResult<BoogieASTNode> result = new UnsupportedSyntaxResult<BoogieASTNode>(BoogieASTNode,
				Activator.s_PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),longDescription);
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_NAME, result);
		UltimateServices.getInstance().cancelToolchain();
	}

	public BoogieVar constructBoogieVar(String name, Object object,
			PrimitiveType type, boolean b, Object object2) {
		// TODO Auto-generated method stub
		return null;
	}
	
	
	/**
	 * Use with caution! Construct auxiliary variables only if you need then in
	 * the whole verification process.
	 * Construct auxiliary variables only if the assertion stack of the script
	 * is at the lowest level.
	 * Auxiliary variables are not supported in any backtranslation.
	 */
	public BoogieVar constructAuxiliaryBoogieVar(String identifier, 
			String procedure, StorageClass storageClass, IType iType, 
			boolean isOldvar, BoogieASTNode BoogieASTNode) {
		return m_Boogie2SmtSymbolTable.constructBoogieVar(identifier, procedure, 
				storageClass, iType, isOldvar, BoogieASTNode);
	}

}