package local.stalin.boogie.cfg2smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.ListIterator;
import java.util.Stack;

import org.apache.log4j.Logger;


import local.stalin.boogie.type.ArrayType;
import local.stalin.boogie.type.BoogieType;
import local.stalin.boogie.type.ConstructedType;
import local.stalin.boogie.type.PlaceholderType;
import local.stalin.boogie.type.PrimitiveType;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITETerm;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.model.IType;
import local.stalin.model.boogie.ast.ArrayAccessExpression;
import local.stalin.model.boogie.ast.ArrayStoreExpression;
import local.stalin.model.boogie.ast.AssertStatement;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Attribute;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.BinaryExpression;
import local.stalin.model.boogie.ast.BitVectorAccessExpression;
import local.stalin.model.boogie.ast.BitvecLiteral;
import local.stalin.model.boogie.ast.BooleanLiteral;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.ConstDeclaration;
import local.stalin.model.boogie.ast.EnsuresSpecification;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.FunctionApplication;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.IdentifierExpression;
import local.stalin.model.boogie.ast.IfThenElseExpression;
import local.stalin.model.boogie.ast.IntegerLiteral;
import local.stalin.model.boogie.ast.LeftHandSide;
import local.stalin.model.boogie.ast.ModifiesSpecification;
import local.stalin.model.boogie.ast.NamedAttribute;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.QuantifierExpression;
import local.stalin.model.boogie.ast.RealLiteral;
import local.stalin.model.boogie.ast.RequiresSpecification;
import local.stalin.model.boogie.ast.Specification;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.StringLiteral;
import local.stalin.model.boogie.ast.Trigger;
import local.stalin.model.boogie.ast.TypeDeclaration;
import local.stalin.model.boogie.ast.UnaryExpression;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableDeclaration;
import local.stalin.model.boogie.ast.VariableLHS;


public class Boogie2SMT {
	private Theory theory;

	private ArrayList<FunctionSymbol> selectStores = new ArrayList<FunctionSymbol>();
	private Term ONE; 
	private Term ZERO;
	private Sort intSort, realSort;
	
	private Stack<TermVariable> typeStack = new Stack<TermVariable>();
	private Stack<HashMap<String,SMTLibBase>> identStack = new Stack<HashMap<String, SMTLibBase>>();
	private HashMap<String, FunctionSymbol> typeSymbols = new HashMap<String, FunctionSymbol>();
	private HashMap<String, FunctionSymbol> functions = new HashMap<String, FunctionSymbol>();
	private HashMap<String, SMTLibBase> globalConsts = new HashMap<String, SMTLibBase>();
	private HashMap<String, IType> globals = new HashMap<String, IType>();
	private HashMap<String, IType> locals = new HashMap<String, IType>();
	private HashMap<String, Procedure> procedureMap = new HashMap<String, Procedure>();
	private HashSet<String> itefunctions = new HashSet<String>();
	private PredicateSymbol partOrder, leqInt, ltInt, geqInt, gtInt;
	private PredicateSymbol leqReal, ltReal, geqReal, gtReal;
	
	private boolean isOldContext = false;
	private int generation = 0;
	
	private HashMap<String, TermVariable> oldGlobals = new HashMap<String, TermVariable>();
	private HashSet<TermVariable> allVars;
	private HashMap<String, TermVariable> outVars;
	private HashMap<String, TermVariable> inVars;
	
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private static final boolean debugMessages = false;

	public void incGeneration(){
		generation++;
	}
	
	public Boogie2SMT() {
		theory = new Theory();
		theory.setLogic("AUFLIRA");
		intSort = theory.getSort("Int");
		realSort = theory.getSort("Real");
		ONE = theory.numeral("1");
		ZERO = theory.numeral("0");
		partOrder = theory.createPredicate("po_", new Sort[] {intSort, intSort});
		leqInt = theory.getPredicate("<=", new Sort[] {intSort, intSort});
		ltInt = theory.getPredicate("<", new Sort[] {intSort, intSort});
		geqInt = theory.getPredicate(">=", new Sort[] {intSort, intSort});
		gtInt = theory.getPredicate(">", new Sort[] {intSort, intSort});

		leqReal = theory.getPredicate("<=", new Sort[] {realSort, realSort});
		ltReal = theory.getPredicate("<", new Sort[] {realSort, realSort});
		geqReal = theory.getPredicate(">=", new Sort[] {realSort, realSort});
		gtReal = theory.getPredicate(">", new Sort[] {realSort, realSort});

		theory.createFunction("mod", new Sort[] {intSort, intSort}, intSort);
		theory.createFunction("div", new Sort[] {intSort, intSort}, intSort);
		
		/* TODO: axioms for mod, div and mul ??? */
		
		identStack.add(globalConsts);
	}
	
	public Theory getTheory() {
		return theory;
	}

	private String quoteId(String id) {
		return SMTLibBase.quoteId(id);
	}
	
	private TermVariable createInVar(String id) {
		IType type = locals.containsKey(id) ? locals.get(id) : globals.get(id);
		Sort sort = convertSort(type);
		TermVariable tv =
			theory.createTermVariable("v_"+quoteId(id)+"_"+generation, sort);
		inVars.put(id, tv);
		allVars.add(tv);
		return tv;
	}
	
	private SMTLibBase getSmtIdentifier(String id) {
		if (locals.containsKey(id) || globals.containsKey(id)) {
			if (debugMessages) s_Logger.info(id + " is either local or global variable!");
			if (globals.containsKey(id) && isOldContext) {
				if (debugMessages) s_Logger.info(id + " is old global variable!");
				return theory.term(oldGlobals.get(id));
			}
			
			if (!inVars.containsKey(id)) {
				if (debugMessages) s_Logger.info(id + " is not in inVars!");
				TermVariable tv = createInVar(id); 
				if (!outVars.containsKey(id)) {
					if (debugMessages) s_Logger.info(id + " is not in outVars!");
					outVars.put(id, tv);
				}
			}
			if (debugMessages) s_Logger.info("Returning inVars entry of " + id + " as Term");
			return theory.term(inVars.get(id));
		}
		
		ListIterator<HashMap<String, SMTLibBase>> it = identStack.listIterator(identStack.size());
		while (it.hasPrevious()) {
			if (debugMessages) s_Logger.info("Has previous!!");
			HashMap<String,SMTLibBase> map = it.previous();
			if (map.containsKey(id)) {
				if (debugMessages) s_Logger.info("Returning map entry of " + id + "!");
				return map.get(id);
			}
		}
		throw new AssertionError("Identifier "+id+" was not declared.");
	}

	private Term wrapFormula(Formula formula) {
		return theory.ite(formula, ONE, ZERO);
	}
	
	private Sort convertSort(IType boogieType) {
		return boogieType.equals(PrimitiveType.realType) ? realSort : intSort;
	}

	@SuppressWarnings("unused")
	private Formula generateLabel(Statement stmt) {
		String label = "l_" + quoteId(stmt.getFilename()) + "_" + stmt.getLineNr();
		PredicateSymbol symb = theory.createPredicate(label, new Sort[0]);
		return theory.atom(symb);
	}

	public void declareType(TypeDeclaration typedecl) {
		if (typedecl.getSynonym() != null)
			return;
		String id = typedecl.getIdentifier();
		Sort[] argSorts = new Sort[typedecl.getTypeParams().length];
		for (int i = 0; i < argSorts.length; i++)
			argSorts[i] = intSort;
		FunctionSymbol func = theory.createFunction("t_"+quoteId(id), argSorts, intSort);
		typeSymbols.put(id, func);
	}

	public void declareFunction(FunctionDeclaration funcdecl) {
		for (Attribute attr : funcdecl.getAttributes()) {
			if (attr instanceof NamedAttribute) {
				NamedAttribute nattr = (NamedAttribute) attr;
				if (nattr.getName().equals("bvint")
					&& nattr.getValues().length == 1
					&& nattr.getValues()[0] instanceof StringLiteral
					&& ((StringLiteral)nattr.getValues()[0]).getValue().equals("ITE")) {
					/* TODO: make sanity check of parameter types ?? */
					itefunctions.add(funcdecl.getIdentifier());
					return;
				}
			}
		}
		String id = funcdecl.getIdentifier();
		String smtID = "f_"+quoteId(id);
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
			Sort sort = convertSort(vl.getType().getBoogieType()); 
			for (int i = 0; i < ids; i++) {
				paramSorts[paramNr++] = sort;
			}			
		}
		Sort resultSort = 
			convertSort(funcdecl.getOutParam().getType().getBoogieType());
		functions.put(id, theory.createFunction(smtID, paramSorts, resultSort));
	}

	public void declareConstants(ConstDeclaration constdecl) {
		VarList varlist = constdecl.getVarList();
		Sort[] paramTypes = new Sort[0];

		if (varlist.getType().equals(PrimitiveType.boolType)) {
			for (String id : varlist.getIdentifiers()) {
				PredicateSymbol sym = theory.createPredicate("c_"+quoteId(id), paramTypes);
				globalConsts.put(id, theory.atom(sym));
			}
		} else {
			Sort sort = convertSort(varlist.getType().getBoogieType());
			for (String id : varlist.getIdentifiers()) {
				FunctionSymbol sym = theory.createFunction("c_"+quoteId(id), paramTypes, sort);
				globalConsts.put(id, theory.term(sym));
			}
		}
	}	

	public void declareVariables(VariableDeclaration vardecl) {
		for (VarList vl : vardecl.getVariables()) {
			Sort sort = convertSort(vl.getType().getBoogieType());
			for (String id: vl.getIdentifiers()) {
				globals.put(id, vl.getType().getBoogieType());
				TermVariable sym = theory.createTermVariable("v_"+quoteId(id)+"_old", sort);
				oldGlobals.put(id, sym);
			}
		}
	}
	
	public void declareLocals(Procedure proc) {
		HashMap<String, SMTLibBase> inParams = new HashMap<String, SMTLibBase>(); 
		
		for (VarList vl : proc.getInParams()) {
			for (String id: vl.getIdentifiers()) {
				Sort sort = convertSort(vl.getType().getBoogieType());
				FunctionSymbol sym = theory.getFunction("in_"+quoteId(id), new Sort[0]);
				if (sym == null)
					sym = theory.createFunction("in_"+quoteId(id), new Sort[0], sort);
				inParams.put(id, theory.term(sym));
			}
		}
		for (VarList vl : proc.getOutParams()) {
			for (String id: vl.getIdentifiers()) {
				locals.put(id, vl.getType().getBoogieType());
			}
		}
		for (VariableDeclaration vdecl : proc.getBody().getLocalVars()) {
			for (VarList vl: vdecl.getVariables()) {
				for (String id: vl.getIdentifiers()) {
					locals.put(id, vl.getType().getBoogieType());
				}
			}
		}
		
		for (String id : proc.getTypeParams())
			typeStack.push(theory.createTermVariable(quoteId(id), intSort));
		identStack.push(inParams);
	}
	
	/**
	 * declareLocals for procedures with or without implementation. Opposed to
	 * declareLocals this method can also applied to procedures without an
	 * implementation. (This method adds also the inParameters to the local
	 * variables). This method is a hack and only used by Heizmann's 
	 * UnstructuredBoogie2RecursiveCFG. On the long run this method will be
	 * removed and UnstructuredBoogie2RecursiveCFG will get an own Boogie2SMT
	 * class.
	 */
	public void declareLocalsFPWOWI(Procedure proc) {
		HashMap<String, SMTLibBase> inParams = new HashMap<String, SMTLibBase>(); 
		
		for (VarList vl : proc.getInParams()) {
			for (String id: vl.getIdentifiers()) {
				Sort sort = convertSort(vl.getType().getBoogieType());
				FunctionSymbol sym = theory.getFunction("in_"+quoteId(id), new Sort[0]);
				if (sym == null)
					sym = theory.createFunction("in_"+quoteId(id), new Sort[0], sort);
				inParams.put(id, theory.term(sym));
				locals.put(id, vl.getType().getBoogieType());
			}
		}
		for (VarList vl : proc.getOutParams()) {
			for (String id: vl.getIdentifiers()) {
				locals.put(id, vl.getType().getBoogieType());
			}
		}
		if (proc.getBody() != null)
		for (VariableDeclaration vdecl : proc.getBody().getLocalVars()) {
			for (VarList vl: vdecl.getVariables()) {
				for (String id: vl.getIdentifiers()) {
					locals.put(id, vl.getType().getBoogieType());
				}
			}
		}
		
		for (String id : proc.getTypeParams())
			typeStack.push(theory.createTermVariable(quoteId(id), intSort));
		identStack.push(inParams);
	}
	
	
	
	
	
	
	public void declareAxiom(Axiom ax) {
		theory.createAxiom(translateFormula(ax.getFormula()));
	}
	
	public void declareProcedure(Procedure proc) {
		procedureMap.put(proc.getIdentifier(), proc);
	}
	
	public Specification[] getProcedureSpecs(Procedure procImpl) {
		if (debugMessages) 
			s_Logger.info("Starting to build specs for procedure " + procImpl.getIdentifier());
		
		Procedure procDecl = this.procedureMap.get(procImpl.getIdentifier());
		if (procDecl == procImpl)
			return procDecl.getSpecification();
		return new RenameProcedureSpec().renameSpecs(procDecl, procImpl);
	}
	
	public void removeLocals(Procedure proc) {
		identStack.pop();
		for (int i = 0; i < proc.getTypeParams().length; i++)
			typeStack.pop();
		locals.clear();
	}
	
	private void createArrayFunc(int numArgs) {
		Sort[] storeargs = new Sort[numArgs+2];
		for (int i = 0; i < numArgs+2; i++)
			storeargs[i] = intSort;
		Sort[] selargs = new Sort[numArgs+1];
		for (int i = 0; i < numArgs+1; i++)
			selargs[i] = intSort;
		FunctionSymbol store = theory.createFunction("sstore", storeargs, intSort);
		FunctionSymbol select = theory.createFunction("sselect", selargs, intSort);

		Term[] storevec = new Term[numArgs+2];
		Term[] selvec = new Term[numArgs+1];
		Term[] selstorevec = new Term[numArgs+1];
		Term[] selstore1vec = new Term[numArgs+1];
		TermVariable[] vars1 = new TermVariable[numArgs+2];
		TermVariable[] vars = new TermVariable[2*numArgs+2];
		Formula xyeq = Atom.TRUE;
		vars1[0] = vars[0] = theory.createTermVariable("a", intSort);
		vars1[numArgs+1] = vars[2*numArgs+1] = theory.createTermVariable("v", intSort);
		storevec[0] = selvec[0] = theory.term(vars[0]);
		storevec[numArgs+1] = theory.term(vars[2*numArgs+1]);
		for (int i = 0; i < numArgs; i++) {
			vars1[i+1] = vars[2*i+1] = theory.createTermVariable("x"+i, intSort);
			vars[2*i+2] = theory.createTermVariable("y"+i, intSort);
			selstore1vec[i+1] = storevec[i+1] = theory.term(vars[2*i+1]);
			selstorevec[i+1] = selvec[i+1] = theory.term(vars[2*i+2]);
		}
		selstore1vec[0] = selstorevec[0] = theory.term(store, storevec);
		for (int i = numArgs-1; i>= 0; i--)
			xyeq = theory.and(theory.equals(storevec[i+1], selvec[i+1]), xyeq);
		Term selstore1 = theory.term(select, selstore1vec);
		Term selstore = theory.term(select, selstorevec);
		Term sel      = theory.term(select, selvec);
		Formula f1 = theory.equals(selstore1, storevec[numArgs+1]);
		Formula qf1 = theory.forall(vars1, f1, new SMTLibBase[][] { {selstore1} });
		Formula f = theory.or(xyeq, theory.equals(selstore, sel));
		Formula qf = theory.forall(vars, f, new SMTLibBase[][] { {selstore} });
		theory.createAxiom(qf1);
		theory.createAxiom(qf);
		s_Logger.debug("Sel/store "+numArgs+" axiom: "+qf);
		selectStores.add(select);
		selectStores.add(store);
	}
	
	private FunctionSymbol getArrayFunc(int numArgs, boolean isStore) {
		while (2*numArgs > selectStores.size()) {
			createArrayFunc(selectStores.size() / 2 + 1);
		}
		return selectStores.get(2*(numArgs-1) + (isStore ? 1 : 0));
	}

	private Term translateType(BoogieType type) {
		if (type instanceof PlaceholderType) {
			int depth = ((PlaceholderType)type).getDepth();
			return theory.term(typeStack.get(typeStack.size() - depth - 1));
		} else if (type instanceof PrimitiveType) {
			String id = "pt"+((PrimitiveType)type).getTypeCode();
			FunctionSymbol func = theory.getFunction(id);
			if (func == null)
				func = theory.createFunction(id, new Sort[0], intSort);
			return theory.term(func);
		} else if (type instanceof ConstructedType) {
			ConstructedType ctype = (ConstructedType) type;
			Term[] args = new Term[ctype.getConstr().getParamCount()];
			for (int i = 0; i < args.length; i++)
				args[i] = translateType(ctype.getParameter(i));
			return theory.term(typeSymbols.get(ctype.getConstr().getName()), args);
		} else {
			ArrayType atype = (ArrayType) type;
			int numIndices = atype.getIndexCount();
			Sort[] argSort = new Sort[numIndices+1];
			for (int i = 0; i < argSort.length; i++)
				argSort[i] = intSort;
			FunctionSymbol afunc = theory.getFunction("ptarr", argSort);
			if (afunc == null)
				afunc = theory.createFunction("ptarr", argSort, intSort);
			Term[] indTypes = new Term[numIndices+1];
			for (int i = 0; i < numIndices; i++)
				indTypes[i] = translateType(atype.getIndexType(i));
			indTypes[numIndices] = translateType(atype.getValueType());
			return theory.term(afunc, indTypes);
		}
	}
	
	private Term createArrayTerm(Expression arr, Expression[] indices, Expression value) {
		BoogieType arrayType = (BoogieType) arr.getType();
		ArrayType arrType = (ArrayType) arrayType.getUnderlyingType();
		int placeholders = arrType.getNumPlaceholders();
		BoogieType[] subst = new BoogieType[arrType.getNumPlaceholders()];
		for (int i = 0; i < indices.length; i++) {
			arrType.getIndexType(i).unify((BoogieType) indices[i].getType(), subst);
		}

		int numArgs = placeholders + indices.length;
		int termArgs = numArgs + (value != null ? 2 : 1);
		Term[] result = new Term[termArgs];
		result[0] = translateTerm(arr);
		for (int i = 0; i < placeholders; i++)
			result[i+1] = translateType(subst[i]);
		for (int i = 0; i < indices.length; i++)
			result[placeholders+i+1] = translateTerm(indices[i]);
		if (value != null)
			result[numArgs+1] = translateTerm(value);
		FunctionSymbol selstore = getArrayFunc(numArgs, value != null);
		return theory.term(selstore, result);
	}

	private Term translateTerm(Expression exp) {
		if (exp instanceof ArrayAccessExpression) {			
			ArrayAccessExpression arrexp = (ArrayAccessExpression) exp;
			Expression[] indices = arrexp.getIndices();
			return createArrayTerm(arrexp.getArray(), indices, null);
		} else if (exp instanceof ArrayStoreExpression) {
			ArrayStoreExpression arrexp = (ArrayStoreExpression) exp;
			Expression[] indices = arrexp.getIndices();
			return createArrayTerm(arrexp.getArray(), indices, arrexp.getValue());
		} else if (exp instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) exp;
			BinaryExpression.Operator op = binexp.getOperator();
			Sort sort =	convertSort(binexp.getLeft().getType());
			
			if (op == BinaryExpression.Operator.COMPEQ  ||
					op == BinaryExpression.Operator.COMPGEQ || op == BinaryExpression.Operator.COMPGT ||
				    op == BinaryExpression.Operator.COMPLEQ || op == BinaryExpression.Operator.COMPLT ||
				    op == BinaryExpression.Operator.COMPNEQ || 
				    op == BinaryExpression.Operator.LOGICAND || 
				    op == BinaryExpression.Operator.LOGICOR ||
				    op == BinaryExpression.Operator.LOGICIMPLIES || 
				    op == BinaryExpression.Operator.LOGICIFF)
				return wrapFormula(translateFormula(exp));
			else if (op == BinaryExpression.Operator.ARITHDIV ) {
				FunctionSymbol fun_symb = theory.getFunction("div", sort, sort);
				return theory.term(fun_symb, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHMINUS ){
				FunctionSymbol fun_symb = theory.getFunction("-", sort, sort);
				return theory.term(fun_symb, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHMOD ){
				FunctionSymbol fun_symb = theory.getFunction("mod", sort, sort);
				return theory.term(fun_symb, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHMUL ){
				FunctionSymbol fun_symb = theory.getFunction("*", sort, sort);
				return theory.term(fun_symb, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHPLUS ){
				FunctionSymbol fun_symb = theory.getFunction("+", sort, sort);
				return theory.term(fun_symb, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.BITVECCONCAT ){
				/* TODO */
				throw new UnsupportedOperationException("BITVECCONCAT not implemented");
			} else {
				throw new AssertionError("Unsupported binary expression "+exp);
			}
		} else if (exp instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) exp;
			UnaryExpression.Operator op = unexp.getOperator();
			if (op == UnaryExpression.Operator.LOGICNEG) {
				return wrapFormula(translateFormula(exp));
			} else if (op == UnaryExpression.Operator.ARITHNEGATIVE) {
				FunctionSymbol fun_symb = theory.getFunction("-", intSort);
				return theory.term(fun_symb, translateTerm(unexp.getExpr()));
			} else if (op == UnaryExpression.Operator.OLD) {
				boolean oldOldContext = isOldContext;
				isOldContext = true;
				Term term = translateTerm(unexp.getExpr());
				isOldContext = oldOldContext;
				return term;
			} else
				throw new AssertionError("Unsupported unary expression "+exp);
		} else if (exp instanceof RealLiteral){
			return theory.rational(((RealLiteral)exp).getValue());
		} else if (exp instanceof BitvecLiteral){
			//TODO
			throw new UnsupportedOperationException("BitvecLiteral not implemented");
		} else if (exp instanceof BitVectorAccessExpression){
			//TODO
			throw new UnsupportedOperationException("BitVectorAccess not implemented");
		} else if (exp instanceof BooleanLiteral){
			return ((BooleanLiteral) exp).getValue() ? ONE : ZERO;
		} else if (exp instanceof FunctionApplication){
			FunctionApplication func = ((FunctionApplication)exp);
			if (itefunctions.contains(func.getIdentifier())) {
				Formula cond = translateFormula(func.getArguments()[0]);
				Term t = translateTerm(func.getArguments()[1]);
				Term e = translateTerm(func.getArguments()[2]);
				/* Special case: If-then-else */
				return theory.ite(cond, t, e);
			}
			Sort[] params = new Sort[func.getArguments().length];
			for (int i=0;i < func.getArguments().length;i++){
				params[i] = intSort;
			}
			FunctionSymbol funcSymb = functions.get(func.getIdentifier());
			Term[] parameters = new Term[func.getArguments().length];
			for (int i=0; i<func.getArguments().length;i++)
				parameters[i] = translateTerm(func.getArguments()[i]);
			return theory.term(funcSymb, parameters);
		} else if (exp instanceof IdentifierExpression){
			IdentifierExpression var = (IdentifierExpression)exp;
			SMTLibBase ident = getSmtIdentifier(var.getIdentifier());
			if (ident instanceof Term)
				return (Term) ident;
			else
				return wrapFormula((Formula) ident);
		} else if (exp instanceof IntegerLiteral){
			return theory.numeral(((IntegerLiteral)exp).getValue());
		} else if (exp instanceof IfThenElseExpression){
			IfThenElseExpression ite = (IfThenElseExpression) exp;
			Formula cond = translateFormula(ite.getCondition());
			Term thenPart = translateTerm(ite.getThenPart());
			Term elsePart = translateTerm(ite.getElsePart());
			return theory.ite(cond, thenPart, elsePart);
		} else if (exp instanceof QuantifierExpression){
			return wrapFormula(translateFormula(exp));
		} else {
			throw new AssertionError("Unsupported expression "+exp);
		}
	}
	
	private Formula translateFormula(Expression exp) {
		assert exp.getType().equals(PrimitiveType.boolType) : "Not a boolean expression: "+exp;

		if (exp instanceof BinaryExpression){
			BinaryExpression binexp = (BinaryExpression) exp;
			BinaryExpression.Operator op = binexp.getOperator();
			
			if (op == BinaryExpression.Operator.COMPEQ ){
				if (binexp.getLeft().getType().equals(PrimitiveType.boolType))
					return theory.iff(translateFormula(binexp.getLeft()), 
							translateFormula(binexp.getRight()));
				else
					return theory.equals(translateTerm(binexp.getLeft()), 
							translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPGEQ ){
				PredicateSymbol geq = 
					binexp.getLeft().getType().equals(PrimitiveType.intType)
					? geqInt : geqReal;
				return theory.atom(geq, translateTerm(binexp.getLeft()), 
						 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPGT ){
				PredicateSymbol gt = 
					binexp.getLeft().getType().equals(PrimitiveType.intType)
					? gtInt : gtReal;
				return theory.atom(gt, translateTerm(binexp.getLeft()), 
						 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPLEQ ){
				PredicateSymbol leq = 
					binexp.getLeft().getType().equals(PrimitiveType.intType)
					? leqInt : leqReal;
				return theory.atom(leq, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPLT ){
				PredicateSymbol lt = 
					binexp.getLeft().getType().equals(PrimitiveType.intType)
					? ltInt : ltReal;
				return theory.atom(lt, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPNEQ ){
				if (binexp.getLeft().getType().equals(PrimitiveType.boolType))
					return theory.xor(translateFormula(binexp.getLeft()), 
							translateFormula(binexp.getRight()));
				else
					return theory.not(theory.equals(translateTerm(binexp.getLeft()), 
							translateTerm(binexp.getRight())));
			} else if (op == BinaryExpression.Operator.COMPPO ){
				return theory.atom(partOrder, translateTerm(binexp.getLeft()), 
				 		   translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICAND) {
				return theory.and(translateFormula(binexp.getLeft()), 
						          translateFormula(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICOR) {
				return theory.or(translateFormula(binexp.getLeft()), 
						          translateFormula(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICIMPLIES) {
				return theory.implies(translateFormula(binexp.getLeft()), 
						          translateFormula(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICIFF) {
				return theory.iff(translateFormula(binexp.getLeft()), 
						          translateFormula(binexp.getRight()));
			} else {
				throw new AssertionError("Unsupported boolean binary operator "+binexp);
			}
		} else if (exp instanceof IdentifierExpression){
			IdentifierExpression var = (IdentifierExpression)exp;
			SMTLibBase ident = getSmtIdentifier(var.getIdentifier());
			if (ident instanceof Term)
				return theory.distinct((Term) ident, ZERO);
			else
				return (Formula) ident;
		} else if (exp instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) exp;
			UnaryExpression.Operator op = unexp.getOperator();
			if (op == UnaryExpression.Operator.LOGICNEG){
				return theory.not(translateFormula(unexp.getExpr()));
			} else if (op == UnaryExpression.Operator.OLD){
				boolean oldOldContext = isOldContext;
				isOldContext = true;
				Formula formula = translateFormula(unexp.getExpr());
				isOldContext = oldOldContext;
				return formula;
			} else {
				throw new AssertionError("Unsupported boolean unary operator "+unexp);
			}
		} else if (exp instanceof BooleanLiteral) {
			return ((BooleanLiteral)exp).getValue() ? Atom.TRUE : Atom.FALSE;
		} else if (exp instanceof FunctionApplication) {
			FunctionApplication func = (FunctionApplication) exp;
			if (itefunctions.contains(func.getIdentifier())) {
				Formula cond = translateFormula(func.getArguments()[0]);
				Formula t = translateFormula(func.getArguments()[1]);
				Formula e = translateFormula(func.getArguments()[2]);
				/* Special case: If-then-else */
				return theory.ifthenelse(cond, t, e);
			}
			return theory.distinct(translateTerm(exp), ZERO);
		} else if (exp instanceof ArrayAccessExpression
				|| exp instanceof ArrayStoreExpression) {
			return theory.distinct(translateTerm(exp), ZERO);
		} else if (exp instanceof IfThenElseExpression){
			IfThenElseExpression ite = (IfThenElseExpression) exp;
			Formula cond = translateFormula(ite.getCondition());
			Formula thenPart = translateFormula(ite.getThenPart());
			Formula elsePart = translateFormula(ite.getElsePart());
			return theory.ifthenelse(cond, thenPart, elsePart);
		} else if (exp instanceof QuantifierExpression){
			QuantifierExpression quant = (QuantifierExpression) exp;
			String[] typeParams = quant.getTypeParams();
			VarList[] variables = quant.getParameters();
			int numvars = typeParams.length;
			for (int i = 0; i < variables.length; i++)
				numvars += variables[i].getIdentifiers().length;
			TermVariable[] vars = new TermVariable[numvars]; 
			HashMap<String,SMTLibBase> newVars = new HashMap<String, SMTLibBase>();
			int offset = 0;
			for (int j = 0; j < typeParams.length; j++) {
				vars[offset] = theory.createTermVariable("q" + quoteId(typeParams[j]), intSort);
				typeStack.push(vars[offset]);
				offset++;
			}
			for (int i = 0; i < variables.length; i++) {
				for (int j = 0; j < variables[i].getIdentifiers().length; j++) {
					vars[offset] = theory.createTermVariable("q" + quoteId(variables[i].getIdentifiers()[j]), intSort);
					newVars.put(variables[i].getIdentifiers()[j], theory.term(vars[offset]));
					offset++;
				}
			}
			identStack.push(newVars);
			Formula form = translateFormula(quant.getSubformula());
			Attribute[] attrs = quant.getAttributes();
			int numTrigs = 0;
			for (Attribute a : attrs) {
				if (a instanceof Trigger)
					numTrigs++;
			}
			SMTLibBase[][] triggers = new SMTLibBase[numTrigs][];
			offset = 0;
			for (Attribute a : attrs) {
				if (a instanceof Trigger) {
					Expression[] trigs = ((Trigger) a).getTriggers();
					SMTLibBase[] smttrigs = new SMTLibBase[trigs.length];
					for (int i = 0; i < trigs.length; i++) {
						Term trig = translateTerm(trigs[i]);
						if (trig instanceof ITETerm
							&& ((ITETerm)trig).getTrueCase() == ONE
							&& ((ITETerm)trig).getFalseCase() == ZERO)
							smttrigs[i] = ((ITETerm) trig).getCondition();
						else
							smttrigs[i] = trig;
					}
					triggers[offset++] = smttrigs;
				}
			}
			identStack.pop();
			for (int j = 0; j < typeParams.length; j++) {
				typeStack.pop();
			}
			return quant.isUniversal() ? theory.forall(vars, form, triggers)
					: theory.exists(vars, form, triggers);
		} else {
			throw new AssertionError("Unsupported boolean Boogie expression "+exp);
		}
	}

	private Formula assumes;
	private Formula asserts;

	public void startBlock() {
		outVars = new HashMap<String, TermVariable>();
		inVars  = new HashMap<String, TermVariable>();
		allVars = new HashSet<TermVariable>();
		assumes = Atom.TRUE;
		asserts = Atom.TRUE;
	}
	
	public void addAssignment(AssignmentStatement assign) {
		LeftHandSide[] lhs = assign.getLhs();
		Expression[] rhs = assign.getRhs();
		for (int i=0; i < lhs.length; i++) {
			/* ArrayLHS are removed by preprocessor */
			VariableLHS vlhs = (VariableLHS) lhs[i];
			String name = vlhs.getIdentifier();
			if (!inVars.containsKey(name)) {
				if (!outVars.containsKey(name)) {
					TermVariable tv = createInVar(name);
					outVars.put(name, tv);
				}
			} 
			if (inVars.containsKey(name)) {
				TermVariable tv = inVars.get(name);
				inVars.remove(name);
				generation++;
				Term rhsTerm = translateTerm(rhs[i]); 
				Formula eq = theory.equals(theory.term(tv), rhsTerm);
				assumes = theory.and(eq, assumes);
				asserts = theory.implies(eq, asserts);
			}
		}
	}
	
	public void addHavoc(HavocStatement havoc) {
		//ArrayList<TermVariable> vars = new ArrayList<TermVariable>(); 
		for (String id : havoc.getIdentifiers()) {
			if (!inVars.containsKey(id)) {
				if (!outVars.containsKey(id)) {
					TermVariable tv = createInVar(id);
					outVars.put(id, tv);
				}
			}
			if (inVars.containsKey(id)) {
				//vars.add(inVars.get(id));
				inVars.remove(id);
			}
		}
		/*
		if (vars.size() > 0) {
			TermVariable[] tvs = vars.toArray(new TermVariable[vars.size()]);
			assumes = theory.exists(tvs, assumes);
			asserts = theory.forall(tvs, asserts);
		}
		*/
		generation++;
	}
	public void addAssume(AssumeStatement assume) {
		Formula f = translateFormula(assume.getFormula());
		assumes = theory.and(f, assumes);
		asserts = theory.implies(f, asserts);
	}
	public void addAssert(AssertStatement assertstmt) {
		Formula f = translateFormula(assertstmt.getFormula());
		//Formula label = generateLabel(assertstmt);
		assumes = theory.and(f, assumes);
		asserts = theory.and(f, asserts);
		//asserts = theory.and(theory.implies(label, f), asserts);
	}
	
	public void addProcedureCall(CallStatement call) {
		Procedure procedure = this.procedureMap.get(call.getMethodName());

		HashMap<String, SMTLibBase> substitution = new HashMap<String, SMTLibBase>();
		Expression[] arguments = call.getArguments();
		int offset;
		String[] lhs = call.getLhs();
		offset = 0;
		ArrayList<String> havocVars = new ArrayList<String>();
		for (VarList vl: procedure.getOutParams()) {
			for (String id : vl.getIdentifiers()) {
				substitution.put(id, getSmtIdentifier(lhs[offset]));
				havocVars.add(lhs[offset]);
				offset++;
			}
		}

		if (!havocVars.isEmpty()) {
			for (String id : havocVars) {
				inVars.remove(id);
			}
		}
		HashMap<String, TermVariable> newOldGlobals = new HashMap<String, TermVariable>();
		/* FIXME: shouldn't this be .putAll(globals)?
		 * The oldGlobals of the procedure call should be the current globals
		 * before the procedure call.  However these are not known until we
		 * iterate through the modifies spec below.
		 */
		newOldGlobals.putAll(oldGlobals);
		for (Specification spec: procedure.getSpecification()){
			if (spec instanceof ModifiesSpecification){
				for (String id: ((ModifiesSpecification) spec).getIdentifiers()) {
					substitution.put(id, getSmtIdentifier(id));
					havocVars.add(id);
					TermVariable tv =
						theory.createTermVariable("v_"+quoteId(id)+"_"+(generation+1), intSort);
					newOldGlobals.put(id, tv);
				}
			}
		}

		generation++;

		offset = 0;
		for (VarList vl : procedure.getInParams()) {
			for (String id : vl.getIdentifiers()) {
				substitution.put(id, translateTerm(arguments[offset++]));
			}
		}

		HashMap<String, TermVariable> oldOldGlobals = oldGlobals;
		HashMap<String, IType> oldLocals = locals;
		oldGlobals = newOldGlobals;
		locals = new HashMap<String, IType>();
		
		identStack.push(substitution);
		for (Specification spec: procedure.getSpecification()){
			if (spec instanceof EnsuresSpecification) {
				Expression post = ((EnsuresSpecification)spec).getFormula();
				Formula f = translateFormula(post);
				assumes = theory.and(f, assumes);
				asserts = theory.implies(f, asserts);
			}
		}

		if (!havocVars.isEmpty()) {
			for (String id : havocVars) {
				if (globals.containsKey(id)) {
					inVars.remove(id);
					inVars.put(id, oldGlobals.get(id));
					allVars.add(oldGlobals.get(id));
				}
			}
		}

		for (Specification spec: procedure.getSpecification()){
			if (spec instanceof RequiresSpecification && !spec.isFree()) {
				Expression pre = ((RequiresSpecification)spec).getFormula();
				Formula f = translateFormula(pre);
				assumes = theory.and(f, assumes);
				asserts = theory.and(f, asserts);
			}
		}
		identStack.pop();
		oldGlobals = oldOldGlobals;
		locals = oldLocals;
	}

	public HashMap<String, TermVariable> getInVars() {
		return inVars;
	}
	public HashMap<String, TermVariable> getOutVars() {
		return outVars;
	}
	public HashSet<TermVariable> getAllVars() {
		return allVars;
	}
	public HashMap<String, TermVariable> getOldVars() {
		return oldGlobals;
	}

	public Formula getAssumes() {
		return assumes;
	}
	public Formula getAsserts() {
		return asserts;
	}
	public void endBlock() {
		outVars = null;
		inVars = null;
	}
	
}
